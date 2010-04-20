{-# LANGUAGE ForeignFunctionInterface, ScopedTypeVariables,
  RecursiveDo #-}
module Logfile(Logfile, LogfilePtr(..), openLogfile, nextRecord,
               LogRecord(..),LogRecordBody(..)) where

import System.Posix.IO
import System.Posix.Types
import System.IO
import System.IO.Unsafe
import Foreign.Marshal.Alloc
import Foreign.Storable
import Foreign.Ptr
import Foreign.C.Types
import Data.Word
import Numeric
import Control.Monad
import Data.IORef

import Types
import Config

data ByteFile = ByteFile { bf_fd :: Fd,
                           bf_window :: Ptr Word8,
                           bf_window_size :: IORef Int,
                           bf_window_offset :: IORef FileOffset }

{- Read this much from the log file at a time. -}
windowSize :: ByteCount
windowSize = 65536

openByteFile :: FilePath -> IO ByteFile
openByteFile path =
    do h <- openFd path ReadOnly Nothing defaultFileFlags
       window <- mallocBytes (fromIntegral windowSize)
       sz <- newIORef 0
       ofs <- newIORef 0
       return $ ByteFile { bf_fd = h,
                           bf_window = window,
                           bf_window_size = sz,
                           bf_window_offset = ofs }

byteFile :: Int -> (Ptr Word8 -> Int -> IO a) -> ByteFile -> FileOffset -> IO (Maybe a)
byteFile sz peeker bf ofs =
    do winsize <- readIORef $ bf_window_size bf
       winofs <- readIORef $ bf_window_offset bf
       when (ofs < winofs || ofs + fromIntegral sz >= winofs + fromIntegral winsize) $
            do fdSeek (bf_fd bf) AbsoluteSeek ofs
               newWinSize <- fdReadBuf (bf_fd bf) (bf_window bf) windowSize
               writeIORef (bf_window_offset bf) ofs
               writeIORef (bf_window_size bf) $ fromIntegral newWinSize
       winsize' <- readIORef $ bf_window_size bf
       winofs' <- readIORef $ bf_window_offset bf       
       if ofs < winofs' || ofs + fromIntegral sz >= winofs' + fromIntegral winsize'
        then return Nothing
        else liftM Just $ peeker (bf_window bf) (fromIntegral $ ofs - winofs')

error' :: String -> a -> a
error' msg = error msg

byteFileStorable :: Storable a => ByteFile -> FileOffset -> IO (Maybe a)
byteFileStorable bf ofs =
    mdo res <- byteFile (sizeOf $ error' "sizeOf forced argument?" $ maybe undefined id res) peekByteOff bf ofs
        return res

bufferToList' :: Storable a => [a] -> Ptr a -> Int -> Int -> IO [a]
bufferToList' acc _ _  0 = return $ reverse acc
bufferToList' acc ptr offset cntr =
    do item <- peekByteOff ptr offset
       bufferToList' (item:acc) ptr (offset + 1) (cntr - 1)

bufferToList :: Storable a => Ptr a -> Int -> Int -> IO [a]
bufferToList = bufferToList' []

byteFileByteList :: ByteFile -> FileOffset -> Int -> IO (Maybe [Word8])
byteFileByteList bf ofs sz =
    do winsize <- readIORef $ bf_window_size bf
       winofs <- readIORef $ bf_window_offset bf
       when (ofs < winofs || ofs + fromIntegral sz >= winofs + fromIntegral winsize) $
            do fdSeek (bf_fd bf) AbsoluteSeek ofs
               newWinSize <- fdReadBuf (bf_fd bf) (bf_window bf) windowSize
               writeIORef (bf_window_offset bf) ofs
               writeIORef (bf_window_size bf) $ fromIntegral newWinSize
       winsize' <- readIORef $ bf_window_size bf
       winofs' <- readIORef $ bf_window_offset bf       
       if ofs < winofs' || ofs + fromIntegral sz >= winofs' + fromIntegral winsize'
        then return Nothing
        else liftM Just $ bufferToList (bf_window bf) (fromIntegral $ ofs - winofs') sz
    
newtype Logfile = Logfile ByteFile
data LogfilePtr = LogfilePtr FileOffset Integer deriving (Show, Read, Eq)

data LogRecordBody = LogSyscall { ls_nr :: Word32,
                                  ls_res :: Word64,
                                  ls_arg1 :: Word64,
                                  ls_arg2 :: Word64,
                                  ls_arg3 :: Word64 }
                   | LogMemory { lm_ptr :: Word64,
                                 lm_contents :: [Word8] }
                   | LogRdtsc { lr_tsc :: Word64 }
                   | LogClientCall
                   | LogClientReturn
                   | LogSignal { ls_rip :: Word64,
                                 ls_signo :: Word32,
                                 ls_err :: Word64,
                                 ls_va :: Word64 }
                   | LogAccess { ls_read :: Bool,
                                 ls_val :: Word64,
                                 ls_size :: Int,
                                 ls_ptr :: Word64 }
                     deriving Show

data LogRecord = LogRecord {lr_tid :: ThreadId,
                            lr_body :: LogRecordBody} deriving Show

openLogfile :: FilePath -> IO (Logfile, LogfilePtr)
openLogfile path =
    do h <- openByteFile path
       return (Logfile h, LogfilePtr 0 0)

data ByteParser a = ByteParser { run_byte_parser :: ByteFile -> FileOffset -> IO (Either String (a, FileOffset)) }

instance Monad ByteParser where
    return x = ByteParser $ \_ contents -> return $ Right (x, contents)
    (ByteParser a) >>= b =
        ByteParser $ \file contents ->
            do ls <- a file contents
               case ls of
                 Left x -> return $ Left x
                 Right (ares, atrail) ->
                     run_byte_parser (b ares) file atrail

instance Functor ByteParser where
    fmap = liftM

parseByteFile :: ByteFile -> FileOffset -> ByteParser a -> IO (Maybe (a, FileOffset))
parseByteFile bf startOffset bp =
    do res <- run_byte_parser bp bf startOffset
       return $ case res of
                  Left _ -> Nothing
                  Right x -> Just x

byteParseSkipBytes :: Word32 -> ByteParser ()
byteParseSkipBytes cntr =
    ByteParser $ \_ o -> return $ Right ((), o + fromIntegral cntr)

byteParseStorable :: Storable a => ByteParser a
byteParseStorable = ByteParser $ \file offset ->
                                    do v <- byteFileStorable file offset
                                       return $ case v of
                                                  Nothing -> Left "cannot parse storable"
                                                  Just v' -> Right (v', offset + (fromIntegral $ sizeOf v'))

byteParseByteList :: Int -> ByteParser [Word8]
byteParseByteList nrBytes =
    ByteParser $ \file offset ->
        do res <- byteFileByteList file offset nrBytes
           return $ case res of
                      Nothing -> Left "cannot parse byte list: end of file"
                      Just v -> Right (v, offset + fromIntegral nrBytes)

getByte :: ByteParser Word8
getByte =
    ByteParser $ \file offset ->
        do res <- byteFileStorable file offset
           return $ case res of
                      Nothing -> Left "getByte at EOF"
                      Just b -> Right (b, offset + 1)

byteListToInteger :: [Word8] -> Integer
byteListToInteger = foldr (\a b -> b * 256 + a) 0 . (map toInteger)

byteParseUnsigned :: ByteParser Word32
byteParseUnsigned = byteParseStorable

byteParseULong :: ByteParser Word64
byteParseULong = byteParseStorable

byteParseSyscallRecord :: ByteParser LogRecordBody
byteParseSyscallRecord = do nr <- byteParseUnsigned
                            byteParseUnsigned {- pad -}
                            res <- byteParseSysres
                            arg1 <- byteParseULong
                            arg2 <- byteParseULong
                            arg3 <- byteParseULong
                            return $ LogSyscall { ls_nr = nr,
                                                  ls_res = res,
                                                  ls_arg1 = arg1,
                                                  ls_arg2 = arg2,
                                                  ls_arg3 = arg3 }

byteParseMemoryRecord :: Int -> ByteParser LogRecordBody
byteParseMemoryRecord nrBytes = do ptr <- byteParseULong
                                   body <- byteParseByteList $ nrBytes - 8
                                   return $ LogMemory { lm_ptr = ptr, lm_contents = body }

byteParseRdtscRecord :: ByteParser LogRecordBody
byteParseRdtscRecord = fmap LogRdtsc byteParseULong

byteParseClientRecord :: ByteParser LogRecordBody
byteParseClientRecord = do cls <- byteParseULong
                           return $ case cls of
                                      0x50500000 -> LogClientCall
                                      0x50500001 -> LogClientReturn
                                      _ -> error $ "bad client request class " ++ (showHex cls "")

byteParseSignalRecord :: ByteParser LogRecordBody
byteParseSignalRecord = do rip <- byteParseULong
                           signo <- byteParseUnsigned
                           byteParseUnsigned {- pad -}
                           err <- byteParseULong
                           va <- byteParseULong
                           return $ LogSignal { ls_rip = rip,
                                                ls_signo = signo,
                                                ls_err = err,
                                                ls_va = va }

byteParseBool :: ByteParser Bool
byteParseBool = fmap ((/=) 0) getByte

{- Shamelessly ripped from
   http://hackage.haskell.org/trac/ghc/attachment/ticket/3218/fdReadBuf.patch,
   since this version of ghc doesn't seem to have it. -}
fdReadBuf :: Fd
          -> Ptr Word8 -- ^ Memory in which to put the data
          -> ByteCount -- ^ Maximum number of bytes to read
          -> IO ByteCount -- ^ Number of bytes read (zero for EOF)
fdReadBuf _fd _buf 0 = return 0
fdReadBuf fd buf nbytes =
    fmap fromIntegral $
         c_safe_read (fromIntegral fd) (castPtr buf) (fromIntegral nbytes)
foreign import ccall safe "read"
  c_safe_read :: CInt -> Ptr CChar -> CSize -> IO CSsize

byteParseSysres :: ByteParser Word64
byteParseSysres = do code <- byteParseULong
                     iserr <- byteParseBool
                     byteParseByteList 7 {- padding -}
                     return $ if iserr
                              then 0 - code
                              else code
                         
byteParseAccessRecord :: Int -> Bool -> ByteParser (Maybe LogRecordBody)
byteParseAccessRecord nrBytes is_read =
    if not useMemoryRecords
    then return Nothing
    else do ptr <- byteParseULong
            body <- byteParseByteList $ nrBytes - 8
            return $ Just $ LogAccess { ls_read = is_read,
                                        ls_ptr = ptr,
                                        ls_size = length body,
                                        ls_val = fromInteger $ byteListToInteger body }

byteParseTaggedUnion :: (Eq a, Show a) => a -> [(a, ByteParser b)] -> ByteParser b
byteParseTaggedUnion key lkup =
    case lookup key lkup of
      Nothing -> error $ "invalid tagged union key " ++ (show key)
      Just worker -> worker

byteParseRecord :: Integer -> ByteParser (LogRecord, Integer)
byteParseRecord cntr =
    do 
       cls <- byteParseUnsigned
       sz <- byteParseUnsigned
       tid <- byteParseUnsigned
       body <- byteParseTaggedUnion cls [(1, return Nothing),
                                         (2, fmap Just $ byteParseSyscallRecord),
                                         (3, fmap Just $ byteParseMemoryRecord $ fromIntegral $ sz - 12),
                                         (4, fmap Just $ byteParseRdtscRecord),
                                         (5, byteParseAccessRecord (fromIntegral $ sz - 12) True),
                                         (6, byteParseAccessRecord (fromIntegral $ sz - 12) False),
                                         (7, return Nothing),
                                         (8, return Nothing),
                                         (9, return Nothing),
                                         (10, fmap Just $ byteParseClientRecord),
                                         (11, fmap Just $ byteParseSignalRecord)]
       case body of
         Nothing -> byteParseSkipBytes (sz - 12) >> byteParseRecord (cntr + 1)
         Just b -> return (LogRecord { lr_tid = ThreadId $ toInteger tid,
                                       lr_body = b },
                           cntr)

nextRecord' :: Logfile -> LogfilePtr -> IO (Maybe (LogRecord, LogfilePtr))
nextRecord' (Logfile lf) (LogfilePtr offset record_nr) =
    do res <- parseByteFile lf offset (byteParseRecord record_nr)
       case res of
         Nothing -> return Nothing
         Just ((lr, newRecordNr), newOffset) ->
             return $ Just (lr, LogfilePtr newOffset newRecordNr)

nextRecord :: Logfile -> LogfilePtr -> Maybe (LogRecord, LogfilePtr)
nextRecord lf lp =
    unsafePerformIO $ nextRecord' lf lp
