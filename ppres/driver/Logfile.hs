{-# LANGUAGE ForeignFunctionInterface, ScopedTypeVariables #-}
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

import Types
import Util

newtype Logfile = Logfile Fd
data LogfilePtr = LogfilePtr FileOffset Integer deriving (Show, Read, Eq)

instance Forcable COff where
    force = seq

instance Forcable LogfilePtr where
    force (LogfilePtr x y) = force x . force y

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
                                 ls_va :: Word64 } deriving Show

data LogRecord = LogRecord {lr_tid :: ThreadId,
                            lr_body :: LogRecordBody} deriving Show

openLogfile :: FilePath -> IO (Logfile, LogfilePtr)
openLogfile path =
    do h <- openFd path ReadOnly Nothing defaultFileFlags
       return (Logfile h, LogfilePtr 0 0)

bufferToList :: Storable a => Ptr a -> Int -> IO [a]
bufferToList _ 0 = return []
bufferToList ptr cntr =
    do item <- peek ptr
       rest <- bufferToList (plusPtr ptr $ sizeOf item) (cntr - 1)
       return $ item:rest

fdPReadBytes :: Fd -> FileOffset -> ByteCount -> IO (Maybe [Word8])
fdPReadBytes fd offset size =
    let size' = fromIntegral size in
    do offset' <- fdSeek fd AbsoluteSeek offset
       if offset' /= offset
          then return Nothing
          else allocaBytes size' $ \buf -> do bc <- fdReadBuf fd buf size
                                              if bc == size
                                                 then liftM Just $ bufferToList buf $ fromIntegral bc
                                                 else return Nothing

data ByteParser a = ByteParser { run_byte_parser :: [Word8] -> [(a, [Word8])] }

instance Monad ByteParser where
    return x = ByteParser $ \contents -> [(x, contents)]
    (ByteParser a) >>= b =
        ByteParser $ \contents ->
            do (ares, atrail) <- a contents
               run_byte_parser (b ares) atrail

instance Functor ByteParser where
    fmap = liftM

parseBytes :: String -> ByteParser a -> [Word8] -> a
parseBytes n p c =
    case run_byte_parser p c of
      [] -> error $ "no parse for " ++ n
      ((x,_):_) -> x

byteParseByteList :: Int -> ByteParser [Word8]
byteParseByteList nrBytes = ByteParser $ \contents -> let (result,rest) = splitAt nrBytes contents
                                                      in if length result == nrBytes
                                                         then [(result, rest)]
                                                         else []
getByte :: ByteParser Word8
getByte = ByteParser $ \contents -> case contents of
                                      [] -> []
                                      (x:xs) -> [(x, xs)]

byteParseInteger :: Int -> ByteParser Integer
byteParseInteger nrBytes = do bytes <- byteParseByteList nrBytes
                              return $ foldr (\a b -> b * 256 + a) 0 $ map toInteger bytes

byteParseUnsigned :: ByteParser Word32
byteParseUnsigned = fmap fromInteger $ byteParseInteger 4

byteParseULong :: ByteParser Word64
byteParseULong = fmap fromInteger $ byteParseInteger 8

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
                         
byteParseTaggedUnion :: (Eq a, Show a) => a -> [(a, ByteParser b)] -> ByteParser b
byteParseTaggedUnion key lkup =
    case lookup key lkup of
      Nothing -> error "invalid tagged union"
      Just worker -> worker

nextRecord' :: Logfile -> LogfilePtr -> IO (Maybe (LogRecord, LogfilePtr))
nextRecord' lf@(Logfile fd) (LogfilePtr offset record_nr) =
    do hdr' <- fdPReadBytes fd offset 12
       case hdr' of
         Nothing -> return Nothing
         Just hdr ->
             let ((cls::Word32, size), tid) = parseBytes "hdr" (pairM (pairM byteParseUnsigned byteParseUnsigned) byteParseUnsigned) hdr
             in do bodyBytes' <- fdPReadBytes fd (offset + 12) (fromIntegral $ size - 12)
                   case bodyBytes' of
                     Nothing -> error "truncated logfile"
                     Just bodyBytes ->
                         let body :: Maybe LogRecordBody
                             body = parseBytes "body "(byteParseTaggedUnion cls [(1, return Nothing),
                                                                                 (2, fmap Just $ byteParseSyscallRecord),
                                                                                 (3, fmap Just $ byteParseMemoryRecord $ fromIntegral $ size - 12),
                                                                                 (4, fmap Just $ byteParseRdtscRecord),
                                                                                 (5, return Nothing),
                                                                                 (6, return Nothing),
                                                                                 (7, return Nothing),
                                                                                 (8, return Nothing),
                                                                                 (9, return Nothing),
                                                                                 (10, fmap Just $ byteParseClientRecord),
                                                                                 (11, fmap Just $ byteParseSignalRecord)]) bodyBytes
                             nextPtr = LogfilePtr (offset + fromIntegral size) (record_nr + 1)
                         in case body of
                              Nothing -> nextRecord' lf nextPtr
                              Just b -> return $ Just (LogRecord { lr_tid = ThreadId $ toInteger tid,
                                                                   lr_body = b },
                                                       nextPtr)

nextRecord :: Logfile -> LogfilePtr -> Maybe (LogRecord, LogfilePtr)
nextRecord lf lp =
    unsafePerformIO $ nextRecord' lf lp
