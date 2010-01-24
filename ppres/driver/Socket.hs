{-# LANGUAGE ForeignFunctionInterface #-}
module Socket(sendSocketCommand, recvSocket, fdToSocket, recvStringBytes,
              ControlPacket(..), ResponsePacket(..), ResponseData(..))
    where

import Data.Word
import Data.Int
import Foreign.Storable
import Foreign.Ptr
import Foreign.Marshal.Alloc
import Network.Socket
import Foreign.C.Types
import Control.Monad.State
import Char

foreign import ccall unsafe "send"
  c_send :: CInt -> Ptr a -> CSize -> CInt -> IO CInt

data ControlPacket = ControlPacket Word32 [Word64]
data ResponseData = ResponseDataString String
                  | ResponseDataAncillary Word32 [Word64]
data ResponsePacket = ResponsePacket Bool [ResponseData]

socketToFd :: Socket -> CInt
socketToFd (MkSocket x _ _ _ _) = x

fdToSocket :: CInt -> IO Socket
fdToSocket fd = mkSocket fd AF_UNIX Stream 0 Connected

sendPacket :: Socket -> ControlPacket -> IO ()
sendPacket handle (ControlPacket command args) =
    let nr_args :: Word32
        nr_args = fromIntegral $ length args
        packet_size = 8 * (nr_args + 1)
        build_packet packet_ptr =
            let flatten_list _ [] = return ()
                flatten_list ptr (x:xs) =
                    do poke ptr x
                       flatten_list (plusPtr ptr (sizeOf x)) xs
            in do pokeByteOff packet_ptr 0 command
                  pokeByteOff packet_ptr 4 nr_args
                  flatten_list (plusPtr packet_ptr 8) args
        send_packet ptr =
            do build_packet ptr
               c_send (socketToFd handle) ptr (fromInteger $ toInteger packet_size) 0
    in allocaBytes (8 * (length args + 1)) send_packet >> return ()

recvStringBytes :: Socket -> Int32 -> IO String
recvStringBytes sock len =
    let peekArray :: Storable a => Ptr a -> Int -> IO [a]
        peekArray _ 0 = return []
        peekArray ptr count =
            do i <- peek ptr
               let s = sizeOf i
               if count < s
                then error "weird: peeking array but size of array not multiple of size of element"
                else do rest <- peekArray (ptr `plusPtr` s) (count - s)
                        return $ i:rest
                       
        bufferToString :: Ptr Word8 -> Int -> IO String
        bufferToString ptr l =
            do bytes <- peekArray ptr l
               return $ map (chr.fromIntegral) bytes
    in
      allocaBytes (fromIntegral len) $ \buffer ->
        do (r, _) <- recvBufFrom sock buffer (fromIntegral len)
           bufferToString buffer r

getResponse :: Socket -> IO ResponsePacket
getResponse handle =
    let getInt32 :: IO Int32
        getInt32 = allocaBytes 4 $ \ptr -> do recvBufFrom handle ptr 4
                                              peek ptr
        getAncillary :: IO ResponseData
        getAncillary = error "Write me"
        getString :: IO ResponseData
        getString = do bytes <- getInt32
                       s <- recvStringBytes handle bytes
                       return $ ResponseDataString s
        worker :: [ResponseData] -> IO ResponsePacket
        worker acc_data =
            do rm <- getInt32
               case rm of
                 0 -> return $ ResponsePacket True (reverse acc_data)
                 1 -> return $ ResponsePacket False (reverse acc_data)
                 2 -> do anc <- getAncillary
                         worker $ anc:acc_data
                 3 -> do s <- getString
                         worker $ s:acc_data
                 _ -> error $ "strange response type " ++ (show rm)
    in worker []

sendSocketCommand :: Socket -> ControlPacket -> IO ResponsePacket
sendSocketCommand handle cp =
    sendPacket handle cp >> getResponse handle

recvSocket :: Socket -> IO Socket
recvSocket parent =
    liftIO $ do newFd <- recvFd parent
                mkSocket newFd AF_UNIX Stream 0 Connected

