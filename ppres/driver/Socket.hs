{-# LANGUAGE ForeignFunctionInterface #-}
module Socket(sendSocketCommand, recvSocket, fdToSocket, recvStringBytes,
              ControlPacket(..))
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

sendSocketCommand :: Socket -> ControlPacket -> IO Int32
sendSocketCommand handle cp =
    let get_response :: (Ptr Int32) -> IO Int32
        get_response ptr =
            do (r, _) <- recvBufFrom handle ptr 4
               peek ptr
    in do sendPacket handle cp
          allocaBytes 4 get_response

recvSocket :: Socket -> IO Socket
recvSocket parent =
    liftIO $ do newFd <- recvFd parent
                mkSocket newFd AF_UNIX Stream 0 Connected


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
