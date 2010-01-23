{-# LANGUAGE ForeignFunctionInterface #-}
module Socket(sendSocketCommand, recvSocket, fdToSocket) where

import Data.Word
import Data.Int
import Foreign.Storable
import Foreign.Ptr
import Foreign.Marshal.Alloc
import Network.Socket
import Foreign.C.Types

foreign import ccall unsafe "send"
  c_send :: CInt -> Ptr a -> CSize -> CInt -> IO CInt


socketToFd :: Socket -> CInt
socketToFd (MkSocket x _ _ _ _) = x

fdToSocket :: CInt -> IO Socket
fdToSocket fd = mkSocket fd AF_UNIX Stream 0 Connected

sendSocketCommand :: Socket -> Word32 -> [Word64] -> IO Int32
sendSocketCommand handle command args =
    let nr_args :: Word32
        nr_args = fromInteger $ toInteger $ length args
        packet_size = 8 * (nr_args + 1)
        build_packet packet_ptr =
            let flatten_list _ [] = return ()
                flatten_list ptr (x:xs) =
                    do poke ptr x
                       flatten_list (plusPtr ptr (sizeOf x)) xs
            in
            do pokeByteOff packet_ptr 0 command
               pokeByteOff packet_ptr 4 nr_args
               flatten_list (plusPtr packet_ptr 8) args
        send_packet ptr =
            do build_packet ptr
               c_send (socketToFd handle) ptr (fromInteger $ toInteger packet_size) 0
        get_response :: (Ptr Int32) -> IO Int32
        get_response ptr =
            do (r, _) <- recvBufFrom handle ptr 4
               peek ptr
    in do allocaBytes (8 * (length args + 1)) send_packet
          allocaBytes 4 get_response


recvSocket :: Socket -> IO Socket
recvSocket parent =
    do newFd <- recvFd parent
       mkSocket newFd AF_UNIX Stream 0 Connected

