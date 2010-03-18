{-# LANGUAGE ForeignFunctionInterface, ScopedTypeVariables #-}
module Socket(sendSocketCommand, sendSocketCommandTrailer, recvSocket, fdToSocket, recvStringBytes,
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

import Types

foreign import ccall unsafe "send"
  c_send :: CInt -> Ptr a -> CSize -> CInt -> IO CInt

data ControlPacket = ControlPacket Word32 [Word64]
data ResponseData = ResponseDataString String
                  | ResponseDataBytes [Word8]
                  | ResponseDataAncillary Word32 [Word64]
                    deriving Show
data ResponsePacket = ResponsePacket Bool [ResponseData]

socketToFd :: Socket -> CInt
socketToFd (MkSocket x _ _ _ _) = x

fdToSocket :: CInt -> IO Socket
fdToSocket fd = mkSocket fd AF_UNIX Stream 0 Connected

flatten_list :: Storable a => Ptr a -> [a] -> IO ()
flatten_list _ [] = return ()
flatten_list ptr (x:xs) =
    do poke ptr x
       flatten_list (plusPtr ptr (sizeOf x)) xs

sendBytes :: Socket -> [Word8] -> IO ()
sendBytes handle bytes =
    let len = length bytes
        worker ptr =
            do flatten_list ptr bytes
               c_send (socketToFd handle) ptr (fromIntegral len) 0
    in do allocaBytes len worker
          return ()

sendPacket :: Socket -> ControlPacket -> IO ()
sendPacket handle (ControlPacket command args) =
    let nr_args :: Word32
        nr_args = fromIntegral $ length args
        packet_size = 8 * (nr_args + 1)
        build_packet packet_ptr =
            do pokeByteOff packet_ptr 0 command
               pokeByteOff packet_ptr 4 nr_args
               flatten_list (plusPtr packet_ptr 8) args
        send_packet ptr =
            do build_packet ptr
               c_send (socketToFd handle) ptr (fromInteger $ toInteger packet_size) 0
    in allocaBytes (8 * (length args + 1)) send_packet >> return ()

recvArray :: Storable a => Int -> Socket -> Int -> IO [a]
recvArray s sock nr_items =
    if nr_items == 0 then return []
    else let len = s * nr_items
             peekArray _ 0 = return []
             peekArray ptr count =
                 do i <- peek ptr
                    rest <- peekArray (ptr `plusPtr` s) (count - 1)
                    return $ i:rest
         in allocaBytes len $ \ptr ->
             do (r, _) <- recvBufFrom sock ptr len
                if r /= len then error "other end hung up on us?"
                   else peekArray ptr nr_items

recvStringBytes :: Socket -> Int32 -> IO String
recvStringBytes sock len =
    do (bytes::[Word8]) <- recvArray 1 sock (fromIntegral len)
       return $ map (chr.fromIntegral) bytes

getResponse :: Socket -> IO ResponsePacket
getResponse handle =
    let getInt32 :: IO Int32
        getInt32 = allocaBytes 4 $ \ptr -> do recvBufFrom handle ptr 4
                                              peek ptr
        getAncillary :: IO ResponseData
        getAncillary =
            do code <- getInt32
               nr_args <- getInt32
               args <- recvArray 8 handle (fromIntegral nr_args)
               return $ ResponseDataAncillary (fromIntegral code) args
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
                 4 -> do bytes <- getInt32
                         s <- recvArray 1 handle (fromIntegral bytes)
                         worker $ (ResponseDataBytes s):acc_data
                 _ -> error $ "strange response type " ++ (show rm)
    in worker []

sendSocketCommand :: Socket -> ControlPacket -> IO ResponsePacket
sendSocketCommand handle cp =
    sendPacket handle cp >> getResponse handle

sendSocketCommandTrailer :: Socket -> ControlPacket -> [Word8] -> IO ResponsePacket
sendSocketCommandTrailer handle cp trailer =
    do sendPacket handle cp
       sendBytes handle trailer
       getResponse handle

recvSocket :: Socket -> IO Socket
recvSocket parent =
    do newFd <- recvFd parent
       mkSocket newFd AF_UNIX Stream 0 Connected


instance Forcable Socket where
    force = seq
