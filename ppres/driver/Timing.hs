{- Simple thing which allows you to record some interesting events
   along with the time at which they happen. -}
module Timing(tlog, logentry) where

import IO
import System.IO.Unsafe
import Data.IORef
import CPUTime

timingFile :: Handle
{-# NOINLINE timingFile #-}
timingFile = unsafePerformIO $ openFile "timing.dat" WriteMode

lastEventTime :: IORef Integer
{-# NOINLINE lastEventTime #-}
lastEventTime = unsafePerformIO $ newIORef 0

t :: IO Integer
t = do x <- getCPUTime
       return $ x `div` 1000000

{- Add an entry to the timing log which shows the current time, the
   time delta, and the message. -}
logentry :: String -> a -> IO a
logentry msg val = do now <- t
                      last_event <- readIORef lastEventTime
                      let time_since_last = now - last_event
                      hPutStrLn timingFile $ (show now) ++ "\t" ++ (show time_since_last) ++ "\t" ++ msg
                      writeIORef lastEventTime now
                      return val

{- Semantically, this is const id, except that it transparently
   arranges that when the returned thunk is forced an entry is added
   to the timing log. -}
tlog :: String -> a -> a
tlog msg = unsafePerformIO . logentry msg
