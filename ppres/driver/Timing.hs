{- Simple thing which allows you to record some interesting events
   along with the time at which they happen. -}
module Timing(tlog, logentry) where

import IO
import System.IO.Unsafe
import Data.IORef
import CPUTime
import Time

timingFile :: Handle
{-# NOINLINE timingFile #-}
timingFile = unsafePerformIO $ openFile "timing.dat" WriteMode

lastEventTime :: IORef Integer
{-# NOINLINE lastEventTime #-}
lastEventTime = unsafePerformIO $ newIORef 0

startTime :: ClockTime
{-# NOINLINE startTime #-}
startTime = unsafePerformIO getClockTime

lastRTEvent :: IORef ClockTime
lastRTEvent = unsafePerformIO $ newIORef startTime

t :: IO Integer
t = do x <- getCPUTime
       return $ x `div` 1000000

tdToMicroseconds :: TimeDiff -> Integer
tdToMicroseconds td = (toInteger $ tdSec td) * 1000000 + (tdPicosec td `div` 1000000)

{- Add an entry to the timing log which shows the current time, the
   time delta, and the message. -}
logentry :: String -> a -> IO a
logentry msg val = do now <- t
                      rtNow <- getClockTime
                      last_event <- readIORef lastEventTime
                      rtLastEvent <- readIORef lastRTEvent
                      let time_since_last = now - last_event
                          rt_since_last = tdToMicroseconds $ rtNow `diffClockTimes` rtLastEvent
                          rt_since_start = tdToMicroseconds $ rtNow `diffClockTimes` startTime
                      hPutStrLn timingFile $ (show now) ++ "\t" ++ (show time_since_last) ++ "\t" ++ (show rt_since_start) ++ "\t" ++ (show rt_since_last) ++ "\t" ++ msg
                      writeIORef lastEventTime now
                      writeIORef lastRTEvent rtNow
                      return val

{- Semantically, this is const id, except that it transparently
   arranges that when the returned thunk is forced an entry is added
   to the timing log. -}
tlog :: String -> a -> a
tlog msg = unsafePerformIO . logentry msg
