module Debug(logMsg, dumpLog) where

import System.IO.Unsafe
import Data.IORef

data LogBuffer = LogBuffer { lb_strings :: [String],
                             lb_nr_strings :: Int }

nrLogBuffers :: Int
nrLogBuffers = 4

nrStringsPerBuffer :: Int
nrStringsPerBuffer = 1000

globalLog :: IORef [LogBuffer]
{-# NOINLINE globalLog #-}
globalLog =
    unsafePerformIO $ newIORef $ take nrLogBuffers $ repeat $ LogBuffer { lb_strings = [], lb_nr_strings = 0 }

logMsg :: String -> a -> a
logMsg msg val =
    unsafePerformIO $ do b@(buffer:buffers) <- readIORef globalLog
                         writeIORef globalLog $
                          if lb_nr_strings buffer < nrStringsPerBuffer
                          then ((LogBuffer { lb_strings = msg:(lb_strings buffer),
                                             lb_nr_strings = 1 + (lb_nr_strings buffer)}):buffers)
                          else ((LogBuffer { lb_strings = [msg],
                                             lb_nr_strings = 1 }):(take (nrLogBuffers - 1) b))
                         return val

dumpLog :: IO ()
dumpLog =
    do buffers <- readIORef globalLog
       mapM_ (\buffer -> mapM_ putStrLn $ reverse $ lb_strings buffer) buffers
