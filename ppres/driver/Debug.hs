module Debug(logMsg, ioLogMsg, dumpLog) where

import System.IO.Unsafe
import Data.IORef

data LogBuffer = LogBuffer { lb_strings :: [(Integer, String)],
                             lb_nr_strings :: Int }

nrLogBuffers :: Int
nrLogBuffers = 4

nrStringsPerBuffer :: Int
nrStringsPerBuffer = 1000

globalLog :: IORef ([LogBuffer], Integer)
{-# NOINLINE globalLog #-}
globalLog =
    unsafePerformIO $ newIORef (take nrLogBuffers $ repeat $ LogBuffer { lb_strings = [], lb_nr_strings = 0 },
                                0)

ioLogMsg :: String -> IO ()
ioLogMsg msg =
    do (b@(buffer:buffers), ident) <- readIORef globalLog
       writeIORef globalLog
        (if lb_nr_strings buffer < nrStringsPerBuffer
         then ((LogBuffer { lb_strings = (ident, msg):(lb_strings buffer),
                            lb_nr_strings = 1 + (lb_nr_strings buffer)}):buffers)
         else ((LogBuffer { lb_strings = [(ident, msg)],
                            lb_nr_strings = 1 }):(take (nrLogBuffers - 1) b)),
         ident + 1)

logMsg :: String -> a -> a
logMsg msg val =
    unsafePerformIO $ do ioLogMsg msg
                         return val

dumpLog :: IO ()
dumpLog =
    do buffers <- fmap fst $ readIORef globalLog
       mapM_ (\buffer -> mapM_ (\(a, b) -> putStrLn $ show a ++ ": " ++ b) $ reverse $ lb_strings buffer) $ reverse buffers
