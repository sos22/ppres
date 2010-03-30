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

{- You need to be quite careful about stack and heap usage here,
   because the log can build up for several hours and then got forced
   in one big go, which can lead to memory leaks and stack overflows.
   The seqs fix it. -}
ioLogMsg :: String -> IO ()
ioLogMsg msg =
    do (b@(buffer:buffers), ident) <- readIORef globalLog
       writeIORef globalLog $ let nextId = ident + 1
                                  x = seq nextId (if lb_nr_strings buffer < nrStringsPerBuffer
                                                  then let s = (ident, msg):(lb_strings buffer)
                                                       in seq s ((LogBuffer { lb_strings = s,
                                                                              lb_nr_strings = 1 + (lb_nr_strings buffer)}):buffers)
                                                  else ((LogBuffer { lb_strings = [(ident, msg)],
                                                                     lb_nr_strings = 1 }):(take (nrLogBuffers - 1) b)),
                                                  nextId)
                              in x

logMsg :: String -> a -> a
logMsg msg val =
    unsafePerformIO $ do ioLogMsg msg
                         return val

dumpLog :: IO ()
dumpLog =
    do buffers <- fmap fst $ readIORef globalLog
       mapM_ (\buffer -> mapM_ (\(a, b) -> putStrLn $ show a ++ ": " ++ b) $ reverse $ lb_strings buffer) $ reverse buffers
