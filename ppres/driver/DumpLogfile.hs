import Logfile
import System.Environment

dumpLogfile :: Logfile -> LogfilePtr -> IO ()
dumpLogfile lf ptr =
    case nextRecord lf ptr of
      Nothing -> return ()
      Just (rec, nextPtr) ->
          (putStrLn $ show rec) >> dumpLogfile lf nextPtr

main :: IO ()
main = do args <- getArgs
          case args of
            [path] -> do (log,startPtr) <- openLogfile path
                         dumpLogfile log startPtr
            _ -> putStrLn "wanted a single argument, the path to dump"
