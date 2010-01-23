module Main(main) where

import System.Environment
import System.Exit
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import IO
import Data.Word
import Control.Monad

import Types
import Worker
import Snapshot
import WorldState

data UICommand = UIExit
               | UIWhereAmI
               | UISnapshot
               | UIListSnapshots
               | UIKillSnapshot SnapshotId
               | UIActivateSnapshot SnapshotId
               | UIRun Integer
               | UITrace Integer
               | UITraceThread ThreadId
               | UITraceAddress Word64
               | UIRunMemory ThreadId Integer
                 deriving Show

command_lexer :: P.TokenParser ()
command_lexer = P.makeTokenParser haskellDef

snapshot_id_parser :: Parser SnapshotId
snapshot_id_parser = P.integer command_lexer
thread_id_parser :: Parser ThreadId
thread_id_parser = P.integer command_lexer

command_parser :: Parser UICommand
command_parser =
    do w <- P.identifier command_lexer
       case w of
         "exit" -> return UIExit
         "quit" -> return UIExit
         "loc" -> return UIWhereAmI
         "whereami" -> return UIWhereAmI
         "snapshot" -> return UISnapshot
         "ls" -> return UIListSnapshots
         "kill" -> liftM UIKillSnapshot snapshot_id_parser
         "activate" -> liftM UIActivateSnapshot snapshot_id_parser
         "run" -> liftM UIRun (P.integer command_lexer)
         "trace" -> liftM UITrace (P.integer command_lexer)
         "tracet" -> liftM UITraceThread thread_id_parser
         "tracem" -> do addr <- P.integer command_lexer
                        return $ UITraceAddress $ fromInteger addr
         "runm" -> do t <- thread_id_parser
                      n <- P.integer command_lexer
                      return $ UIRunMemory t n
         _ -> unexpected ("keyword " ++ w)

getCommand :: IO UICommand
getCommand =
    do putStr "> "
       hFlush stdout
       l <- getLine
       case parse command_parser "" l of
         Left err -> do putStrLn $ "Cannot parse command " ++ l ++ ": " ++ (show err)
                        getCommand
         Right v -> return v

ignore :: IO a -> IO ()
ignore x = x >> return ()

runCommand :: UICommand -> WorldState -> IO WorldState
runCommand UIExit ws =
    sequence_ [maybe (return ()) (ignore . killWorker) $ ws_worker ws,
               mapM_ killSnapshot $ ws_snapshots ws,
               ignore $ killSnapshot $ ws_root_snapshot ws,
               exitWith ExitSuccess] >> return ws
runCommand UISnapshot ws =
    withWorker ws $
     \w ->
        do s <- takeSnapshot (ws_next_snap_id ws) w
           case s of
             Nothing -> do putStrLn "cannot take snapshot"
                           return ws
             Just s' -> do print $ snapshot_id s'
                           return $ ws { ws_snapshots = s':(ws_snapshots ws) }
runCommand UIListSnapshots ws =
    do mapM_ (\s -> print $ snapshot_id s) $ ws_snapshots ws
       return ws
runCommand (UIKillSnapshot sid) ws =
    if sid == (snapshot_id $ ws_root_snapshot ws)
    then do putStrLn "Can't kill the root snapshot"
            return ws
    else
        case getSnapshot ws sid of
          Nothing -> do putStrLn ("Can't find snapshot " ++ (show sid))
                        return ws
          Just s -> do r <- killSnapshot s
                       if r
                        then return $ ws { ws_snapshots =
                                               [s' | s' <- ws_snapshots ws,
                                                snapshot_id s' /= sid] }
                        else do putStrLn "Error killing snapshot"
                                return ws
runCommand (UIActivateSnapshot sid) ws =
    case getSnapshot ws sid of
      Nothing -> do putStrLn ("Cannot find snapshot " ++ (show sid))
                    return ws
      Just s -> do worker <- activateSnapshot s
                   case worker of
                     Nothing -> do putStrLn "cannot activate snapshot"
                                   return ws
                     Just _ ->
                         do case ws_worker ws of
                              Nothing -> return ()
                              Just w' -> ignore $ killWorker w'
                            return $ ws { ws_worker = worker } 
runCommand (UIRun cntr) ws =
    withWorker ws $ \w -> do runWorker w cntr
                             return ws
runCommand (UITrace cntr) ws =
    withWorker ws $ \w -> do traceWorker w cntr
                             return ws
runCommand (UITraceThread ident) ws =
    withWorker ws $ \w -> do traceThreadWorker w ident
                             return ws
runCommand (UITraceAddress addr) ws =
    withWorker ws $ \w -> do traceAddressWorker w addr
                             return ws
runCommand (UIRunMemory tid cntr) ws =
    withWorker ws $ \w -> do runMemoryWorker w tid cntr
                             return ws

commandLoop :: WorldState -> IO ()
commandLoop ws =
    do cmd <- getCommand
       ws' <- runCommand cmd ws
       commandLoop ws'

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> error "need the file descriptor to communicate on"
            (_:_:_) -> error "Too many arguments"
            [fdString] -> do initState <- initialWorldState $ read fdString
                             commandLoop initState
