{-# LANGUAGE ForeignFunctionInterface #-}
module Main(main) where

import System.Environment
import System.Exit
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import IO
import Data.Word
import Data.Int
import Data.IORef
import Control.Monad
import Foreign.Storable
import Foreign.Ptr
import Foreign.Marshal.Alloc

import Network.Socket

import Foreign.C.Types

import Debug.Trace

foreign import ccall "send"
  c_send :: CInt -> Ptr a -> CSize -> CInt -> IO CInt

type SnapshotId = Integer
type ThreadId = Integer

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

data Worker = Worker { worker_fd :: Socket }
data Snapshot = Snapshot { snapshot_fd :: Socket,
                           snapshot_id :: SnapshotId }
data WorldState = WorldState { ws_worker :: Maybe Worker,
                               ws_snapshots :: [Snapshot],
                               ws_root_snapshot :: Snapshot,
                               ws_next_snap_id :: IORef SnapshotId }

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

socketToFd :: Socket -> CInt
socketToFd (MkSocket x _ _ _ _) = x

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

sendWorkerCommand :: Worker -> Word32 -> [Word64] -> IO Int32
sendWorkerCommand worker command args =
    sendSocketCommand (worker_fd worker) command args

sendSnapshotCommand :: Snapshot -> Word32 -> [Word64] -> IO Int32
sendSnapshotCommand snapshot command args =
    sendSocketCommand (snapshot_fd snapshot) command args

getSnapshot :: WorldState -> SnapshotId -> Maybe Snapshot
getSnapshot ws sid =
    worker (ws_snapshots ws)
    where worker [] = if sid == (snapshot_id $ ws_root_snapshot ws)
                      then Just $ ws_root_snapshot ws
                      else Nothing
          worker (s:ss) = if snapshot_id s == sid then Just s
                          else worker ss

activateSnapshot :: Snapshot -> IO (Maybe Worker)
activateSnapshot ss =
    do ack <- sendSnapshotCommand ss 0xabce []
       if ack /= 0
        then return Nothing
        else do fd <- recvSocket (snapshot_fd ss)
                return $ Just $ Worker { worker_fd = fd }

killWorker :: Worker -> IO Bool
killWorker worker =
    do ack <- sendWorkerCommand worker 0x1235 []
       if ack == 0
          then do sClose $ worker_fd worker
                  return True
          else return False

killSnapshot :: Snapshot -> IO Bool
killSnapshot worker =
    do ack <- sendSnapshotCommand worker 0xabcd []
       if ack == 0
          then do sClose $ snapshot_fd worker
                  return True
          else return False

ignore :: IO a -> IO ()
ignore x = x >> return ()

recvSocket :: Socket -> IO Socket
recvSocket parent =
    do newFd <- recvFd parent
       mkSocket newFd AF_UNIX Stream 0 Connected

runWorker :: Worker -> Integer -> IO ()
runWorker worker cntr =
    do ack <- sendWorkerCommand worker 0x1236 [fromInteger cntr]
       if ack /= 0
          then putStrLn "error running worker"
          else return ()

traceWorker :: Worker -> Integer -> IO ()
traceWorker worker cntr =
    do ack <- sendWorkerCommand worker 0x1237 [fromInteger cntr]
       if ack /= 0
          then putStrLn "error running worker"
          else return ()

traceThreadWorker :: Worker -> ThreadId -> IO ()
traceThreadWorker worker tid =
    do ack <- sendWorkerCommand worker 0x1239 [fromInteger tid]
       if ack /= 0
          then putStrLn "error running worker"
          else return ()

traceAddressWorker :: Worker -> Word64 -> IO ()
traceAddressWorker worker addr =
    do ack <- sendWorkerCommand worker 0x123a [addr]
       if ack /= 0
          then putStrLn "error running worker"
          else return ()

runMemoryWorker :: Worker -> ThreadId -> Integer -> IO ()
runMemoryWorker worker tid cntr =
    do ack <- sendWorkerCommand worker 0x1238 [fromInteger $ tid, fromInteger $ cntr]
       if ack /= 0
          then putStrLn "error running worker"
          else return ()

withWorker :: WorldState -> (Worker -> IO WorldState) -> IO WorldState
withWorker ws f =
    case ws_worker ws of
      Nothing -> do putStrLn "Need a worker for that"
                    return ws
      Just w -> f w

takeSnapshot :: IORef SnapshotId -> Worker -> IO (Maybe Snapshot)
takeSnapshot sid' worker =
    do sid <- readIORef sid'
       writeIORef sid' (sid + 1)
       ack <- sendWorkerCommand worker 0x1234 []
       if ack < 0
          then return Nothing
          else do newFd <- recvSocket (worker_fd worker)
                  return $ Just $ Snapshot {snapshot_fd = newFd,
                                            snapshot_id = sid }

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

initialWorldState :: Socket -> IO WorldState
initialWorldState h =
    do next_id <- newIORef 1
       return $ WorldState { ws_worker = Nothing,
                             ws_snapshots = [],
                             ws_root_snapshot = Snapshot h 0,
                             ws_next_snap_id = next_id }

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> error "need the file descriptor to communicate on"
            (_:_:_) -> error "Too many arguments"
            [fdString] -> do f <- mkSocket (read fdString) AF_UNIX Stream 0 Connected
                             initState <- initialWorldState f
                             commandLoop initState
