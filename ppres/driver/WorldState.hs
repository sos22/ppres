module WorldState(initialWorldState, doAssignment, lookupVariable,
                  lookupSnapshot, doRename, exitWorld) where

import System.Exit
import Foreign.C.Types
import Control.Monad.State

import Socket
import Types
import UIValue
import History
import WorkerCache

initialWorldState :: CInt -> IO WorldState
initialWorldState fd =
    do f <- fdToSocket fd
       let root_snap = Worker f
       initWorkerCache root_snap
       return $ WorldState { ws_bindings = [("start", UIValueSnapshot emptyHistory)] }

lookupVariable :: VariableName -> WorldMonad (Maybe UIValue)
lookupVariable name =
    do s <- get
       return $ lookup name $ ws_bindings s

lookupSnapshot :: VariableName -> WorldMonad (Maybe History)
lookupSnapshot name =
    do s <- lookupVariable name
       case s of
         Just (UIValueSnapshot s') -> return $ Just s'
         _ -> do liftIO $ putStrLn $ name ++ " is not a snapshot"
                 return Nothing

doAssignment :: VariableName -> UIValue -> WorldMonad ()
doAssignment name val =
    do v <- lookupVariable name
       case v of
         Nothing -> return ()
         Just oldVal -> uiv_destruct oldVal
       modify $ \ws -> ws { ws_bindings = (name, val):
                            [b | b <- (ws_bindings ws), fst b /= name]}

{- We impose, in effect, a linear type system on the client language,
   so you can rename stuff but not duplicate it. -}
doRename :: VariableName -> VariableName -> WorldMonad ()
doRename dest src =
    do s <- lookupVariable src
       d <- lookupVariable dest
       case s of
         Nothing -> liftIO $ putStrLn $ "can't find " ++ src
         Just s' ->
             do case d of
                  Nothing -> return ()
                  Just d' -> uiv_destruct d'
                modify $ \ws -> ws { ws_bindings = (dest,s'):
                                    [(n, v) | (n, v) <- ws_bindings ws,
                                              n /= src && n/= dest] }

exitWorld :: WorldMonad ()
exitWorld =
    liftIO $ do destroyWorkerCache
                exitWith ExitSuccess
