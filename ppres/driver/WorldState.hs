{-# LANGUAGE ScopedTypeVariables #-}
module WorldState(initialWorldState, doAssignment) where

import Foreign.C.Types

import Socket
import Types
import Snapshot

initialWorldState :: CInt -> IO WorldState
initialWorldState fd =
    do f <- fdToSocket fd
       let root_snap = Snapshot f "root"
       worker <- activateSnapshot root_snap
       case worker of
         Nothing -> error "cannot activate root snapshot"
         Just w ->
           return $ WorldState { ws_worker = w,
                                 ws_snapshots = [],
                                 ws_root_snapshot = root_snap,
                                 ws_bindings = [] }

lookupVariable :: VariableName -> WorldState -> Maybe UIValue
lookupVariable name ws = lookup name $ ws_bindings ws

doAssignment :: WorldState -> VariableName -> UIValue -> IO WorldState
doAssignment ws name val =
    do case lookupVariable name ws of
         Nothing -> return ()
         Just oldVal -> uiv_destruct oldVal
       return $ ws { ws_bindings = (name, val):
                                   [b | b <- (ws_bindings ws), fst b /= name]}
