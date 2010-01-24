{-# LANGUAGE ScopedTypeVariables #-}
module WorldState(initialWorldState, doAssignment, lookupVariable,
                  doRename) where

import Foreign.C.Types

import Socket
import Types
import UIValue

initialWorldState :: CInt -> IO WorldState
initialWorldState fd =
    do f <- fdToSocket fd
       let root_snap = Worker f
       return $ WorldState { ws_worker = root_snap,
                             ws_bindings = [("root", UIValueSnapshot root_snap)] }

lookupVariable :: VariableName -> WorldState -> Maybe UIValue
lookupVariable name ws = lookup name $ ws_bindings ws

doAssignment :: WorldState -> VariableName -> UIValue -> IO WorldState
doAssignment ws name val =
    do case lookupVariable name ws of
         Nothing -> return ()
         Just oldVal -> uiv_destruct oldVal
       return $ ws { ws_bindings = (name, val):
                                   [b | b <- (ws_bindings ws), fst b /= name]}

{- We impose, in effect, a linear type system on the client language,
   so you can rename stuff but not duplicate it. -}
doRename :: WorldState -> VariableName -> VariableName -> IO WorldState
doRename ws dest src =
    case lookupVariable src ws of
      Nothing -> do putStrLn $ "can't find " ++ src
                    return ws
      Just s ->
          do case lookupVariable dest ws of
               Nothing -> return ()
               Just d -> uiv_destruct d
             return $ ws { ws_bindings =
                               (dest,s):[(n, v) | (n, v) <- ws_bindings ws,
                                              n /= src && n/= dest] }
