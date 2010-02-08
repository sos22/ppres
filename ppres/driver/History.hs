module History(historyPrefixOf, emptyHistory, fixupWorkerForHist,
               appendHistory, truncateHistory, History, HistoryEntry(..),
               mkHistory) where

import Control.Monad

import Types
import Worker

data HistoryEntry = HistoryRun (Topped EpochNr)
                  | HistoryRunThread ThreadId
                  | HistoryRunMemory ThreadId Integer
                    deriving (Eq, Show)

data History = History [HistoryEntry] deriving (Show, Eq)

mkHistory :: [HistoryEntry] -> History
mkHistory = History

doHistoryEntry :: Worker -> HistoryEntry -> IO Integer
doHistoryEntry w (HistoryRun cntr) =
    let deEpoch (EpochNr x) = x
    in
    do rs <- replayStateWorker w
       case rs of
         ReplayStateOkay e ->
             do runWorker w cntr
                rs' <- replayStateWorker w
                case rs' of
                  ReplayStateFinished -> return 100 -- Just make something up
                  ReplayStateFailed _ (FailureReasonControl _ _ e') ->
                      return $ deEpoch $ e' - e + 1
                  ReplayStateOkay e' -> return $ deEpoch $ e' - e + 1
         ReplayStateFinished -> return 1
         ReplayStateFailed _ (FailureReasonControl _ _ _) -> return 1
doHistoryEntry w (HistoryRunThread tid) = traceThreadWorker w tid >> return 1
doHistoryEntry w (HistoryRunMemory tid cntr) =
    runMemoryWorker w tid cntr >> return cntr

stripSharedPrefix :: History -> History -> (History, History)
stripSharedPrefix (History aa) (History bb) =
    case worker aa bb of
      (a', b') -> (History a', History b')
    where worker a [] = (a, [])
          worker [] b = ([], b)
          worker aas@(a:as) bbs@(b:bs) =
              if a == b then worker as bs
              else case (a, b) of
                     (HistoryRun an, HistoryRun bn) ->
                         if an < bn
                         then worker as bbs
                         else worker aas bs
                     (HistoryRunMemory atid acntr,
                      HistoryRunMemory btid bcntr) | atid == btid ->
                         if acntr < bcntr
                         then worker as ((HistoryRunMemory btid $ bcntr - acntr):bs)
                         else worker ((HistoryRunMemory atid $ acntr - bcntr):as) bs

                     _ -> ((a:as), (b:bs))

{- a `historyPrefixOf` b -> True iff a is a prefix of b (which includes
   when a and b are equal as a special case) -}
historyPrefixOf :: History -> History -> Bool
historyPrefixOf a b =
    case  stripSharedPrefix a b of
      (History [], _) -> True
      _ -> False

emptyHistory :: History
emptyHistory = History []

{- fixupWorkerForHist worker current desired -> assume that worker is
   in a state represented by current, and get it into a state
   represented by desired.  current must be a prefix of desired.
   Returns an estimate of how much it cost us to do so. -}
fixupWorkerForHist :: Worker -> History -> History -> IO Integer
fixupWorkerForHist w current desired =
    case stripSharedPrefix current desired of
      (History [], History todo) -> liftM sum $ mapM (doHistoryEntry w) todo
      _ -> error ((show current) ++ " is not a prefix of " ++ (show desired))

appendHistory :: History -> HistoryEntry -> History
appendHistory (History []) he = History [he]
appendHistory (History h) he =
    History $ 
    let (hl:hrest) = reverse h
    in case (hl, he) of
         (HistoryRun x, HistoryRun y) ->
             if x == y
             then h
             else if x < y
                  then reverse $ (HistoryRun y):hrest
                  else error "appendHistory tried to go backwards in time!"
         (HistoryRunMemory xtid xcntr, HistoryRunMemory ytid ycntr)
             | xtid == ytid ->
                 reverse $ (HistoryRunMemory xtid (xcntr + ycntr)):hrest
         _ -> reverse $ he:hl:hrest


{- Truncate a history so that it only runs to a particular epoch number -}
truncateHistory :: History -> Topped EpochNr -> History
truncateHistory (History hs) cntr =
    History $ worker hs
    where worker [HistoryRun Infinity] = [HistoryRun cntr]
          worker ((HistoryRun c):hs') =
              if c < cntr then (HistoryRun c):(worker hs')
              else [HistoryRun cntr]
          worker ((h@(HistoryRunMemory _ _)):hs') = h:(worker hs')
          worker _ = error $ "truncate bad history " ++ (show hs)


instance Forcable HistoryEntry where
    force (HistoryRun t) = force t
    force (HistoryRunThread t) = force t
    force (HistoryRunMemory t i) = force t . force i

instance Forcable History where
    force (History h) = force h
