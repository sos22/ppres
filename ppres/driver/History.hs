module History(historyPrefixOf, emptyHistory, fixupWorkerForHist,
               appendHistory, truncateHistory) where

import Types
import Worker

doHistoryEntry :: Worker -> HistoryEntry -> IO Bool
doHistoryEntry w (HistoryRun cntr) = runWorker w cntr
doHistoryEntry w (HistoryRunThread tid) = traceThreadWorker w tid >> return True
doHistoryEntry w (HistoryRunMemory tid cntr) =
    runMemoryWorker w tid cntr >> return True

stripSharedPrefix :: History -> History -> (History, History)
stripSharedPrefix (History aa) (History bb) =
    case worker aa bb of
      (a', b') -> (History a', History b')
    where worker a [] = (a, [])
          worker [] b = ([], b)
          worker (a:as) (b:bs) =
              if a == b then worker as bs
              else case (a, b) of
                     (HistoryRun an, HistoryRun bn) ->
                         if an == (-1)
                         then worker (a:as) bs
                         else if bn == (-1)
                              then worker as (b:bs)
                              else if an < bn
                                   then worker as ((HistoryRun $ bn - an):bs)
                                   else worker ((HistoryRun $ an - bn):as) bs
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
   Returns True if we succeed or False if something goes wrong. -}
fixupWorkerForHist :: Worker -> History -> History -> IO Bool
fixupWorkerForHist w current desired =
    case stripSharedPrefix current desired of
      (History [], History todo) ->
          worker todo
      _ -> error ((show current) ++ " is not a prefix of " ++ (show desired))
    where worker [] = return True
          worker (d:ds) =
              do r <- doHistoryEntry w d
                 case r of
                   False -> return r
                   True -> worker ds

appendHistory :: History -> HistoryEntry -> History
appendHistory (History e) he =
    History $ e ++ [he]

{- Truncate a history so that it only runs to a particular record number -}
truncateHistory :: History -> Integer -> History
truncateHistory (History hs) cntr =
    History $ worker hs
    where worker [HistoryRun (-1)] = [HistoryRun cntr]
          worker ((HistoryRun c):hs') =
              if c <= cntr then (HistoryRun c):(worker hs')
              else [HistoryRun cntr]
          worker ((h@(HistoryRunMemory _ _)):hs') = h:(worker hs')
          worker _ = error $ "truncate bad history " ++ (show hs)

