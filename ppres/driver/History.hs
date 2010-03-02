module History(historyPrefixOf, emptyHistory, fixupWorkerForHist,
               appendHistory, truncateHistory, History, HistoryEntry(..),
               mkHistory, histLastCoord, controlTraceToWorker, truncateHistory',
               traceToWorker) where

import Control.Monad

import Types
import Worker

data HistoryEntry = HistoryRun !(Topped ReplayCoord)
                  | HistorySetThread !ThreadId
                    deriving (Eq, Show, Read)

{- We cache, in the history record, the last epoch in the history and
   the number of entries in the history.  This means we can do a quick
   out in historyPrefixOf in many useful cases. -}
data History = History (Topped ReplayCoord) Int (DList HistoryEntry) deriving (Show, Eq, Read)

histLastCoord :: History -> Topped ReplayCoord
histLastCoord (History x _ _) = x

last_coord :: [HistoryEntry] -> Topped ReplayCoord
last_coord he = worker $ reverse he
                where worker [] = Finite startCoord
                      worker ((HistoryRun x):_) = x
                      worker (_:x) = worker x

{- Either id, for valid histories, or undefined for invalid ones. -}
sanityCheckHistory :: History -> History
sanityCheckHistory hh@(History epoch len h) =
    if len /= dlLength h
    then error $ "History " ++ (show hh) ++ " had bad length (should be " ++ (show $ dlLength h) ++ ")"
    else if last_coord (dlToList h) /= epoch
         then error $ "History " ++ (show hh) ++ " had bad last epoch (should be " ++ (show $ last_coord (dlToList h)) ++ ")"
         else hh

mkHistory :: [HistoryEntry] -> History
mkHistory h = History (last_coord h) (length h) (listToDl h)

{- Estimate of cost of going from a to b. -}
replayCost :: ReplayCoord -> ReplayCoord -> Integer
replayCost a b =
    toInteger $ rc_access b - rc_access a

doHistoryEntry :: Worker -> HistoryEntry -> IO Integer
doHistoryEntry w (HistoryRun cntr) =
    do rs <- replayStateWorker w
       case rs of
         ReplayStateOkay e ->
             do runWorker w cntr
                rs' <- replayStateWorker w
                case rs' of
                  ReplayStateFinished e' -> return $ replayCost e e'
                  ReplayStateFailed _ _ e' _ ->
                      return $ replayCost e e'
                  ReplayStateOkay e' -> return $ replayCost e e'
         ReplayStateFinished _ -> return 1
         ReplayStateFailed _ _ _ _ -> return 1
doHistoryEntry w (HistorySetThread tid) = setThreadWorker w tid >> return 1

stripSharedPrefix :: History -> History -> ([HistoryEntry], [HistoryEntry])
stripSharedPrefix (History _ _ aa) (History _ _ bb) =
    worker (dlToList aa) (dlToList bb)
    where worker a [] = (a, [])
          worker [] b = ([], b)
          worker aas@(a:as) bbs@(b:bs) =
              if a == b then worker as bs
              else case (a, b) of
                     (HistoryRun an, HistoryRun bn) ->
                         if an < bn
                         then worker as bbs
                         else worker aas bs
                     _ -> ((a:as), (b:bs))

{- a `historyPrefixOf` b -> True iff a is a prefix of b (which includes
   when a and b are equal as a special case) -}
historyPrefixOf :: History -> History -> Bool
historyPrefixOf (History a_last_epoch a_length a) (History b_last_epoch b_length b) =
    if a_length > b_length || a_last_epoch > b_last_epoch
    then False
    else
        let worker aas bbs =
              {-# SCC "historyPrefixOfWorker" #-}
              case (aas, bbs) of
                (Nothing, _) -> True
                (_, Nothing) -> False
                (Just (DListEntry _ as aa), Just (DListEntry _ bs bb)) ->
                    if aa == bb then worker as bs
                    else case (aa, bb) of
                           (HistoryRun acntr, HistoryRun bcntr) ->
                               if acntr <= bcntr
                               then worker as bbs
                               else False
                           _ -> False
            res = worker (dle_head a) (dle_head b)
        in res

emptyHistory :: History
emptyHistory = mkHistory []

{- fixupWorkerForHist worker current desired -> assume that worker is
   in a state represented by current, and get it into a state
   represented by desired.  current must be a prefix of desired.
   Returns either:

   -- Left an estimate of how much that cost, or

   -- Right intermediate_history if we go over budget.
 -}
fixupWorkerForHist :: Integer -> Worker -> History -> History -> IO (Integer, Maybe History)
fixupWorkerForHist budget w current desired =
    case stripSharedPrefix current desired of
      ([], todo) ->
          worker todo 0 current
          where worker [] cost _ = return (cost, Nothing)
                worker (x:xs) cost so_far =
                    if cost > budget
                    then return $ (cost, Just so_far)
                    else do cost' <- doHistoryEntry w x
                            let (Right r) = appendHistory so_far x
                            worker xs (cost + cost') r
      _ -> error $ (show current) ++ " is not a prefix of " ++ (show desired) ++ " (historyPrefixOf " ++ (show $ historyPrefixOf current desired) ++ ")"

appendHistory :: History -> HistoryEntry -> Either String History
appendHistory (History old_last_epoch old_nr_records dlh) he =
    let h = dlToList dlh
        revh = reverse h
        lastThread [] = Just 1
        lastThread ((HistoryRun _):_) = Nothing
        lastThread ((HistorySetThread x):_) = Just x
        (hl:hrest) = revh
    in case h of
         [] -> Right $ mkHistory [he]
         _ ->
             do (new_last_epoch, new_nr_records, h') <-
                    case (hl, he) of
                      (HistoryRun x, HistoryRun y) ->
                          if x == y
                          then Right (old_last_epoch, old_nr_records, h)
                          else if x < y
                               then Right (y, old_nr_records, reverse $ (HistoryRun y):hrest)
                               else Left "appendHistory tried to go backwards in time!"
                      (HistorySetThread _, HistorySetThread lt) ->
                          Right $ 
                                if Just lt == lastThread hrest
                                then (old_last_epoch, old_nr_records - 1, reverse hrest)
                                else (old_last_epoch, old_nr_records, reverse $ he:hrest)
                      (_, HistorySetThread lt) ->
                          Right $
                                if Just lt == lastThread revh
                                then (old_last_epoch, old_nr_records, h)
                                else (old_last_epoch, old_nr_records + 1, reverse $ he:revh)
                      (_, HistoryRun y) ->
                          Right (y, old_nr_records + 1, reverse $ he:revh)
                let res = History new_last_epoch new_nr_records $ listToDl h'
                return $ sanityCheckHistory res

{- Truncate a history so that it only runs to a particular epoch number -}
truncateHistory :: History -> Topped ReplayCoord -> Either String History
truncateHistory (History _ _ hs) cntr =
    let worker [HistoryRun Infinity] = Right [HistoryRun cntr]
        worker ((HistoryRun c):hs') =
            if c < cntr then liftM ((:) $ HistoryRun c) $ worker hs'
            else Right [HistoryRun cntr]
        worker (h:hs') = liftM ((:) h) $ worker hs'
        worker _ = Left $ "truncate bad history: " ++ (show hs) ++ " to " ++ (show cntr)
    in liftM mkHistory (worker $ dlToList hs)

{- Like truncateHistory, but make sure we stay in the same thread.
   Bit of a hack. -}
truncateHistory' :: History -> Topped ReplayCoord -> Either String History
truncateHistory' (History _ _ hs) cntr =
    let worker [HistoryRun Infinity] = Right [HistoryRun cntr]
        worker ((HistoryRun c):hs') =
            if c < cntr then liftM ((:) $ HistoryRun c) $ worker hs'
            else case hs' of
                   ((HistorySetThread t):_) | cntr == c -> Right [HistoryRun cntr, HistorySetThread t]
                   _ -> Right [HistoryRun cntr]
        worker (h:hs') = liftM ((:) h) $ worker hs'
        worker _ = Left $ "truncate bad history: " ++ (show hs) ++ " to " ++ (show cntr)
    in liftM mkHistory (worker $ dlToList hs)

instance Forcable HistoryEntry where
    force (HistoryRun t) = force t
    force (HistorySetThread t) = force t

instance Forcable History where
    force (History a b h) = force a . force b . force h

{- Take a worker and a history representing its current state and run
   it forwards to some other history, logging control expressions as
   we go. -}
{- This arguably belongs in Worker.hs, but that would mean exposing
   the internals of the History type. -}
controlTraceToWorker :: Worker -> History -> History -> IO (Either String [Expression])
controlTraceToWorker work start end =
    let worker [] = return []
        worker ((HistorySetThread tid):rest) = (setThreadWorker work tid) >> worker rest
        worker ((HistoryRun cntr):rest) = do h <- controlTraceWorker work cntr
                                             rest' <- worker rest
                                             return $ h ++ rest'
    in
    case stripSharedPrefix start end of
      ([], todo) -> liftM Right $ worker todo
      _ -> return $ Left $ (show start) ++ " is not a prefix of " ++ (show end)

{- Ditto: should be in Worker.hs, but don't want to expose the innards
   of History. -}
traceToWorker :: Worker -> History -> History -> IO (Either String [TraceRecord])
traceToWorker worker start end =
    let work [] = return []
        work ((HistorySetThread tid):rest) = setThreadWorker worker tid >> work rest
        work ((HistoryRun cntr):rest) = do h <- traceWorker worker cntr
                                           rest' <- work rest
                                           return $ h ++ rest'
    in case stripSharedPrefix start end of
         ([], todo) -> liftM Right $ work todo
         _ -> return $ Left $ shows start $ " is not a prefix of " ++ (show end)
