module History(historyPrefixOf, emptyHistory, fixupWorkerForHist,
               appendHistory, truncateHistory, History,
               mkHistory, histLastCoord, controlTraceToWorker,
               traceToWorker, runThread, absHistSuffix, threadAtAccess,
               setRegister) where

import Control.Monad.Error
import Data.Word

import Types
import Worker
import Util

data HistoryEntry = HistoryRun !ThreadId !(Topped AccessNr)
                  | HistorySetRegister !ThreadId !RegisterName !Word64
                    deriving (Eq, Show, Read)

{- We cache, in the history record, the last epoch in the history and
   the number of entries in the history.  This means we can do a quick
   out in historyPrefixOf in many useful cases. -}
data History = History (Topped AccessNr) Int (DList HistoryEntry) deriving (Show, Eq, Read)

runThread :: History -> ThreadId -> Topped AccessNr -> Either String History
runThread hist tid acc =
    appendHistory hist $ HistoryRun tid acc

setRegister :: History -> ThreadId -> RegisterName -> Word64 -> History
setRegister hist tid reg val =
    deError $ appendHistory hist $ HistorySetRegister tid reg val

histLastCoord :: History -> Topped AccessNr
histLastCoord (History x _ _) = x

last_coord :: [HistoryEntry] -> Topped AccessNr
last_coord he = worker $ reverse he
                where worker [] = Finite $ AccessNr 0
                      worker ((HistoryRun _ x):_) = x
                      worker ((HistorySetRegister _ _ _):x) = worker x

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
replayCost :: AccessNr-> AccessNr -> Integer
replayCost a b =
    toInteger $ b - a

doHistoryEntry :: Worker -> HistoryEntry -> IO Integer
doHistoryEntry w (HistoryRun tid cntr) =
    do setThreadWorker w tid
       rs <- replayStateWorker w
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
doHistoryEntry w (HistorySetRegister tid reg val) =
    do setRegisterWorker w tid reg val
       return 1

stripSharedPrefix :: History -> History -> ([HistoryEntry], [HistoryEntry])
stripSharedPrefix (History _ _ aa) (History _ _ bb) =
    worker (dlToList aa) (dlToList bb)
    where worker a [] = (a, [])
          worker [] b = ([], b)
          worker aas@(a:as) bbs@(b:bs) =
              if a == b then worker as bs
              else case (a, b) of
                     (HistoryRun atid an, HistoryRun btid bn) | atid == btid ->
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
                           (HistoryRun atid acntr, HistoryRun btid bcntr) | atid == btid ->
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
        (hl:hrest) = revh
    in case h of
         [] -> Right $ mkHistory [he]
         _ ->
             do (new_last_epoch, new_nr_records, h') <-
                    case (hl, he) of
                      (HistoryRun xtid x, HistoryRun ytid y)
                          | x == y -> Right (old_last_epoch, old_nr_records, h) {- didn't advance -> no-op -}
                          | y < x -> Left "appendHistory tried to go backwards in time!"
                          | xtid == ytid ->
                              Right (y, old_nr_records, reverse $ he:hrest)
                          | otherwise ->
                              Right (y, old_nr_records + 1, reverse $ he:revh)
                      _ -> Right (old_last_epoch, old_nr_records + 1, reverse $ he:revh)
                let res = History new_last_epoch new_nr_records $ listToDl h'
                return $ sanityCheckHistory res

{- Truncate a history so that it only runs to a particular epoch number -}
truncateHistory :: History -> Topped AccessNr -> Either String History
truncateHistory (History _ _ hs) cntr =
    let worker [HistoryRun tid Infinity] = Right [HistoryRun tid cntr]
        worker ((HistoryRun tid c):hs') =
            if c < cntr then liftM ((:) $ HistoryRun tid c) $ worker hs'
            else Right [HistoryRun tid cntr]
        worker _ = Left $ "truncate bad history: " ++ (show hs) ++ " to " ++ (show cntr)
    in liftM mkHistory (worker $ dlToList hs)

{- Make a new history in which access numbers are all relative to the
   previous access, rather than absolute from the beginning of the
   world. -}
mkRelativeHistory :: AccessNr -> [HistoryEntry] -> [(ThreadId, Integer)]
mkRelativeHistory _ [] = []
mkRelativeHistory (AccessNr base) ((HistoryRun tid (Finite aa@(AccessNr acc))):others) =
    (tid, acc - base):(mkRelativeHistory aa others)
mkRelativeHistory _ [HistoryRun _ Infinity] = error "can't convert infinite history to relative form"
mkRelativeHistory _ _ = error "history is broken: stuff beyond infinity"

relHistToThreadAbs :: [(ThreadId, Integer)] -> [(ThreadId, Integer)] -> [(ThreadId, Integer)]
relHistToThreadAbs _ [] = []
relHistToThreadAbs currentAccs ((tid,relAcc):others) =
    let currentAcc = maybe 0 id $ lookup tid currentAccs
        newAcc = currentAcc + relAcc
        newLookup = (tid,newAcc):(filter ((/=) tid . fst) currentAccs)
    in (tid,newAcc):(relHistToThreadAbs newLookup others)

mkThreadAbsoluteHistory :: AccessNr -> [HistoryEntry] -> [(ThreadId, Integer)]
mkThreadAbsoluteHistory acc = relHistToThreadAbs [] . mkRelativeHistory acc

absHistSuffix :: History -> History -> Either String [(ThreadId, Integer)]
absHistSuffix prefix@(History (Finite pacc) _ _) hist =
    case stripSharedPrefix hist prefix of
      (hh, []) -> Right $ mkThreadAbsoluteHistory pacc hh
      _ -> Left $ (show prefix) ++ " is not a prefix of " ++ (show hist)
absHistSuffix _ _ = Left "tried to strip an infinite prefix"

threadAtAccess :: History -> AccessNr -> Either String ThreadId
threadAtAccess (History _ _ items) acc =
    foldr (\(HistoryRun tid acc') rest ->
               if (Finite acc) < acc'
               then Right tid
               else rest) (Left "ran out of history") $ dlToList items

instance Forcable HistoryEntry where
    force (HistoryRun tid t) = force tid . force t
    force (HistorySetRegister tid reg val) = force tid . force reg . force val

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
        worker ((HistoryRun tid cntr):rest) = do setThreadWorker work tid
                                                 h <- controlTraceWorker work cntr
                                                 rest' <- worker rest
                                                 return $ h ++ rest'
        worker ((HistorySetRegister tid reg val):rest) = do setRegisterWorker work tid reg val
                                                            worker rest
    in
    case stripSharedPrefix start end of
      ([], todo) -> liftM Right $ worker todo
      _ -> return $ Left $ (show start) ++ " is not a prefix of " ++ (show end)

{- Ditto: should be in Worker.hs, but don't want to expose the innards
   of History. -}
traceToWorker :: Worker -> History -> History -> IO (Either String [TraceRecord])
traceToWorker worker start end =
    let work [] = return []
        work ((HistoryRun tid cntr):rest) =
            do setThreadWorker worker tid
               h <- traceWorker worker cntr
               rest' <- work rest
               return $ h ++ rest'
        work ((HistorySetRegister tid reg val):rest) =
            do setRegisterWorker worker tid reg val
               work rest
    in case stripSharedPrefix start end of
         ([], todo) -> liftM Right $ work todo
         _ -> return $ Left $ shows start $ " is not a prefix of " ++ (show end)
