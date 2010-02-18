module History(historyPrefixOf, emptyHistory, fixupWorkerForHist,
               appendHistory, truncateHistory, History, HistoryEntry(..),
               mkHistory, historyDiff, applyHistoryDiff, HistoryDiff) where

import Control.Monad
import Debug.Trace

import Types
import Worker

data HistoryEntry = HistoryRun !(Topped EpochNr)
                  | HistoryRunMemory !Integer
                  | HistorySetThread !ThreadId
                    deriving (Eq, Show, Read)

{- A history diff is a representation of a function of type
   History->Maybe History where the intent is that the result is the
   old history with some fixups applied.  It has three parts:

   -- An old suffix which is to be stripped from the end of the old
      history.

   -- An optional record counter.  Once the old suffix has been
      stripped, the final entry in the old history, which must be a
      finite HistoryRun, will have this number added to its target
      record number.  If that makes the target negative (which implies
      that this number is negative) then the apply fails.

   -- A new suffix which is to be added.

   If the diff doesn't apply, the result is Nothing.
-}
{- Caution: the history entries in the lists are *relative*, whereas
   everywhere else they're absolute -}
data HistoryDiff = HistoryDiff { hd_old_suffix :: [HistoryEntry],
                                 hd_record_fixup :: Maybe EpochNr,
                                 hd_new_suffix :: [HistoryEntry] } deriving Show

{- Convert all of the epoch numbers in a history to be relative to the
   previous record. -}
relativeHistory :: [HistoryEntry] -> Topped EpochNr -> [HistoryEntry]
relativeHistory []                      _    = []
relativeHistory ((HistoryRun x):others) base = HistoryRun (x - base):(relativeHistory others x)
relativeHistory (x             :y)      base = x:(relativeHistory y base)

{- Inverse -}
absoluteHistory :: [HistoryEntry] -> Topped EpochNr -> [HistoryEntry]
absoluteHistory []                      _    = []
absoluteHistory ((HistoryRun x):others) base = HistoryRun (x + base):(absoluteHistory others x)
absoluteHistory (x             :y)      base = x:(absoluteHistory y base)

{- Compute a history diff.  There is a trivial diff from a to b which
   is always valid, which is just to take the old suffix as the
   entirety of a and the new one as the entirety of b, with no fixup,
   but that's pretty useless, so we try to do a bit better than that. -}
historyDiff :: History -> History -> HistoryDiff
historyDiff (History _ _ as') (History _ _ bs') =
    worker (relativeHistory as' 0) (relativeHistory bs' 0)
    where
      worker aas@(a:as) bbs@(b:bs)
          | a == b = worker as bs {- Strip identical prefix -}
          | otherwise =
              case (a, b) of
                (HistoryRun (Finite a_target), HistoryRun (Finite b_target)) ->
                    HistoryDiff { hd_old_suffix = as,
                                  hd_record_fixup = Just $ b_target - a_target,
                                  hd_new_suffix = bs }
                _ -> HistoryDiff { hd_old_suffix = aas,
                                   hd_record_fixup = Nothing,
                                   hd_new_suffix = bbs }

      worker as bs =
          {- One of the histories was a prefix of the other.  Easy
             case. -}
          HistoryDiff { hd_old_suffix = as,
                        hd_record_fixup = Nothing,
                        hd_new_suffix = bs }

applyHistoryDiff :: HistoryDiff -> History -> Maybe History
applyHistoryDiff hd (History _ _ base) =
    let revbase = reverse $ relativeHistory base 0
        old_suffix = reverse $ hd_old_suffix hd

        {- Slightly misnamed, because it works on the reversed history
           and suffix, and so mechanically it removes a shared
           *prefix*.  It's the suffix of the original history,
           though. -}
        {- Try to match the first and second arguments together.
           Whenever they match, strip that item and proceed.  If we
           get to the end of the second list, return Just the first.
           If we don't get to the end, return Nothing. -}
        strip_suffix b [] = Just b
        strip_suffix (a:as) (b:bs) | a == b = strip_suffix as bs
                                   | otherwise = Nothing
        strip_suffix [] _ = Nothing

        apply_record_fixup :: Maybe EpochNr -> [HistoryEntry] -> Maybe [HistoryEntry]
        apply_record_fixup Nothing x = Just x
        apply_record_fixup (Just fixup) ((HistoryRun (Finite x)):others) =
            let newx = fixup + x
            in if newx < 0 then Nothing
               else if newx == 0 then Just others
                    else Just $ (HistoryRun (Finite newx)):others
        apply_record_fixup _ _ = Nothing

    in do no_suffix <- strip_suffix revbase old_suffix
          no_suffix_fixed <- apply_record_fixup (hd_record_fixup hd) no_suffix
          return $ mkHistory $ absoluteHistory (reverse $ (reverse $ hd_new_suffix hd) ++ no_suffix_fixed) 0

{- We cache, in the history record, the last epoch in the history and
   the number of entries in the history.  This means we can do a quick
   out in historyPrefixOf in many useful cases. -}
data History = History (Topped EpochNr) Int [HistoryEntry] deriving (Show, Eq, Read)

{- Either id, for valid histories, or undefined for invalid ones. -}
sanityCheckHistory :: History -> History
sanityCheckHistory hh@(History epoch len h) =
    if len /= length h
    then error $ "History " ++ (show hh) ++ " had bad length (should be " ++ (show $ length h) ++ ")"
    else if last_epoch h /= epoch
         then error $ "History " ++ (show hh) ++ " had bad last epoch (should be " ++ (show $ last_epoch h) ++ ")"
         else hh

last_epoch :: [HistoryEntry] -> Topped EpochNr
last_epoch he = worker $ reverse he
                where worker [] = Finite 0
                      worker ((HistoryRun x):_) = x
                      worker (_:x) = worker x

mkHistory :: [HistoryEntry] -> History
mkHistory h = History (last_epoch h) (length h) h

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
                  ReplayStateFailed _ _ _ e' _ ->
                      return $ deEpoch $ e' - e + 1
                  ReplayStateOkay e' -> return $ deEpoch $ e' - e + 1
         ReplayStateFinished -> return 1
         ReplayStateFailed _ _ _ _ _ -> return 1
doHistoryEntry w (HistorySetThread tid) = setThreadWorker w tid >> return 1
doHistoryEntry w (HistoryRunMemory cntr) =
    runMemoryWorker w cntr >> return cntr

stripSharedPrefix :: History -> History -> ([HistoryEntry], [HistoryEntry])
stripSharedPrefix (History _ _ aa) (History _ _ bb) =
    worker aa bb
    where worker a [] = (a, [])
          worker [] b = ([], b)
          worker aas@(a:as) bbs@(b:bs) =
              if a == b then worker as bs
              else case (a, b) of
                     (HistoryRun an, HistoryRun bn) ->
                         if an < bn
                         then worker as bbs
                         else worker aas bs
                     (HistoryRunMemory acntr, HistoryRunMemory bcntr) ->
                         if acntr < bcntr
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
        worker a b
        where
          worker aas bbs =
              {-# SCC "historyPrefixOfWorker" #-}
              case (aas, bbs) of
                ([], _) -> True
                (_, []) -> False
                (aa:as, bb:bs) ->
                    if aa == bb then worker as bs
                    else case (aa, bb) of
                           (HistoryRun acntr, HistoryRun bcntr) ->
                               if acntr <= bcntr
                               then worker as bbs
                               else False
                           (HistoryRunMemory acntr, HistoryRunMemory bcntr) ->
                               if acntr <= bcntr
                               then worker as bbs
                               else False
                           _ -> False

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
                            worker xs (cost + cost') (appendHistory so_far x)
      _ -> error $ (show current) ++ " is not a prefix of " ++ (show desired) ++ " (historyPrefixOf " ++ (show $ historyPrefixOf current desired) ++ ")"

appendHistory :: History -> HistoryEntry -> History
appendHistory (History _ _ []) he = mkHistory [he]
appendHistory (History old_last_epoch old_nr_records h) he =
    let revh = reverse h
        lastThread [] = Just 1
        lastThread ((HistoryRun _):_) = Nothing
        lastThread ((HistoryRunMemory _):x) = lastThread x
        lastThread ((HistorySetThread x):_) = Just x
        (hl:hrest) = revh
        (new_last_epoch, new_nr_records, h') =
            case (hl, he) of
               (HistoryRun x, HistoryRun y) ->
                   if x == y
                   then (old_last_epoch, old_nr_records, h)
                   else if x < y
                        then (y, old_nr_records, reverse $ (HistoryRun y):hrest)
                        else error "appendHistory tried to go backwards in time!"
               (HistoryRunMemory xcntr, HistoryRunMemory ycntr) ->
                   (old_last_epoch, old_nr_records,
                                  if xcntr == ycntr
                                  then h
                                  else if xcntr < ycntr
                                       then reverse $ (HistoryRunMemory ycntr):hrest
                                       else error "appendHistory tried to undo memory accesses")
               (HistorySetThread _, HistorySetThread lt) ->
                   if Just lt == lastThread hrest
                   then (old_last_epoch, old_nr_records - 1, reverse hrest)
                   else (old_last_epoch, old_nr_records, reverse $ he:hrest)
               (_, HistorySetThread lt) ->
                   if Just lt == lastThread revh
                   then (old_last_epoch, old_nr_records, h)
                   else (old_last_epoch, old_nr_records + 1, reverse $ he:revh)
               (_, HistoryRun y) ->
                   (y, old_nr_records + 1, reverse $ he:revh)
               _ -> (old_last_epoch, old_nr_records + 1, reverse $ he:revh)
        res = History new_last_epoch new_nr_records h'
    in sanityCheckHistory res

{- Truncate a history so that it only runs to a particular epoch number -}
truncateHistory :: History -> Topped EpochNr -> History
truncateHistory (History _ _ hs) cntr =
    mkHistory (worker hs)
    where worker [HistoryRun Infinity] = [HistoryRun cntr]
          worker ((HistoryRun c):hs') =
              if c < cntr then (HistoryRun c):(worker hs')
              else [HistoryRun cntr]
          worker (h:hs') = h:(worker hs')
          worker _ = error $ "truncate bad history " ++ (show hs)


instance Forcable HistoryEntry where
    force (HistoryRun t) = force t
    force (HistorySetThread t) = force t
    force (HistoryRunMemory i) = force i

instance Forcable History where
    force (History a b h) = force a . force b . force h
