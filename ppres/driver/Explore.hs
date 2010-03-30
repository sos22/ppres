module Explore(enumerateHistories, findSomeHistory,
               findNeighbouringHistories) where

import Numeric
import Data.Word

import History
import Types
import Timing
import Util

import qualified Debug.Trace

dt :: String -> a -> a
dt = Debug.Trace.trace

live_threads :: History -> [ThreadId]
live_threads hist =
    [a | (a, b) <- threadState hist, not (ts_dead b)]

rescheduleOnEveryAccess :: Bool
rescheduleOnEveryAccess = False

findNeighbouringHistories :: History -> [History]
findNeighbouringHistories start =
    let threads = live_threads start
        nThread = nextThread start
        threads' = nThread:(filter ((/=) nThread) threads)
    in case (replayState start, threads) of
         (ReplayStateFailed _ _ _ _, _) -> []
         (ReplayStateFinished _, _) -> tlog ("success " ++ (show start)) []
         (_, []) -> [] {- No runnable threads -> we are dead. -}
         (ReplayStateOkay now, [t]) ->
             {- Only one runnable thread -> run it until it
                generates some event which might cause other threads
                to become runnable.  That pretty much means a system
                call. -}
             let giveUpCoord = Finite $ now + 1000
                 (trc, nextEvent) = deError $ traceToEvent start t giveUpCoord
                 syscalls = filter isSyscall trc
                            where isSyscall x = case trc_trc x of
                                                  TraceSyscall _ -> True
                                                  _ -> False
                 syscallLocs = map trc_loc syscalls
                 runToCoord = Finite $ case syscallLocs of
                                         [] -> 1 + (rs_access_nr $ replayState nextEvent)
                                         (x:_) -> x + 1
             in dt ("run single-threaded to " ++ (show runToCoord) ++ " " ++ (show syscallLocs))
                    [deError $ runThread start t runToCoord]

         (ReplayStateOkay now, _) ->

             {- We have several threads to choose from.  The simplest
                approach would be to pick a thread arbitrarily and run
                it for a single access.  That's obviously very
                inefficient, because most accesses are uninteresting.
                We therefore take, for each thread, a memory trace up
                to its next system call, and look for any races
                between threads in those traces.  We can then advance
                each thread to either its first race, if it has one,
                or its next system call. -}
             {- Why stop at system calls?  Answer: because they're
                totally ordered by the log, and so any race which
                crosses a syscall boundary is by definition not
                interesting. -}
             let trace_for_thread horizon t =
                     let (postTraceHist, collectedTrace) =
                             deError $ do (trc, e) <- traceToEvent start t (Finite horizon)
                                          return (e, trc)
                         (haveSyscall, stoppedTrace) = stop_at_syscall collectedTrace
                         filteredTrace = filter (isInteresting . trc_trc) stoppedTrace
                         isInteresting (TraceFootstep _ _ _ _) = False
                         isInteresting _ = True
                         stop_at_syscall [] = tlog "trace didn't stop" (False, [])
                         stop_at_syscall (x:xs) =
                             if should_stop_here $ trc_trc x
                             then (True, [x])
                             else let (s, r) = stop_at_syscall xs
                                  in (s, x:r)
                         should_stop_here (TraceSyscall _) = tlog "trace stopped for system call" True
                         should_stop_here (TraceCalling _) = tlog "trace stopped for calling event" True
                         should_stop_here (TraceCalled _) = tlog "trace stopped for called event" True
                         should_stop_here (TraceSignal _ _ _ _) = tlog "trace stopped for signal event" True
                         should_stop_here TraceRdtsc = tlog "trace stopped for rdtsc event" True
                         should_stop_here (TraceLoad _ _ _ _ _) = rescheduleOnEveryAccess
                         should_stop_here (TraceStore _ _ _ _ _) = rescheduleOnEveryAccess
                         should_stop_here _ = False
                     in case replayState postTraceHist of
                          ReplayStateFailed _ _ _ _ -> (True, filteredTrace)
                          ReplayStateFinished _ -> (True, filteredTrace)
                          ReplayStateOkay _ -> (haveSyscall, filteredTrace)
                 thread_traces horizon = [(t, trace_for_thread horizon t) | t <- threads']
                 thread_targets horizon =
                     let traces = thread_traces horizon
                         tt x = (maybe (error "1") id) $ lookup x traces
                         thread_events t = filter (isTargetEvent . trc_trc) $ snd $ tt t
                                           where 
                                                 isTargetEvent (TraceLoad _ _ p _ rip) =
                                                     rescheduleOnEveryAccess || existsStoreNotInThread t p rip
                                                 isTargetEvent (TraceStore _ _ p _ rip) =
                                                     rescheduleOnEveryAccess || existsAccessNotInThread t p rip
                                                 isTargetEvent _ = tlog "resched on non-race" True
                         racemsg :: ThreadId -> Word64 -> ThreadId -> Word64 -> Word64 -> a -> a
                         racemsg tid1 rip1 tid2 rip2 ptr = tlog $ "race between " ++ (show tid1) ++ ":" ++
                                                           (showHex rip1 $
                                                            " and " ++ (show tid2) ++ ":" ++
                                                            (showHex rip2 $ "on " ++ (showHex ptr "")))
                                                                                                               
                         {- True if any thread other than t accesses ptr -}
                         existsAccessNotInThread t ptr rip =
                             or [case trc_trc evt of
                                   TraceLoad _ _ ptr' _ rip' | ptr == ptr' -> racemsg t rip (trc_tid evt) rip' ptr True
                                   TraceStore _ _ ptr' _ rip' | ptr == ptr' -> racemsg t rip (trc_tid evt) rip' ptr True
                                   _ -> False
                                 | other_t <- threads', other_t /= t, evt <- snd $ tt other_t]
                         {- True if any thread other than t stores to ptr -}
                         existsStoreNotInThread t ptr rip =
                             or [case trc_trc evt of
                                   TraceStore _ _ ptr' _ rip' | ptr == ptr' -> racemsg t rip (trc_tid evt) rip' ptr True
                                   _ -> False
                                 | other_t <- threads', other_t /= t, evt <- snd $ tt other_t]
                         thread_event t = case thread_events t of
                                            [] -> Nothing
                                            (x:_) -> Just $ trc_loc x + 1
                     in [(t, (fst $ tt t, thread_event t)) | t <- threads']
                 real_targets :: AccessNr -> [(ThreadId, AccessNr)]
                 real_targets h =
                     let tts = thread_targets h
                         {- We need to advance the horizon if there's
                            some thread which hasn't failed and which
                            doesn't yet have a target -}
                         advance_horizon = or [case tt of 
                                                 (False, Nothing) -> True
                                                 _ -> False
                                                 | (_, tt) <- tts]
                     in if advance_horizon
                        then real_targets $ h + 1000
                        else concatMap (\x -> case x of
                                                (t, (_, Just i)) -> [(t,i)]
                                                (_, (_, Nothing)) -> []) tts
                 targets :: [(ThreadId, AccessNr)]
                 targets = real_targets (now + 1000)
                           -- [(t, ReplayCoord $ now + 1) | t <- threads']
             in
               [deError $ runThread start tid $ Finite targ
                | (tid, targ) <- targets]

data ExploreState a = ExploreState { es_white :: [a],
                                     es_grey :: [a] }

pickNextItem :: Show a => ExploreState a -> Maybe (a, ExploreState a)
pickNextItem state = case es_grey state of
                       [] -> Nothing
                       (a:as) -> tlog ("explore " ++ (show a)) $ Just (a, state { es_grey = as, es_white = a:(es_white state) })

discoverItem :: Eq a => a -> ExploreState a -> ExploreState a
discoverItem item state =
    if item `elem` (es_white state) || item `elem` (es_grey state)
    then state
    else state { es_grey = item:(es_grey state)}

exhaustiveExplore :: (Eq a, Show a) => a -> (a -> [a]) -> [a]
exhaustiveExplore start advance =
    let startState = ExploreState [] [start]
        exploreState state =
            case pickNextItem state of
              Nothing -> state
              Just (n_item, n_state) ->
                  let new_greys = advance n_item
                      next_state = foldr discoverItem n_state new_greys
                  in exploreState next_state
    in es_white $ exploreState startState

exploreTo :: (Eq a, Show a) => a -> (a -> [a]) -> (a -> Bool) -> Maybe a
exploreTo start advance prd =
    let startState = ExploreState [] [start]
        exploreState state =
            case pickNextItem state of
              Nothing -> Nothing
              Just (n_item, n_state) ->
                  let new_greys = advance n_item
                      next_state = foldr discoverItem n_state new_greys
                  in if prd n_item
                     then Just n_item
                     else exploreState next_state
    in exploreState startState

enumerateHistories :: History -> [History]
enumerateHistories start = exhaustiveExplore start findNeighbouringHistories

findSomeHistory :: History -> Maybe History
findSomeHistory start =
    exploreTo start findNeighbouringHistories succeeds
    where succeeds x = case replayState x of
                         ReplayStateFinished _ -> True
                         _ -> False

