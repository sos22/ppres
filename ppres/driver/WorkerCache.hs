{- This module is intended to hide all the grubbiness of the interface
   to the C world, and provides a nice functional API to it.  The
   functional API is expressed entirely in terms of Histories, and we
   are responsible for mapping them into Workers as and when
   necessary. -}
module WorkerCache(initWorkerCache, destroyWorkerCache, 
                   threadState, replayState, 
                   fetchMemory, vgIntermediate, nextThread,
                   controlTraceTo, getRegisters,
                   getRipAtAccess, traceTo, traceToEvent) where

import Data.Word
import Control.Monad.State
import Data.IORef
import Data.List

import System.IO.Unsafe

import Types
import History

--import qualified Debug.Trace
dt :: String -> a -> a
dt = const id

{- We use a two level cache.  The first level is primarily for the
   benefit of the automated search process, and has an expiry policy
   like this:

   -- If you search for X, expire everything which isn't a prefix of X.
   -- After that, expire in FIFO order.

   Stuff which expires out of the first level goes to the second
   level, which is maintained LRU.  This level is primarily there to
   avoid pathological behaviour if the user is driving us
   interactively. -}
type WorkerPool = [(History, Worker)]
data WorkerCache = WorkerCache { wc_fifo_cache :: IORef WorkerPool,
                                 wc_lru_cache :: IORef WorkerPool,
                                 wc_start :: Worker }


fifoCacheSize :: Int
fifoCacheSize = 800

lruCacheSize :: Int
lruCacheSize = 100

globalWorkerCache :: IORef (Maybe WorkerCache)
{-# NOINLINE globalWorkerCache #-}
globalWorkerCache =
    unsafePerformIO $ newIORef Nothing

workerCache :: IO WorkerCache
workerCache =
    do wc <- readIORef globalWorkerCache
       case wc of
         Nothing -> error "worker cache not ready"
         Just wc' -> return wc'

mkWorkerPool :: WorkerPool
mkWorkerPool = []

initWorkerCache :: Worker -> IO ()
initWorkerCache start =
    do fifo <- newIORef mkWorkerPool
       lru <- newIORef mkWorkerPool
       writeIORef globalWorkerCache $ Just $ WorkerCache { wc_fifo_cache = fifo,
                                                           wc_lru_cache = lru,
                                                           wc_start = start }

destroyWorkerCache :: IO ()
destroyWorkerCache =
    let killPool :: IORef WorkerPool -> IO ()
        killPool p = readIORef p >>= mapM_ (killWorker . snd)
    in
    do wc <- workerCache
       killPool $ wc_fifo_cache wc
       killPool $ wc_lru_cache wc
       killWorker $ wc_start wc
       writeIORef globalWorkerCache Nothing

getWorker :: History -> IO Worker
getWorker target =

    {- This is a bit skanky.  The problem is that hist might contain
       some thunks which will themselves perform worker cache
       operations, and if we were to force them at exactly the wrong
       time then it's possible that they could modify the cache while
       we have a reference to the old cache state, which would
       potentially cause us to touch dead workers.  We avoid the issue
       completely by just forcing hist before doing anything -}
    force target $

    do wc <- workerCache

       fifo <- readIORef $ wc_fifo_cache wc
       lru <- readIORef $ wc_lru_cache wc

       let {- First, search the FIFO list, expiring as we go. -}
           (best_fifo, new_fifo', expired_fifo) = search_fifo fifo
           search_fifo [] = (Nothing, [], expired_fifo')
           search_fifo ((h,w):rest) =
               let (best_rest, new_fifo_rest, expired_rest) = search_fifo rest
                   isPrefixOfTarget = historyPrefixOf h target
                   new_best =
                       if not isPrefixOfTarget
                       then best_rest
                       else case best_rest of
                              Nothing -> Just (h, w)
                              Just (best_rest_h, _) ->
                                  if best_rest_h `historyPrefixOf` h
                                  then Just (h, w)
                                  else best_rest
                   new_fifo'' = (if isPrefixOfTarget
                                then (:) (h,w)
                                else id) new_fifo_rest
                   new_expired = (if isPrefixOfTarget
                                  then id
                                  else (:) (h, w)) expired_rest
               in (new_best, new_fifo'', new_expired)
           (new_fifo, expired_fifo') = splitAt (fifoCacheSize-1) new_fifo'

           {- Search the current LRU, comparing to both the target and
              the best FIFO.  sorted_lru is the current LRU list
              sorted by goodness, except that if the best history is
              to be found in the LRU we remove it from the list and
              put it in best_lru.  The final result is either new_fifo
              or new_fifo with the best from the LRU at the front. -}
           (best_lru, sorted_lru, new_fifo_augmented) =
               case sortBy goodnessOrdering lru of
                 [] -> (best_fifo, [], new_fifo)
                 xs@(x:xss) ->
                     if historyPrefixOf (fst x) target
                     then case best_fifo of
                            Nothing -> (Just x, xss, x:new_fifo)
                            Just bh ->
                                if historyPrefixOf (fst bh) (fst x)
                                then (Just x, xss, x:new_fifo)
                                else (best_fifo, xs, new_fifo)
                     else (best_fifo, xs, new_fifo)

           {- Build the new LRU.  We do a kind of pull-to-front which
              means that stuff in the LRU which could have been used
              as a basis for the current target ends up ahead of
              things which couldn't have been. -}
           (new_lru, expired_lru) = splitAt lruCacheSize $ sortBy goodnessOrdering $ expired_fifo ++ sorted_lru

           goodnessOrdering (x,_) (y,_) =
               {- Is x a better prefix of target than y?  LT if it is,
                  GT if it isn't, and EQ if they're unordered. -}
               if historyPrefixOf x target
               then if historyPrefixOf y target
                    then if historyPrefixOf x y
                         then LT
                         else GT
                    else LT
               else if historyPrefixOf y target
                    then GT
                    else EQ
           
           (best_hist, best_worker) = case best_lru of
                                        Nothing -> (emptyHistory, wc_start wc)
                                        Just x -> x

           reallySnapshot x = liftM (maybe (error $ "cannot snapshot " ++ (show x)) id) $ takeSnapshot x
       writeIORef (wc_lru_cache wc) new_lru
       writeIORef (wc_fifo_cache wc) new_fifo_augmented

       mapM_ (killWorker . snd) expired_lru
       
       new_worker <- reallySnapshot best_worker
       dt ("found " ++ (show best_hist) ++ " for " ++ (show target)) $ if best_hist == target
        then return new_worker
        else let doFixup currentWorker currentHistory cost_base =
                     do costOrPartial <- fixupWorkerForHist 50 currentWorker currentHistory target
                        case costOrPartial of
                          (cost, Nothing) ->
                              if cost > 10
                              then do modifyIORef (wc_fifo_cache wc) $ (:) (target, currentWorker)
                                      s <- reallySnapshot currentWorker
                                      return (s, cost + cost_base)
                              else return (currentWorker, cost + cost_base)
                          (cost, Just partial) ->
                              dt ("Partial fixup: " ++ (show currentHistory) ++ " -> " ++ (show partial) ++ ", target " ++ (show target)) $
                              do modifyIORef (wc_fifo_cache wc) $ (:) (partial, currentWorker)
                                 newWorker <- reallySnapshot currentWorker
                                 doFixup newWorker partial $ cost_base + cost
             in do (final_worker, cost) <- doFixup new_worker best_hist 0
                   (final_fifo, final_fifo_expired) <- dt ("fixup cost " ++ (show cost)) $ liftM (splitAt fifoCacheSize) $ readIORef $ wc_fifo_cache wc
                   writeIORef (wc_fifo_cache wc) final_fifo
                   almost_final_lru <- readIORef $ wc_lru_cache wc
                   let (final_lru, final_lru_expired) = splitAt lruCacheSize $ sortBy goodnessOrdering $ final_fifo_expired ++ almost_final_lru
                   writeIORef (wc_lru_cache wc) final_lru
                   mapM_ (killWorker . snd) final_lru_expired
                   return final_worker



queryCmd :: (Worker -> IO a) -> History -> a
queryCmd w hist =
    unsafePerformIO $ do worker <- getWorker hist
                         res <- w worker
                         killWorker worker
                         return res

threadState :: History -> [(ThreadId, ThreadState)]
threadState = queryCmd threadStateWorker

replayState :: History -> ReplayState
replayState = queryCmd replayStateWorker

fetchMemory :: History -> Word64 -> Word64 -> Maybe [Word8]
fetchMemory hist addr size =
    queryCmd (\worker -> fetchMemoryWorker worker addr size) hist

vgIntermediate :: History -> Word64 -> Maybe String
vgIntermediate hist addr =
    queryCmd (\worker -> vgIntermediateWorker worker addr) hist

nextThread :: History -> ThreadId
nextThread = queryCmd nextThreadWorker

controlTraceTo :: History -> History -> Either String [Expression]
controlTraceTo start end =
    queryCmd (\worker -> controlTraceToWorker worker start end) start

traceTo :: History -> History -> Either String [TraceRecord]
traceTo start end = 
    queryCmd (\worker -> traceToWorker worker start end) start

getRegisters :: History -> RegisterFile
getRegisters = queryCmd getRegistersWorker

getRipAtAccess :: History -> AccessNr -> Either String Word64
getRipAtAccess hist whn =
    do hist' <- truncateHistory hist $ Finite $ whn + 1
       getRegister (getRegisters hist') REG_RIP

traceToEvent :: History -> ThreadId -> Topped AccessNr -> Either String ([TraceRecord], History)
traceToEvent start tid limit =
    unsafePerformIO $ do worker <- getWorker start
                         trc <- traceToEventWorker worker tid limit
                         rs <- replayStateWorker worker
                         killWorker worker
                         return $ do h <- runThread start tid $ Finite (rs_access_nr rs)
                                     return (trc, h)

