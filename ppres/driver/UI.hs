{-# LANGUAGE RelaxedPolyRec, ScopedTypeVariables #-}
module Main(main) where

import System.Environment
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import IO
import Data.Word
import Control.Monad.State

import Types
import WorldState
import WorkerCache
import UIValue
import Analysis
import History

data UIExpression = UIDummyFunction
                  | UIRun UIExpression (Topped EpochNr)
                  | UITrace UIExpression (Topped EpochNr)
                  | UITraceAddress UIExpression Word64
                  | UIRunMemory UIExpression Integer
                  | UISetThread UIExpression ThreadId
                  | UIDir
                  | UIVarName VariableName
                  | UIPair UIExpression UIExpression
                  | UIFirst UIExpression
                  | UISecond UIExpression
                  | UIThreadState UIExpression
                  | UIRemoveFootsteps UIExpression
                  | UIFindRacingAccesses UIExpression UIExpression
                  | UIReplayState UIExpression
                  | UIControlTrace UIExpression (Topped Integer)
                  | UIFindControlRaces UIExpression UIExpression
                  | UIFixHist UIExpression
                  | UIFixHist2 UIExpression
                  | UIAdvHist UIExpression
                  | UITruncHist UIExpression (Topped EpochNr)
                  | UIFetchMemory UIExpression Word64 Word64
                  | UIFindCritPairs UIExpression
                  | UIFlipPair UIExpression UIExpression
                  | UIIndex UIExpression Int
                  | UIVGIntermediate UIExpression Word64
                  | UIEnum UIExpression
                  | UILiteral UIValue
                  | UIHistDiff UIExpression UIExpression
                  | UIHistFixup UIExpression UIExpression
                    deriving Show

data UIAssignment = UIAssignment VariableName UIExpression
                  | UIFunction UIExpression
                  | UILoad VariableName String
                  | UISave UIExpression String
                  | UIExit deriving Show

command_lexer :: P.TokenParser ()
command_lexer = P.makeTokenParser haskellDef

keyword :: String -> Parser String
keyword x = do v <- P.identifier command_lexer
               if v == x then return v
                else unexpected (v ++ ", wanted " ++ x)

{- try-choice.  Arbitrary choice with arbitrary lookahead. -}
tchoice :: [Parser a] -> Parser a
tchoice = choice . (map Text.Parsec.try)

expressionParser :: Parser UIExpression
expressionParser =
    let oneExprArgParser name constructor =
            do keyword name
               liftM constructor $ expressionParser
        twoExprArgParser name constructor =
            do keyword name
               a <- expressionParser
               b <- expressionParser
               return $ constructor a b
        topped_int = option Infinity (liftM Finite $ P.integer command_lexer)
        topped_en = liftM (fmap EpochNr) topped_int
        parseTopped e = tchoice [keyword "inf" >> return Infinity, liftM Finite e]
        parseEpochNr = keyword "EpochNr" >> liftM EpochNr parseInteger
        parseThreadId = parseInteger
        parseInteger = P.integer command_lexer
        parseHistoryEntry = tchoice [do keyword "HistoryRun"
                                        liftM HistoryRun $ parseTopped parseEpochNr,
                                     do keyword "HistoryRunMemory"
                                        i <- parseInteger
                                        return $ HistoryRunMemory i,
                                     do keyword "HistorySetThread"
                                        tid <- parseThreadId
                                        return $ HistorySetThread tid]
    in
      tchoice [liftM (const UIDummyFunction) $ keyword "dummy",
               liftM (const UIDir) $ keyword "dir",
               oneExprArgParser "thread_state" UIThreadState,
               do keyword "run"
                  snap <- expressionParser
                  cntr <- topped_en
                  return $ UIRun snap cntr,
               do keyword "trace"
                  snap <- expressionParser
                  cntr <- topped_en
                  return $ UITrace snap cntr,
               do keyword "control_trace"
                  snap <- expressionParser
                  cntr <- topped_int
                  return $ UIControlTrace snap cntr,
               do keyword "tracem"
                  snap <- expressionParser
                  addr <- parseInteger
                  return $ UITraceAddress snap $ fromInteger addr,
               do keyword "setthread"
                  snap <- expressionParser
                  tid <- parseThreadId
                  return $ UISetThread snap tid,
               do keyword "runm"
                  snap <- expressionParser
                  n <- parseInteger
                  return $ UIRunMemory snap n,
               do keyword "trunc"
                  hist <- expressionParser
                  n <- topped_en
                  return $ UITruncHist hist n,
               do keyword "index"
                  hist <- expressionParser
                  n <- parseInteger
                  return $ UIIndex hist (fromInteger n),
               do keyword "fetchmem"
                  hist <- expressionParser
                  addr <- parseInteger
                  size <- parseInteger
                  return $ UIFetchMemory hist (fromInteger addr) (fromInteger size),
               do keyword "vginter"
                  hist <- expressionParser
                  addr <- parseInteger
                  return $ UIVGIntermediate hist (fromInteger addr),
               do keyword "History"
                  e <- between (P.reservedOp command_lexer "[") (P.reservedOp command_lexer "]") $ parseHistoryEntry `sepBy` (P.reservedOp command_lexer ",")
                  return $ UILiteral $ UIValueSnapshot $ mkHistory e,
               twoExprArgParser "pair" UIPair,
               twoExprArgParser "findraces" UIFindRacingAccesses,
               twoExprArgParser "findcontrolraces" UIFindControlRaces,
               twoExprArgParser "flippair" UIFlipPair,
               twoExprArgParser "histdiff" UIHistDiff,
               twoExprArgParser "histfixup" UIHistFixup,
               oneExprArgParser "first" UIFirst,
               oneExprArgParser "second" UISecond,
               oneExprArgParser "defootstep" UIRemoveFootsteps,
               oneExprArgParser "replay_state" UIReplayState,
               oneExprArgParser "fixhist" UIFixHist,
               oneExprArgParser "advhist" UIAdvHist,
               oneExprArgParser "fixhist2" UIFixHist2,
               oneExprArgParser "findcritpairs" UIFindCritPairs,
               oneExprArgParser "enum" UIEnum,
               do ident <- P.identifier command_lexer
                  return $ UIVarName ident
            ]

assignmentParser :: Parser UIAssignment
assignmentParser =
    tchoice [do var <- P.identifier command_lexer
                P.reservedOp command_lexer "="
                rhs <- expressionParser
                eof
                return $ UIAssignment var rhs,
             do keyword "exit"
                eof
                return UIExit,
             do keyword "quit"
                eof
                return UIExit,
             do keyword "load"
                var <- P.identifier command_lexer
                fname <- P.stringLiteral command_lexer
                return $ UILoad var fname,
             do keyword "save"
                lhs <- expressionParser
                fname <- P.stringLiteral command_lexer
                return $ UISave lhs fname,
             do rhs <- expressionParser
                eof
                return $ UIFunction rhs
            ]

getCommand :: IO UIAssignment
getCommand =
    do putStr "> "
       hFlush stdout
       l <- getLine
       case parse assignmentParser "" l of
         Left err -> do putStrLn $ "Cannot parse command " ++ l ++ ": " ++ (show err)
                        getCommand
         Right v -> return v

withSnapshot :: AvailInUI a => WorldState -> UIExpression -> (History -> a) -> UIValue
withSnapshot ws expr f =
    case evalExpression ws expr of
      UIValueSnapshot s' -> toUI $ f s'
      s -> UIValueError $ "Needed a snapshot, got " ++ (show s)

evalExpression :: WorldState -> UIExpression -> UIValue
evalExpression ws f =
    case f of
      UIDummyFunction -> UIValueNull
      UIVarName name -> lookupVariable ws name
      UIPair a b ->
          let a' = evalExpression ws a
              b' = evalExpression ws b
          in UIValuePair a' b'
      UIFirst a ->
          case evalExpression ws a of
            UIValuePair a'' _ -> a''
            _ -> UIValueError "needed a pair for first"
      UISecond a ->
          case evalExpression ws a of
            UIValuePair _ a'' -> a''
            _ -> UIValueError "needed a pair for second"
      UIFixHist a -> withSnapshot ws a $ \s -> fixControlHistory s
      UIAdvHist a -> withSnapshot ws a $ \s -> advanceHist s
      UIFixHist2 a -> withSnapshot ws a $ \s -> fixControlHistory' s
      UITruncHist hist n ->
          withSnapshot ws hist $ \s -> truncateHistory s n
      UIDir ->
          uiValueString $ foldr (\a b -> a ++ "\n" ++ b) "" $ map fst $ ws_bindings ws
      UIRun name cntr ->
          withSnapshot ws name $ \s -> run s cntr
      UITrace name cntr ->
          withSnapshot ws name $ \s -> trace s cntr
      UITraceAddress name addr ->
          withSnapshot ws name $ \s -> traceAddress s addr
      UIRunMemory name cntr ->
          withSnapshot ws name $ \s -> runMemory s cntr
      UIThreadState name ->
          withSnapshot ws name $ \s -> threadState s
      UISetThread snap tid ->
          withSnapshot ws snap $ \s -> setThread s tid
      UIReplayState name -> withSnapshot ws name $ \s -> replayState s
      UIControlTrace name cntr -> withSnapshot ws name $ \s -> controlTrace s cntr
      UIFindRacingAccesses a b ->
          toUI $ do a' <- fromUI $ evalExpression ws a
                    b' <- fromUI $ evalExpression ws b
                    return $ findRacingAccesses a' b'
      UIFlipPair a b ->
          toUI $ do a' <- fromUI $ evalExpression ws a
                    b' <- fromUI $ evalExpression ws b
                    return $ flipPair a' b'
      UIFindControlRaces a b ->
          toUI $ do a' <- fromUI $ evalExpression ws a
                    b' <- fromUI $ evalExpression ws b
                    return $ findControlFlowRaces a' b'
      UIHistDiff a b ->
          toUI $ do a' <- fromUI $ evalExpression ws a
                    b' <- fromUI $ evalExpression ws b
                    return $ historyDiff a' b'
      UIHistFixup a b ->
          toUI $ do a' <- fromUI $ evalExpression ws a
                    b' <- fromUI $ evalExpression ws b
                    return $ applyHistoryDiff a' b'
      UIRemoveFootsteps e ->
          toUI $ do es <- fromUI $ evalExpression ws e
                    let isFootstep (TraceRecord (TraceFootstep _ _ _ _) _) = True
                        isFootstep _ = False
                    return [trc | trc <- es, not $ isFootstep trc ]
      UIFetchMemory hist addr size ->
          withSnapshot ws hist $ \s -> fetchMemory s addr size
      UIVGIntermediate hist addr ->
          withSnapshot ws hist $ \s -> vgIntermediate s addr
      UIFindCritPairs hist ->
          withSnapshot ws hist findCritPairs
      UIIndex lst idx ->
          case evalExpression ws lst of
            UIValueList lst' ->
                if idx >= length lst'
                then UIValueError $ "index " ++ (show idx) ++ " greater than length of list " ++ (show $ length lst')
                else lst'!!idx
            e -> UIValueError $ "wanted a list to index, got a " ++(show e)
      UIEnum start ->
          mapUIValue enumerateHistories $ UIValueList [evalExpression ws start]
      UILiteral x -> x

runAssignment :: UIAssignment -> WorldState -> IO WorldState
runAssignment as ws =
    case as of
      UIAssignment var rhs ->
          return $ doAssignment ws var $ evalExpression ws rhs
      UIFunction f ->
          let r = evalExpression ws f
              ws' = doAssignment ws "last" r
          in print r >> return ws'
      UILoad vname fname ->
          let isSpace ' ' = True
              isSpace '\n' = True
              isSpace '\r' = True
              isSpace '\t' = True
              isSpace _ = False
              isAllSpace = and . map isSpace
              safeRead x = case reads x of
                             [(a, y)] | isAllSpace y -> a
                             _ -> UIValueError $ "cannot parse " ++ x
          in liftM (doAssignment ws vname . safeRead) $ readFile fname
      UISave expr fname ->
          writeFile fname (show $ evalExpression ws expr) >> return ws
      UIExit -> exitWorld >> return ws

commandLoop :: WorldState -> IO ()
commandLoop ws =
    do cmd <- getCommand
       ws' <- runAssignment cmd ws
       commandLoop ws'

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> error "need the file descriptor to communicate on"
            (_:_:_) -> error "Too many arguments"
            [fdString] -> do initState <- initialWorldState $ read fdString
                             commandLoop initState
