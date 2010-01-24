{-# LANGUAGE RelaxedPolyRec #-}
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

data UIExpression = UIDummyFunction
                  | UIRun UIExpression Integer
                  | UITrace UIExpression Integer
                  | UITraceThread UIExpression ThreadId
                  | UITraceAddress UIExpression Word64
                  | UIRunMemory UIExpression ThreadId Integer
                  | UIDir
                  | UIVarName VariableName
                  | UIPair UIExpression UIExpression
                  | UIFirst UIExpression
                  | UISecond UIExpression
                  | UIThreadState UIExpression
                  | UIRemoveFootsteps UIExpression
                    deriving Show

data UIAssignment = UIAssignment VariableName UIExpression
                  | UIFunction UIExpression
                  | UIExit deriving Show

command_lexer :: P.TokenParser ()
command_lexer = P.makeTokenParser haskellDef

thread_id_parser :: Parser ThreadId
thread_id_parser = P.integer command_lexer


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
    in
      tchoice [liftM (const UIDummyFunction) $ keyword "dummy",
               liftM (const UIDir) $ keyword "dir",
               oneExprArgParser "thread_state" UIThreadState,
               do keyword "run"
                  snap <- expressionParser
                  cntr <- option (-1) (P.integer command_lexer)
                  return $ UIRun snap cntr,
               do keyword "trace"
                  snap <- expressionParser
                  cntr <- option (-1) (P.integer command_lexer)
                  return $ UITrace snap cntr,
               do keyword "tracet"
                  snap <- expressionParser
                  thr <- thread_id_parser
                  return $ UITraceThread snap thr,
               do keyword "tracem"
                  snap <- expressionParser
                  addr <- P.integer command_lexer
                  return $ UITraceAddress snap $ fromInteger addr,
               do keyword "runm"
                  snap <- expressionParser
                  t <- thread_id_parser
                  n <- P.integer command_lexer
                  return $ UIRunMemory snap t n,
               do keyword "pair"
                  a <- expressionParser
                  b <- expressionParser
                  return $ UIPair a b,
               oneExprArgParser "first" UIFirst,
               oneExprArgParser "second" UISecond,
               oneExprArgParser "defootstep" UIRemoveFootsteps,
               do ident <- P.identifier command_lexer
                  return $ UIVarName ident
            ]

assignmentParser :: Parser UIAssignment
assignmentParser =
    tchoice [do var <- P.identifier command_lexer
                P.reservedOp command_lexer "="
                rhs <- expressionParser
                return $ UIAssignment var rhs,
             do keyword "exit"
                return UIExit,
             do keyword "quit"
                return UIExit,
             do rhs <- expressionParser
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
      UIDir ->
          uiValueString $ foldr (\a b -> a ++ "\n" ++ b) "" $ map fst $ ws_bindings ws
      UIRun name cntr ->
          withSnapshot ws name $ \s -> run s cntr
      UITrace name cntr ->
          withSnapshot ws name $ \s -> trace s cntr
      UITraceThread name thr ->
          withSnapshot ws name $ \s -> traceThread s thr
      UITraceAddress name addr ->
          withSnapshot ws name $ \s -> traceAddress s addr
      UIRunMemory name tid cntr ->
          withSnapshot ws name $ \s -> runMemory s tid cntr
      UIThreadState name ->
          withSnapshot ws name $ \s -> threadState s
      UIRemoveFootsteps e ->
          case fromUI $ evalExpression ws e of
            Just es ->
                let isFootstep (TraceRecord (TraceFootstep _ _ _ _) _) = True
                    isFootstep _ = False
                in toUI [trc | trc <- es, not $ isFootstep trc ]
            Nothing -> UIValueError "Can only remove footsteps from a list of records"
                   
runAssignment :: UIAssignment -> WorldState -> IO WorldState
runAssignment as ws =
    case as of
      UIAssignment var rhs ->
          return $ doAssignment ws var $ evalExpression ws rhs
      UIFunction f ->
          let r = evalExpression ws f
              ws' = doAssignment ws "last" r
          in print r >> return ws'
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
