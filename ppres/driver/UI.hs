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
import UIValue()

data UIExpression = UIDummyFunction
                  | UIExit
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

data UIAssignment = UIAssignment VariableName UIExpression
                  | UIFunction UIExpression

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
               liftM (const UIExit) $ keyword "exit",
               liftM (const UIExit) $ keyword "quit",
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
               oneExprArgParser "second" UIFirst,
               do ident <- P.identifier command_lexer
                  return $ UIVarName ident
            ]

assignmentParser :: Parser UIAssignment
assignmentParser =
    tchoice [do var <- P.identifier command_lexer
                P.reservedOp command_lexer "="
                rhs <- expressionParser
                return $ UIAssignment var rhs,
             do rhs <- expressionParser
                return $ UIFunction rhs ]

getCommand :: IO UIAssignment
getCommand =
    do putStr "> "
       hFlush stdout
       l <- getLine
       case parse assignmentParser "" l of
         Left err -> do putStrLn $ "Cannot parse command " ++ l ++ ": " ++ (show err)
                        getCommand
         Right v -> return v

withSnapshot :: UIExpression -> (History -> WorldMonad UIValue) -> WorldMonad UIValue
withSnapshot expr f =
    do s <- evalExpression expr
       case s of
         UIValueSnapshot s' -> f s'
         _ -> do liftIO $ putStrLn $ "Needed a snapshot, got " ++ (show s)
                 return UIValueNull

maybeSnapshotToUIValue :: Maybe History -> UIValue
maybeSnapshotToUIValue Nothing = UIValueNull
maybeSnapshotToUIValue (Just s) = UIValueSnapshot s

evalExpression :: UIExpression -> WorldMonad UIValue
evalExpression f =
    case f of
      UIDummyFunction -> return UIValueNull
      UIExit -> do exitWorld
                   return UIValueNull
      UIVarName name -> do r <- lookupVariable name
                           return $ case r of
                                      Nothing -> UIValueNull
                                      Just x -> x
      UIPair a b ->
          do a' <- evalExpression a
             b' <- evalExpression b
             return $ UIValuePair a' b'
      UIFirst a ->
          do a' <- evalExpression a
             case a' of
               UIValuePair a'' _ -> return a''
               _ -> return UIValueNull
      UISecond a ->
          do a' <- evalExpression a
             case a' of
               UIValuePair _ a'' -> return a''
               _ -> return UIValueNull
      UIDir ->
          do ws <- get
             liftIO $ mapM_ (putStrLn . fst) $ ws_bindings ws
             return UIValueNull
      UIRun name cntr ->
          withSnapshot name $ \s ->
              return $ maybeSnapshotToUIValue $ run s cntr
      UITrace name cntr ->
          withSnapshot name $ \s ->
              return $ maybeSnapshotToUIValue $ trace s cntr
      UITraceThread name thr ->
          withSnapshot name $ \s ->
              return $ maybeSnapshotToUIValue $ traceThread s thr
      UITraceAddress name addr ->
          withSnapshot name $ \s ->
              return $ maybeSnapshotToUIValue $ traceAddress s addr
      UIRunMemory name tid cntr ->
          withSnapshot name $ \s ->
              return $ maybeSnapshotToUIValue $ runMemory s tid cntr
      UIThreadState name ->
          withSnapshot name $ \s ->
              return $ case threadState s of
                         Nothing -> UIValueNull
                         Just s' -> UIValueString s'

runAssignment :: UIAssignment -> WorldMonad ()
runAssignment as =
    case as of
      UIAssignment var rhs ->
          do res <- evalExpression rhs
             doAssignment var res
      UIFunction f ->
          do res <- evalExpression f
             doAssignment "last" res
             liftIO $ print res

commandLoop :: WorldMonad ()
commandLoop =
    do cmd <- liftIO $ getCommand
       runAssignment cmd
       commandLoop

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> error "need the file descriptor to communicate on"
            (_:_:_) -> error "Too many arguments"
            [fdString] -> do initState <- initialWorldState $ read fdString
                             evalStateT commandLoop initState
