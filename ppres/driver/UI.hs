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

data UIFunction = UIDummyFunction
                | UIExit
                | UIRun VariableName Integer
                | UITrace VariableName Integer
                | UITraceThread VariableName ThreadId
                | UITraceAddress VariableName Word64
                | UIRunMemory VariableName ThreadId Integer
                | UIDir
                | UIPrint VariableName

data UIAssignment = UIAssignment VariableName UIFunction
                  | UIFunction UIFunction
                  | UIRename VariableName VariableName

command_lexer :: P.TokenParser ()
command_lexer = P.makeTokenParser haskellDef

thread_id_parser :: Parser ThreadId
thread_id_parser = P.integer command_lexer


keyword :: String -> Parser String
keyword x = do v <- P.identifier command_lexer
               if v == x then return v
                else unexpected (v ++ ", wanted " ++ x)

functionParser :: Parser UIFunction
functionParser =
    let tchoice = choice . (map Text.Parsec.try)
    in tchoice [liftM (const UIDummyFunction) $ keyword "dummy",
                liftM (const UIExit) $ keyword "exit",
                liftM (const UIExit) $ keyword "quit",
                liftM (const UIDir) $ keyword "dir",
                do keyword "print"
                   var <- P.identifier command_lexer
                   return $ UIPrint var,
                do keyword "run"
                   snap <- P.identifier command_lexer
                   cntr <- option (-1) (P.integer command_lexer)
                   return $ UIRun snap cntr,
                do keyword "trace"
                   snap <- P.identifier command_lexer
                   cntr <- option (-1) (P.integer command_lexer)
                   return $ UITrace snap cntr,
                do keyword "tracet"
                   snap <- P.identifier command_lexer
                   thr <- thread_id_parser
                   return $ UITraceThread snap thr,
                do keyword "tracem"
                   snap <- P.identifier command_lexer
                   addr <- P.integer command_lexer
                   return $ UITraceAddress snap $ fromInteger addr,
                do keyword "runm"
                   snap <- P.identifier command_lexer
                   t <- thread_id_parser
                   n <- P.integer command_lexer
                   return $ UIRunMemory snap t n
               ]

assignmentParser :: Parser UIAssignment
assignmentParser =
    (Text.Parsec.try $ do var <- P.identifier command_lexer
                          P.reservedOp command_lexer "="
                          rhs <- functionParser
                          return $ UIAssignment var rhs) <|>
    (Text.Parsec.try $ do rhs <- functionParser
                          return $ UIFunction rhs) <|>
    (Text.Parsec.try $ do dest <- P.identifier command_lexer
                          P.reservedOp command_lexer "<-"
                          src <- P.identifier command_lexer
                          return $ UIRename dest src)

getCommand :: IO UIAssignment
getCommand =
    do putStr "> "
       hFlush stdout
       l <- getLine
       case parse assignmentParser "" l of
         Left err -> do putStrLn $ "Cannot parse command " ++ l ++ ": " ++ (show err)
                        getCommand
         Right v -> return v

withSnapshot :: VariableName -> (History -> WorldMonad UIValue) -> WorldMonad UIValue
withSnapshot name f =
    do s <- lookupSnapshot name
       case s of
         Nothing -> do liftIO $ putStrLn $ "Can't find snapshot " ++ name
                       return UIValueNull
         Just s' -> f s'

maybeSnapshotToUIValue :: Maybe History -> UIValue
maybeSnapshotToUIValue Nothing = UIValueNull
maybeSnapshotToUIValue (Just s) = UIValueSnapshot s

runFunction :: UIFunction -> WorldMonad UIValue
runFunction f =
    case f of
      UIDummyFunction -> return UIValueNull
      UIExit -> do exitWorld
                   return UIValueNull
      UIDir ->
          do ws <- get
             liftIO $ mapM_ (print . fst) $ ws_bindings ws
             return UIValueNull
      UIPrint var ->
          do r <- lookupVariable var
             liftIO $ case r of
                        Nothing -> putStrLn $ "no variable " ++ var
                        Just v -> print v
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

runAssignment :: UIAssignment -> WorldMonad ()
runAssignment as =
    case as of
      UIAssignment var rhs ->
          do res <- runFunction rhs
             doAssignment var res
      UIFunction f ->
          do res <- runFunction f
             doAssignment "last" res
      UIRename dest src ->
          doRename dest src

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
