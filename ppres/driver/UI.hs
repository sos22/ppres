module Main(main) where

import System.Environment
import System.Exit
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import IO
import Data.Word
import Control.Monad.State

import Types
import Worker
import WorldState
import UIValue

data UICommand = UIExit
               | UIWhereAmI
                 deriving Show

data UIFunction = UIDummyFunction
                | UISnapshot VariableName
                | UIRun VariableName Integer
                | UITrace VariableName Integer
                | UITraceThread VariableName ThreadId
                | UITraceAddress VariableName Word64
                | UIRunMemory VariableName ThreadId Integer

data UIAssignment = UICommand UICommand
                  | UIAssignment VariableName UIFunction
                  | UIFunction UIFunction
                  | UIRename VariableName VariableName

command_lexer :: P.TokenParser ()
command_lexer = P.makeTokenParser haskellDef

thread_id_parser :: Parser ThreadId
thread_id_parser = P.integer command_lexer

commandParser :: Parser UICommand
commandParser =
    do w <- P.identifier command_lexer
       case w of
         "exit" -> return UIExit
         "quit" -> return UIExit
         "loc" -> return UIWhereAmI
         "whereami" -> return UIWhereAmI
         _ -> unexpected ("keyword " ++ w)

keyword :: String -> Parser String
keyword x = do v <- P.identifier command_lexer
               if v == x then return v
                else unexpected (v ++ ", wanted " ++ x)

functionParser :: Parser UIFunction
functionParser =
    let tchoice = choice . (map Text.Parsec.try)
    in tchoice [liftM (const UIDummyFunction) $ keyword "dummy",
                do keyword "snapshot"
                   liftM UISnapshot $ P.identifier command_lexer,
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
                          return $ UIRename dest src) <|>
    (do command <- commandParser
        return $ UICommand command)

getCommand :: IO UIAssignment
getCommand =
    do putStr "> "
       hFlush stdout
       l <- getLine
       case parse assignmentParser "" l of
         Left err -> do putStrLn $ "Cannot parse command " ++ l ++ ": " ++ (show err)
                        getCommand
         Right v -> return v

runCommand :: UICommand -> WorldMonad ()
runCommand UIExit =
    do ws <- get
       sequence_ [mapM_ (uiv_destruct . snd) $ ws_bindings ws,
                  liftIO $ exitWith ExitSuccess]

runFunction :: UIFunction -> WorldMonad UIValue
runFunction f =
    case f of
      UIDummyFunction -> return UIValueNull
      UISnapshot vname ->
          do p <- lookupSnapshot vname
             case p of
               Nothing -> do liftIO $ putStrLn "Can't find parent snapshot"
                             return UIValueNull
               Just parent ->
                   do s <- takeSnapshot parent
                      case s of
                        Nothing ->
                            do liftIO $ putStrLn "cannot take snapshot"
                               return UIValueNull
                        Just s' ->
                            return $ UIValueSnapshot s'
      UIRun name cntr ->
          do s <- lookupSnapshot name
             case s of
               Nothing -> liftIO $ putStrLn "Can't find snapshot"
               Just s' -> runWorker s' cntr
             return UIValueNull
      UITrace name cntr ->
          do s <- lookupSnapshot name
             case s of
               Nothing -> liftIO $ putStrLn "Can't find snapshot"
               Just s' -> traceWorker s' cntr
             return UIValueNull
      UITraceThread name thr ->
          do s <- lookupSnapshot name
             case s of
               Nothing -> liftIO $ putStrLn "Can't find snapshot"
               Just s' -> traceThreadWorker s' thr
             return UIValueNull
      UITraceAddress name addr ->
          do s <- lookupSnapshot name
             case s of
               Nothing -> liftIO $ putStrLn "Can't find snapshot"
               Just s' -> traceAddressWorker s' addr
             return UIValueNull
      UIRunMemory name tid cntr ->
          do s <- lookupSnapshot name
             case s of
               Nothing -> liftIO $ putStrLn "Can't find snapshot"
               Just s' -> runMemoryWorker s' tid cntr
             return UIValueNull

runAssignment :: UIAssignment -> WorldMonad ()
runAssignment as =
    case as of
      UICommand cmd -> runCommand cmd
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
