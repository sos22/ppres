module Main(main) where

import System.Environment
import System.Exit
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import IO
import Data.Word
import Control.Monad

import Types
import Worker
import WorldState
import UIValue

data UICommand = UIExit
               | UIWhereAmI
               | UIRun Integer
               | UIActivateSnapshot VariableName
               | UITrace Integer
               | UITraceThread ThreadId
               | UITraceAddress Word64
               | UIRunMemory ThreadId Integer
                 deriving Show

data UIFunction = UIDummyFunction
                | UISnapshot

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
         "activate" -> liftM UIActivateSnapshot (P.identifier command_lexer)
         "run" -> liftM UIRun (P.integer command_lexer)
         "trace" -> liftM UITrace (P.integer command_lexer)
         "tracet" -> liftM UITraceThread thread_id_parser
         "tracem" -> do addr <- P.integer command_lexer
                        return $ UITraceAddress $ fromInteger addr
         "runm" -> do t <- thread_id_parser
                      n <- P.integer command_lexer
                      return $ UIRunMemory t n
         _ -> unexpected ("keyword " ++ w)

keyword :: String -> Parser String
keyword x = do v <- P.identifier command_lexer
               if v == x then return v
                else unexpected (v ++ ", wanted " ++ x)

functionParser :: Parser UIFunction
functionParser =
    let chooseKeyword ks =
            choice $
            map Text.Parsec.try [liftM (const cons) $ keyword key |
                                 (cons, key) <- ks]
    in chooseKeyword [(UIDummyFunction, "dummy"),
                      (UISnapshot, "snapshot")]

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

runCommand :: UICommand -> WorldState -> IO WorldState
runCommand UIExit ws =
    sequence_ [mapM_ (uiv_destruct . snd) $ ws_bindings ws,
               exitWith ExitSuccess] >> return ws
runCommand (UIActivateSnapshot sid) ws =
    case lookupVariable sid ws of
      Nothing -> do putStrLn ("Cannot find snapshot " ++ (show sid))
                    return ws
      Just (UIValueSnapshot s) ->
          return $ ws { ws_worker = s } 
      _ -> do putStrLn "Not a snapshot"
              return ws
runCommand (UIRun cntr) ws =
    withWorker ws $ \w -> do runWorker w cntr
                             return ws
runCommand (UITrace cntr) ws =
    withWorker ws $ \w -> do traceWorker w cntr
                             return ws
runCommand (UITraceThread ident) ws =
    withWorker ws $ \w -> do traceThreadWorker w ident
                             return ws
runCommand (UITraceAddress addr) ws =
    withWorker ws $ \w -> do traceAddressWorker w addr
                             return ws
runCommand (UIRunMemory tid cntr) ws =
    withWorker ws $ \w -> do runMemoryWorker w tid cntr
                             return ws

runFunction :: UIFunction -> WorldState -> IO (WorldState, UIValue)
runFunction f ws =
    case f of
      UIDummyFunction -> return (ws, UIValueNull)
      UISnapshot ->
          do s <- takeSnapshot $ ws_worker ws
             case s of
               Nothing ->
                   do putStrLn "cannot take snapshot"
                      return (ws, UIValueNull)
               Just s' ->
                   return (ws, UIValueSnapshot s')

runAssignment :: UIAssignment -> WorldState -> IO WorldState
runAssignment as ws =
    case as of
      UICommand cmd -> runCommand cmd ws
      UIAssignment var rhs ->
          do (ws', res) <- runFunction rhs ws
             doAssignment ws' var res
      UIFunction f ->
          do (ws', res) <- runFunction f ws
             doAssignment ws' "last" res
      UIRename dest src ->
          doRename ws dest src

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
