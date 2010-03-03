{-# LANGUAGE RelaxedPolyRec, ScopedTypeVariables #-}
module Main(main) where

import System.Environment
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import IO
import Control.Monad.State
import Data.IORef
import Foreign.C.Types
import System.Exit

import Socket
import Types
import WorkerCache
import UIValue
import Analysis
import History

data WorldState = WorldState { ws_bindings :: [(VariableName, UIValue)] }

data UIExpression = UIDummyFunction
                  | UIDir
                  | UIVarName VariableName
                  | UITruncHist UIExpression (Topped AccessNr)
                  | UILiteral UIValue
                  | UIFunApp UIExpression UIExpression
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
                else unexpected v

{- try-choice.  Arbitrary choice with arbitrary lookahead. -}
tchoice :: [Parser a] -> Parser a
tchoice = choice . (map Text.Parsec.try)

trivParsec :: Read a => Parser a
trivParsec = do inp <- getInput
                case reads inp of
                  [] -> fail "no parse"
                  [(x,rest)] -> do setInput rest
                                   return x
                  _ -> fail "ambiguous parse"
                    
expressionParser :: Parser UIExpression
expressionParser =
    let 
        parseTopped e = tchoice [keyword "inf" >> return Infinity, liftM Finite e]
        parseAccessNr = keyword "AccessNr" >> parseInteger
        parseReplayCoord = liftM AccessNr parseAccessNr
        parseInteger = P.integer command_lexer
    in
      tchoice [liftM (const UIDummyFunction) $ keyword "dummy",
               liftM (const UIDir) $ keyword "dir",
               do keyword "trunc"
                  hist <- expressionParser
                  n <- parseTopped parseReplayCoord
                  return $ UITruncHist hist n,
               do h <- trivParsec
                  return $ UILiteral $ UIValueSnapshot $ h,
               do keyword "f"
                  f <- expressionParser
                  a <- expressionParser
                  return $ UIFunApp f a,
               do char '~'
                  tid <- parseInteger
                  return $ UILiteral $ UIValueThreadId $ ThreadId tid,
               do ident <- P.identifier command_lexer
                  return $ UIVarName ident,
               do v <- parseInteger
                  return $ UILiteral $ UIValueInteger v
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

inUI :: (AvailInUI a, AvailInUI b) => (a -> b) -> UIValue -> UIValue
inUI f x = toUI $ fmap f $ fromUI x

withSnapshot :: (AvailInUI a, AvailInUI b) => WorldState -> UIExpression -> (b -> a) -> UIValue
withSnapshot ws expr f = inUI f $ evalExpression ws expr

evalExpression :: WorldState -> UIExpression -> UIValue
evalExpression ws f =
    case f of
      UIDummyFunction -> UIValueNull
      UIVarName name -> lookupVariable ws name
      UITruncHist hist n ->
          withSnapshot ws hist $ \s -> truncateHistory s n
      UIDir ->
          uiValueString $ foldr (\a b -> a ++ "\n" ++ b) "" $ map fst $ ws_bindings ws
      UILiteral x -> x
      UIFunApp ff a ->
          evalExpression ws ff `uiApply` evalExpression ws a
                    
mkUIFunction :: (AvailInUI a, AvailInUI b) => (a -> b) -> UIValue
mkUIFunction f =
    UIValueFunction $ \a ->
        case fromUI a of
          Left e -> UIValueError e
          Right x -> toUI $ f x

mkUIFunction2 :: (AvailInUI a, AvailInUI b, AvailInUI c) => (a -> (b -> c)) -> UIValue
mkUIFunction2 f =
    UIValueFunction $ \a ->
        case fromUI a of
          Left e -> UIValueError e
          Right a' -> mkUIFunction (f a')

mkUIFunction3 :: (AvailInUI a, AvailInUI b, AvailInUI c, AvailInUI d) => (a -> (b -> (c -> d))) -> UIValue
mkUIFunction3 f =
    UIValueFunction $ \a ->
        case fromUI a of
          Left e -> UIValueError e
          Right a' -> mkUIFunction2 (f a')

defootstep :: [TraceRecord] -> [TraceRecord]
defootstep = filter (not . isFootstep . trc_trc)
             where isFootstep (TraceFootstep _ _ _ _) = True
                   isFootstep _ = False

uiIndex :: [UIValue] -> Int -> UIValue
uiIndex lst idx =
    if idx >= length lst
    then UIValueError $ "index " ++ (show idx) ++ " greater than length of list " ++ (show $ length lst)
    else lst!!idx

initialWorldState :: CInt -> IO WorldState
initialWorldState fd =
    do f <- fdToSocket fd
       a <- newIORef True
       let root_snap = Worker f a
       initWorkerCache root_snap
       return $ WorldState { ws_bindings = [("start", UIValueSnapshot emptyHistory),
                                            ("first", mkUIFunction (fst :: (UIValue, UIValue) -> UIValue)),
                                            ("second", mkUIFunction (snd :: (UIValue, UIValue) -> UIValue)),
                                            ("thread_state", mkUIFunction threadState),
                                            ("regs", mkUIFunction getRegisters),
                                            ("races", mkUIFunction getRacingExpressions),
                                            ("critsections", mkUIFunction criticalSections),
                                            ("defootstep", mkUIFunction defootstep),
                                            ("replay_state", mkUIFunction replayState),
                                            ("enum", mkUIFunction enumerateHistories),
                                            ("fix", mkUIFunction2 mkFixupLibrary),
                                            ("pair", mkUIFunction2 ((,) :: UIValue -> UIValue -> (UIValue, UIValue))),
                                            ("findraces", mkUIFunction2 findRacingAccesses),
                                            ("findcontroltraces", mkUIFunction2 findControlFlowRaces),
                                            ("ct2", mkUIFunction2 controlTraceTo),
                                            ("t2", mkUIFunction2 traceTo),
                                            ("index", mkUIFunction2 uiIndex),
                                            ("vginter", mkUIFunction2 vgIntermediate),
                                            ("fetchmem", mkUIFunction3 fetchMemory),
                                            ("map", mkUIFunction2 (map :: (UIValue->UIValue) -> [UIValue] -> [UIValue])),
                                            ("zip", mkUIFunction2 (zip :: [UIValue] -> [UIValue] -> [(UIValue,UIValue)])),
                                            ("lastcommunication", mkUIFunction3 lastCommunication),
                                            ("abshist", mkUIFunction2 absHistSuffix)
                                           ] }

lookupVariable :: WorldState -> VariableName -> UIValue
lookupVariable ws name =
    case lookup name $ ws_bindings ws of
      Nothing -> UIValueError $ name ++ " not found"
      Just s' -> s'

doAssignment :: WorldState -> VariableName -> UIValue -> WorldState
doAssignment ws name val =
    ws { ws_bindings = (name, val):
         [b | b <- (ws_bindings ws), fst b /= name]}

exitWorld :: IO ()
exitWorld = do destroyWorkerCache
               exitWith ExitSuccess

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
