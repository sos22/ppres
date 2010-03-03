{-# LANGUAGE RelaxedPolyRec, ScopedTypeVariables #-}
module Main(main) where

import System.Environment
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Text.Parsec.Error
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

data UIExpression = UIVarName VariableName
                  | UILiteral UIValue
                  | UIFunApp UIExpression UIExpression
                    deriving Show

data UIAssignment = UIAssignment VariableName UIExpression
                  | UIFunction UIExpression
                  | UILoad VariableName String
                  | UISave UIExpression String
                  | UIDir
                  | UIExit
                  | UINoop
                    deriving Show

command_lexer :: P.TokenParser ()
command_lexer = P.makeTokenParser haskellDef

keyword :: String -> Parser String
keyword x = do v <- P.identifier command_lexer
               if v == x then return v
                else unexpected v

{- try-choice.  Arbitrary choice with arbitrary lookahead. -}
tchoice :: [Parser a] -> Parser a
tchoice = choice . (map Text.Parsec.try)

trivParsec :: (Monad m, Read a) => ParsecT [Char] u m a
trivParsec =
    ParsecT { runParsecT =
                  \state ->
                      case reads $ stateInput state of
                        [] -> return $ Empty $ return $ Error $ newErrorMessage (Message "no parse") (statePos state)
                        [(x,rest)] ->
                            return $ Consumed $ return $ Ok x (state {stateInput = rest}) (newErrorUnknown $ statePos state)
                        _ -> fail "ambiguous parse" }

ignSpace :: Parser a -> Parser a
ignSpace x =
    do skipMany space
       r <- x
       skipMany space
       return r

expressionParser :: Parser UIExpression
expressionParser =
    let parseInteger = P.integer command_lexer
    in do atoms <- many $ tchoice [liftM UILiteral (ignSpace trivParsec),
                                   do char '~'
                                      tid <- parseInteger
                                      return $ UILiteral $ UIValueThreadId $ ThreadId tid,
                                   liftM UIVarName $ P.identifier command_lexer,
                                   between (P.reservedOp command_lexer "(") (P.reservedOp command_lexer ")") expressionParser]
          if length atoms == 0
           then fail "Huh? parse empty expression"
           else return $ foldl1 UIFunApp atoms

assignmentParser :: Parser UIAssignment
assignmentParser =
    tchoice [do eof
                return UINoop,
             do var <- P.identifier command_lexer
                P.reservedOp command_lexer "="
                rhs <- expressionParser
                eof
                return $ UIAssignment var rhs,
             do keyword "dir"
                eof
                return UIDir,
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

evalExpression :: WorldState -> UIExpression -> UIValue
evalExpression ws f =
    case f of
      UIVarName name -> lookupVariable ws name
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

uiFilter :: (UIValue -> UIValue) -> [UIValue] -> Either String [UIValue]
uiFilter f items = filterM (fromUI . f) items

isSuccessReplayState :: ReplayState -> Bool
isSuccessReplayState (ReplayStateFinished _) = True
isSuccessReplayState _ = False
isFailureReplayState :: ReplayState -> Bool
isFailureReplayState (ReplayStateFailed _ _ _ _) = True
isFailureReplayState _ = False

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
                                            ("abshist", mkUIFunction2 absHistSuffix),
                                            ("trunc", mkUIFunction2 $ \x y -> truncateHistory x $ Finite y),
                                            ("filter", mkUIFunction2 uiFilter),
                                            ("issuccess", mkUIFunction isSuccessReplayState),
                                            ("isfailure", mkUIFunction isFailureReplayState),
                                            ("comp", mkUIFunction2 ((.) :: (UIValue->UIValue)->(UIValue->UIValue)->(UIValue->UIValue)))
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
      UINoop -> return ws
      UIAssignment var rhs ->
          return $ doAssignment ws var $ evalExpression ws rhs
      UIFunction f ->
          let r = evalExpression ws f
              ws' = doAssignment ws "last" r
          in print r >> return ws'
      UIDir ->
          do putStrLn $ foldr (\a b -> a ++ "\n" ++ b) "" $ map fst $ ws_bindings ws
             return ws
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
          in liftM (doAssignment ws vname . safeRead) $ (catch (readFile fname) $
                                                         \e -> return $ "ERR " ++ (show e))
                                                         
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
