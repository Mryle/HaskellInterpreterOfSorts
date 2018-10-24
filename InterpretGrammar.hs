module InterpretGrammar where

import Control.Monad.State
import Control.Monad.Cont
import Control.Monad.Error
import System.IO

import Absgrammar
import Pargrammar
import Lexgrammar
import Printgrammar
import Absgrammar

import InterpretProgram

import Types
import Monad

import ErrM

-- Type Definitions

type ParseFun a = [Token] -> Err a

type InterpretedType = Program
parse :: ParseFun InterpretedType
parse = pProgram

-- Interpreter start, continuation based

-- interpret :: Bool -> InterpretedType -> IO ()
-- interpret debug = \e -> do
    -- x <- runReturning (startingState debug) cont $ interpretFunc e
    -- case x of
      -- Left er -> print $ "Uncaught error " ++ (show er)
      -- Right x -> return ()
  -- where
    -- contE :: TypedValue -> (StateT s (ErrorT ErrorType IO)) ()
    -- contE val = do
      -- lift $ lift $ print $ "Returned " ++ (show val)
    -- cont :: () -> (StateT s (ErrorT ErrorType IO)) ()
    -- cont _ = do
      -- return ()
      
interpret :: Bool -> InterpretedType -> IO ()
interpret debug = \e -> do
    x <- runReturningNCont (startingState debug) $ loadDeclarations e
    case x of
      Left er -> print $ "Uncaught error " ++ (show er)
      Right (_,s) -> do
        let tCState = prepareTypeCheckerState s
        let func = stFunction s
        y <- runReturningNCont tCState $ checkType func
        case y of 
          Left er -> print $ "Uncaught error " ++ (show er)
          Right _ -> do
            z <- runReturningNCont s runProgram
            case z of
              Left er -> print $ "Uncaught error " ++ (show er)
              Right _ -> return ()
-- Running file and everything (TODO)
  
runFile :: ParseFun InterpretedType -> FilePath -> IO ()
runFile p f = readFile f >>= run p

run :: ParseFun InterpretedType -> String -> IO ()
run p s = let ts = myLexer s in case p ts of
           Bad s    -> do putStrLn "\nParse              Failed...\n"
                          putStrLn "Tokens:"
                          putStrLn $ show ts
                          putStrLn s
           Ok  tree -> do InterpretGrammar.interpret False tree



showTree :: (Show a, Print a) => a -> IO ()
showTree tree
 = do
      putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree