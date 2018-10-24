-- General functions that are helpful when using Returning and Interpreter Monad
module Monad where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Cont
import System.IO

import Types

-- Monad and helper functions

runReturning :: s
  -> (b -> StateT s (ErrorT ErrorType IO) ())
  -> Returning s b
  -> IO (Either ErrorType ((), s))
runReturning s c f = runErrorT (runStateT (runContT f c) s)

runReturningNCont s f = runReturning s (\_ -> return ()) f

throwError :: ErrorType -> Interpreter a
throwError err = do
  state <- get
  case dbException $ state of
    Just ret -> ret err
    Nothing -> return ()
  (lift . lift . Control.Monad.Error.throwError) err

catchError :: Interpreter a -> (ErrorType -> Interpreter a) -> Interpreter a
catchError func handler = do
  state <- get
  let prevExc = dbException $ state
  val <- Monad.callCC (\ret -> do
    exception <- Monad.callCC (\throwErr -> do
      modify (\s -> s { dbException = Just throwErr })
      x <- func
      _ <- ret x
      Monad.throwError $ Unknown "Scope should not be here"
      )
    handler exception
    )
  modify (\s -> s { dbException = prevExc })
  return $ val
  
mlift :: IO a -> Returning s a
mlift = lift . lift . lift

lprint :: (Show st) => st -> Returning s ()
lprint = do
  mlift . print
  
lputs :: String -> Returning s ()
lputs = do
  mlift . putStr

lprinterr :: (Show st) => st -> Returning s ()
lprinterr s = do
  mlift $ hPrint stderr s
  return ()

callCC = Control.Monad.Cont.callCC
  
type DbState = Int
  
-- Write debug in case we have this option in state
ldebug :: Types.DebugType -> String -> Interpreter ()
ldebug e s = do
  st <- get
  let indentCurr = dbDebugIndent $ st
  if (dbDebug $ st) e
    then do
      let indent = replicate indentCurr ' '
      lprinterr $ indent ++ s
    else return ()


indentPadding = 1

logFunction :: (Show a, Show b) => Types.DebugType -> String -> a -> Interpreter b -> Interpreter b
logFunction dbType name param func = do
    dbState <- ldebugStartFunction dbType name param
    ret <- func
    ldebugEndFunction dbType name param ret dbState
    return ret
  where
    ldebugStartFunction :: (Show a) => Types.DebugType -> String -> a -> Interpreter DbState
    ldebugStartFunction e s l = do
      st <- get
      let indentCurr = dbDebugIndent $ st
      if (dbDebug $ st) e
        then do
          let indent = replicate indentCurr ' '
          lprinterr $ indent ++ "+:" ++ s ++ " " ++ (show l)
          put $ st {dbDebugIndent = (indentCurr + indentPadding) }
          return indentCurr
        else return indentCurr
    ldebugEndFunction :: (Show a, Show b) => Types.DebugType -> String -> a -> b -> DbState -> Interpreter ()
    ldebugEndFunction e s l retVal indentCurr = do
      st <- get
      if (dbDebug $ st) e
        then do
          put $ st {dbDebugIndent = indentCurr }
          let indent = replicate indentCurr ' '
          lprinterr $ indent ++ "-:" ++ s ++ " " ++ (show l) ++ " = " ++ (show retVal)
        else return ()

ldebugStack :: Interpreter ()
ldebugStack = do
  state <- get
  ldebug Stack $ "Current stack " ++ (show $ stStack state)