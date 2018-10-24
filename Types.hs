-- Declaration of all general types Used in interpreter
module Types where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Cont

import Absgrammar
import Data.Map

-- Store Declaration

data Loc =
  LocNoObj
  | LocObj Int
  deriving (Ord, Eq)

instance Show Loc where
  show LocNoObj = "Ptr(Null)"
  show (LocObj num) = "Ptr(" ++ show num ++ ")"
  
data TypedValue =
  VInt Int
  | VChar Char
  | VBool Bool
  | VObj Loc
  | VFunc TypedFunc
  deriving (Show)

data TypedFunc = TypedFunc {
  funcRetType :: TypeNFunc,
  funcInType :: Interface_specifier,
  funcExec :: (TypedValue -> Interpreter TypedValue),
  funcCode :: [Stmt]
}

toType :: TypedFunc -> TypeAll
toType tp = TypeFunc (funcRetType tp) (funcInType tp)

instance Show TypedFunc where
  show tp = "Func " ++ (show (funcInType tp)) ++ " -> " ++ (show (funcRetType tp))

type Obj = Map String TypedValue

data StackEntry = StackEntry {
  stackName :: String,      -- Name of stack. For debugging reasons
  stackNumber :: Int,       -- Number of stack. For restoring it after function
  stackCurrent :: Loc,      -- Current Object
  stackLocals :: [String],  -- Only names of local variables. Should be deleted on end
  stackPrev :: Loc,  -- previous base_prev obj. It needs to be restored on end
  stackEscape :: Maybe (() -> Interpreter ()),
  stackRepeat :: Maybe (() -> Interpreter ()),
  stackReturn :: Maybe (TypedValue -> Interpreter TypedValue)
}

instance Show StackEntry where
  show t = "Frame: " ++ name ++ num ++ " Obj:" ++ obj ++ ret ++ "\n" where
    name = stackName $ t
    num = " Num:" ++ (show (stackNumber t))
    obj = show $ stackCurrent $ t
    ret = case stackReturn t of
      Nothing -> ""
      Just _ -> " Return"

type Stack = [StackEntry]

data ErrorType =
  -- Execution errors
  Unknown String
  | WrongType
  | Arithmetic
  | NoObject
  | NotAFunction
  | NoReturn
  -- Delaration and final errors
  | DuplicateDecl
  | RegisterExists
  | EndOfStack
  | TCWrongType TypeAll TypeAll -- Type checker wrong type
  | TCUndeclaredRegister String
  | TCLocalOverriding String
  | TCWrongInterface Interface_specifier Interface_list
  deriving (Show)

errorToInt :: ErrorType -> Int
errorToInt e = case e of
  WrongType -> 1
  Arithmetic -> 2
  NoObject -> 3
  NoReturn -> 5
  otherwise -> 127

instance Error ErrorType where
  noMsg = Unknown ""
  strMsg = Unknown
  
data DebugType =
  Exp
  | Stmt
  | Store
  | Declaration
  | Errors
  | Stack
  deriving (Show)

type DebugInformation = DebugType -> Bool

class DebugState a where
  dsDebug       :: a -> DebugInformation
  dsIndent      :: a -> Int

data InterpreterState = IState {
  stRegister    :: Map String TypeAll,
  stFunction    :: Map String TypedFunc,
  stVariables    :: Map Loc Obj,
  stObjCounter  :: Int,
  stStack       :: Stack,
  dbDebug       :: DebugInformation,
  dbDebugIndent :: Int,
  dbException   :: Maybe (ErrorType -> Interpreter ()),
  dbReturnCC    :: Maybe (() -> Interpreter ()) -- to pass CC
}

instance Show InterpreterState where
  show s =  "Registers:" ++ (show $ stRegister s) ++ "\n" ++
            "Functions:" ++ (show $ stFunction s) ++ "\n" ++
            "Variables:" ++ (show $ stVariables s) ++ "\n" ++
            "Stack    :" ++ (show $ stStack    s) ++ "\n" ++
            "Debug    :" ++ (show $ debug $ dbDebug s) ++ "\n" where
    debug f = checkDebug [Stmt, Exp, Store, Errors, Stack] f ""
    checkDebug [] f a = a
    checkDebug (h:t) f a = case (f h) of
      True -> checkDebug t f $ a ++ (show h) ++ " "
      False -> checkDebug t f a

startingState :: Bool -> InterpreterState
startingState debug = IState {
    stRegister = fromList [
      ("base_counter",  TypeNFunc TypeInt),
      ("base_errno",    TypeNFunc TypeInt),
      ("str_print",     TypeNFunc TypeChar),
      ("str_next",      TypeNFunc $ TypeObj $ stringInterface),
      ("str_prev",      TypeNFunc $ TypeObj $ stringInterface)],
    stFunction = Data.Map.empty, -- TODO: Built in functions
    stVariables = fromList [generateObject 0], -- generateObject 0, counterObject 0 1
    stObjCounter = 1,
    stStack = [stackEntry "_main" 0 LocNoObj],
    dbDebug = defaultDebug,
    dbDebugIndent = 0,
    dbException = Nothing,
    dbReturnCC = Nothing
  } where
  stringInterface = generate_interface ["str_print", "str_next", "str_prev"]
  generateObject num = (LocObj num, Data.Map.empty)
  counterObject loc num = (LocObj loc, fromList[("base_counter", VInt num)])
  listObject loc objLoc = (LocObj loc, fromList[("base_next", VObj (LocObj objLoc))])
  stackEntry name loc prev = StackEntry {
      stackName = name,
      stackNumber = 0,
      stackCurrent = LocObj loc,
      stackLocals = [],
      stackPrev = prev,
      stackReturn = Nothing,
      stackRepeat = Nothing,
      stackEscape = Nothing
    }
  defaultDebug dp =  debug
    -- case dp of
      -- Store -> False
      -- otherwise -> debug

generate_interface :: [String] -> Interface_specifier
generate_interface l = InterObj $ Prelude.map (Interface . Name) l

type Returning s a = ContT () (StateT s (ErrorT ErrorType IO)) a
type Interpreter a = Returning InterpreterState a
