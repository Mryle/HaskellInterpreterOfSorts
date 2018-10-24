module InterpretProgram where

import Control.Monad.State
import Absgrammar
import Data.Char
import Data.Map

import Types
import Monad
import InterpretStmt
import InterpretDecl
import TypeCheck

loadDeclarations :: Program -> Interpreter ()
loadDeclarations (Program d) = do
  addStandardLibrary
  interpretDeclarations d
  
prepareTypeCheckerState :: InterpreterState -> TypeCheckerState
prepareTypeCheckerState state = defaultCheckerState reg func db dbi where
  db = Types.dbDebug state
  dbi = Types.dbDebugIndent state
  reg = Types.stRegister state
  funcRaw = Types.stFunction state :: Map String TypedFunc
  func = Data.Map.map toType funcRaw :: Map String TypeAll
-- tCresult <- runReturning tCState (\_ -> return ()) $ typeCheckFunc []
  
checkType :: Map String TypedFunc -> TypeChecker ()
checkType function = do
  let func = elems function
  typeCheckFunc func
  
runProgram :: Interpreter ()
runProgram = interpretStmt (StmtFunc (Name "main") ObjCurr)

-- deprecated
interpretProgram :: Program -> Interpreter ()
interpretProgram (Program d) = do
  addStandardLibrary
  interpretDeclarations d
  interpretStmt (StmtFunc (Name "main") ObjCurr)

  
addStandardLibrary = do
  addStlFunc "print" stlPrint TypeBool $ generate_interface ["str_print"]
  addStlFunc "charToInt" stlCharToInt TypeInt $ generate_interface ["str_print"]
  addStlFunc "intToChar" stlIntToChar TypeChar $ generate_interface ["base_counter"]


addStlFunc :: String -> Interpreter () -> TypeNFunc -> Interface_specifier -> Interpreter ()
addStlFunc name impl retType inter = 
    addFunction name funcImpl retType inter []
  where
    funcImpl (VObj arg) = do
      stackIndex <- getStackNumb
      prev <- getCurrentLoc
      val <- callCC $ \return -> do
        interpretBlockInterfacesAll name arg prev inter [StmtReturn ExpTrue] (Just (stackFillReturn return)) (Just impl)
        throwError NoReturn
      stackRestore stackIndex
      ensureCorrectType (TypeNFunc retType) val
      return $ val
  

stlPrint = do
  c <- interpretExpectChar $ ExpObj $ ObjField $ FieldSingle $ Name $ "str_print"
  lputs [c]
  return ()
  
stlCharToInt = do
  c <- interpretExpectChar $ ExpObj $ ObjField $ FieldSingle $ Name $ "str_print"
  let i = ord c
  interpretStmt $ StmtReturn $ ExpInt $ toInteger i
  
stlIntToChar = do
  i <- interpretExpectInt $ ExpObj $ ObjField $ FieldSingle $ Name $ "base_counter"
  let c = chr $ i
  interpretStmt $ StmtReturn $ ExpChar $ c