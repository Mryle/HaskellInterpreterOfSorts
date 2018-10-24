module InterpretDecl where

import Control.Monad.State
import Control.Monad
import Data.Map

import Absgrammar

import InterpretStmt

import Types
import Monad

interpretDeclarations :: [Declaration] -> Interpreter ()
interpretDeclarations l = sequence_ $ Prelude.map interpretDeclaration l

interpretDeclaration :: Declaration -> Interpreter ()
interpretDeclaration d = logFunction Declaration "interpretDeclaration" d (_internal d) where
  _internal (DeclType (Name name) tp) = do
    state <- get
    let registers = stRegister $ state
    let currentType = Data.Map.lookup name registers
    case currentType of
      Nothing -> do
        modify $ \s -> s {stRegister = Data.Map.insert name tp $ stRegister s }
      Just t -> throwError $ DuplicateDecl
  _internal (DeclFunc (Name name) tp inter stmt) = addFunction name funcImpl tp inter stmt
    where
    funcImpl (VObj arg) = do
      let prev = LocNoObj --getCurrentLoc
      stackIndex <- getStackNumb
      val <- callCC $ \return -> do
        interpretBlockInterfacesFunc name arg prev inter stmt $ Just $ stackFillReturn return
        throwError NoReturn
      stackRestore stackIndex
      ensureCorrectType (TypeNFunc tp) val
      return $ val
  -- All implemented
  -- _internal d = throwError $ Unknown $ "Not Implemented " ++ (show d)

-- | DeclFunc Name TypeNFunc Interface_specifier Stmt -- TODO

addFunction :: String -> (TypedValue -> Interpreter TypedValue) -> TypeNFunc -> Interface_specifier -> [Stmt] -> Interpreter ()
addFunction name funcImpl retType inter stmt = modify $ \s -> s {stFunction = Data.Map.insert name func $ stFunction s }
  where
  func = TypedFunc {
            funcRetType = retType,
            funcInType = inter,
            funcExec = funcImpl,
            funcCode = stmt
            }