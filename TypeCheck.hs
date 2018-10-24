-- Type checker
module TypeCheck where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Cont
import System.IO
import Data.Map

import Absgrammar
import Types hiding (dbDebugIndent, dbDebug, stRegister, stFunction)
import Monad hiding (logFunction, throwError)

data TypeCheckerState = IChecker {
  stRegister    :: Map String TypeAll,
  stFunction    :: Map String TypeAll,
  dbDebug       :: DebugInformation,
  dbDebugIndent :: Int,
  stCurrent     :: Map String TypeAll,
  stReturn      :: Maybe (TypeAll),
  stPrev        :: [Map String TypeAll]
}

defaultCheckerState ::
  Map String TypeAll ->
  Map String TypeAll ->
  DebugInformation -> Int ->
  TypeCheckerState
defaultCheckerState reg func db dbi =
  IChecker {
    stRegister = reg,
    stFunction = func,
    dbDebug = db,
    dbDebugIndent = dbi,
    stCurrent = Data.Map.empty,
    stReturn = Nothing,
    stPrev = []
  }
  
typeCheckFunc :: [TypedFunc] -> TypeChecker ()
typeCheckFunc [] = return ()
typeCheckFunc (h:t) = do
  state <- get
  let retType = funcRetType h
  let (InterObj inter) = funcInType h
  let code = funcCode h
  put $ state {stReturn = Just (TypeNFunc retType)}
  typeCheckBlock inter code
  typeCheckFunc t
  
type TypeChecker a = Returning TypeCheckerState a

typeCheckStmts :: [Stmt] -> TypeChecker ()
typeCheckStmts l = sequence_ $ Prelude.map typeCheckStmt l

typeCheckStmt :: Stmt -> TypeChecker ()
typeCheckStmt s = logFunction Stmt "typeCheckStmt" s (_internal s) where
  _internal s = case s of
    StmtSkip -> return ()
  -- -- -- Current object operations
    StmtAdd (Name name) -> do
      typ <- getRegister name
      state <- get
      let obj = stCurrent state
      let nobj = Data.Map.insert name typ obj
      put $ state { stCurrent = nobj }
    StmtRemove (Name name) -> do
      typ <- getRegister name
      state <- get
      let obj = stCurrent state
      let nobj = Data.Map.delete name obj
      put $ state { stCurrent = nobj }
    StmtLocal (Name name) tp -> do
        getNotRegister name
        state <- get
        let obj = stCurrent state
        let nobj = Data.Map.insert name tp obj
        put $ state { stCurrent = nobj }
      where
        getNotRegister s = do
          state <- get
          let registers = stRegister state
          case Data.Map.lookup s registers of
            Nothing -> return ()
            Just x -> lift . lift . throwError $ TCLocalOverriding $ s
    StmtSpare -> return ()
    StmtKill -> return ()
  -- -- -- Object Manipulation
    StmtAssgn f exp -> do
      ftp <- getField f
      etp <- typeCheckExp exp
      typeSatisfiedBy ftp etp
  -- -- -- Scope manipulation
    StmtRepeat -> return ()
    StmtReturn exp -> do
      tp <- typeCheckExp exp
      state <- get
      let retType = stReturn state
      case retType of
        Just rtp -> typeSatisfiedBy rtp tp
        Nothing -> lift . lift . throwError $ NotAFunction
  -- -- -- Block Statements
    StmtWith obj (InterObj interfaces) stmt -> typeCheckBlock interfaces stmt
    StmtIfElse e (InterObj inter1) s1 (InterObj inter2) s2 -> do
      ensureBool e
      typeCheckBlock inter1 s1
      typeCheckBlock inter2 s2
    StmtWhile e (InterObj inter) stmt -> do
      ensureBool e
      typeCheckBlock inter stmt
    StmtEach (InterObj inter) stmt -> typeCheckBlock inter stmt
    StmtFor (InterObj inter) stmt -> typeCheckBlock (Interface (Name "base_counter"):inter) stmt
    StmtNumb _ _ (InterObj inter) stmt -> typeCheckBlock (Interface (Name "base_counter"):inter) stmt
    StmtNumbNew _ _ (InterObj inter) stmt -> typeCheckBlock (Interface (Name "base_counter"):inter) stmt
  -- Function Statements
    StmtFunc name obj -> typeCheckExp (ExpFunc name obj) >> return ()
    StmtObjFunc field obj -> typeCheckExp (ExpObjFunc (ObjField field) obj) >> return ()
    StmtConstruct inter -> typeCheckExp (ExpConstruct inter) >> return ()
    -- All implemented
    -- otherwise -> lift . lift . throwError $ Unknown $ "Not Implemented " ++ (show s)

typeCheckBlock :: [Interface_list] -> [Stmt] -> TypeChecker ()
typeCheckBlock interfaces stmt = do
  state <- get
  let prev = stPrev state
  let curr = stCurrent state
  next <- interToObj interfaces
  put $ state {stPrev = curr:prev, stCurrent = next}
  typeCheckStmts stmt
  put state
    
-- Sprawdzanie interfejsów

objToType :: Map String TypeAll -> TypeChecker TypeAll
objToType mp = do
    let interfaces = Prelude.map convert $ toList $ mp
    return $ TypeNFunc $ TypeObj $ InterObj $ interfaces
  where
    convert (n,tp) = Interface $ Name $ n

interToObj :: [Interface_list] -> TypeChecker (Map String TypeAll)
interToObj l = _internal l empty where
  _internal [] m = return m
  _internal (Interface (Name name):t) m = do
    maybeTyp <- maybeGetRegister name
    case maybeTyp of
      Nothing -> _internal t m
      Just typ ->_internal t $ Data.Map.insert name typ m

getField :: Field -> TypeChecker TypeAll
getField f = logFunction Store "getField" f (_internal f) where
  _internal (FieldSingle (Name name)) = do
    state <- get
    let current = stCurrent state
    let prev = stPrev state
    if name == "base_prev"
      then case prev of
        (h:_) -> objToType h
        otherwise -> lift . lift . throwError $ NoObject
      else case Data.Map.lookup name current of
        Just tp -> return tp
        Nothing -> lift . lift . throwError $ NoObject
  _internal (FieldMany (Name name) field) = do
    state <- get
    let current = stCurrent state
    let prev = stPrev state
    ftype <- getField $ FieldSingle $ Name $ name
    inter <- objToInterface ftype
    nobj <- interToObj inter
    if name == "base_prev"
      then put $ state {stCurrent = nobj, stPrev = tail prev}
      else put $ state {stCurrent = nobj, stPrev = []}
    tp <- getField field
    put $ state
    return tp

getObj :: Object -> TypeChecker TypeAll
getObj (ObjField field) = getField field
getObj ObjCurr = do
  state <- get
  let current = stCurrent state
  tp <- objToType current
  return $ tp
  
objToInterface :: TypeAll -> TypeChecker [Interface_list]
objToInterface (TypeNFunc (TypeObj (InterObj l))) = return l
objToInterface k = lift . lift . throwError $ TCWrongType (TypeNFunc (TypeObj (InterObj []))) k

-- TODO: Rewrite - more strict

-- if t2 satisfies t1
typeSatisfiedBy :: TypeAll -> TypeAll -> TypeChecker ()
typeSatisfiedBy t1 t2 = case (t1, t2) of
  (TypeNFunc tt1, TypeNFunc tt2) -> typeNFuncSatisfiedBy tt1 tt2
  (TypeFunc r1 (InterObj l1), TypeFunc r2 (InterObj l2)) -> do
    typeNFuncSatisfiedBy r1 r2
    typeInterfaceSatisfiedBy l1 l2
  (TypeFunc _ _, TypeNFunc (TypeVoid)) -> return ()
  otherwise -> lift . lift . throwError $ TCWrongType t1 t2
  
typeNFuncSatisfiedBy :: TypeNFunc -> TypeNFunc -> TypeChecker ()
typeNFuncSatisfiedBy t1 t2 = case (t1, t2) of
  (TypeInt, TypeInt) -> return ()
  (TypeBool, TypeBool) -> return ()
  (TypeChar, TypeChar) -> return ()
  (TypeVoid, TypeVoid) -> return ()
  (TypeObj (InterObj l1), TypeObj (InterObj l2)) -> typeInterfaceSatisfiedBy l1 l2
  (TypeObj _, TypeVoid) -> return ()
  otherwise -> lift . lift . throwError $ TCWrongType (TypeNFunc t1) (TypeNFunc t2)
-- TODO:

typeInterfaceSatisfiedBy :: [Interface_list] -> [Interface_list] -> TypeChecker ()
typeInterfaceSatisfiedBy [] t2 = return ()
typeInterfaceSatisfiedBy (h:t) t2 = do
  if elem h t2
    then typeInterfaceSatisfiedBy t t2
    else lift . lift . throwError $ TCWrongInterface (InterObj t2) h
  
typeCheckExp :: Exp -> TypeChecker TypeAll
typeCheckExp f = logFunction Exp "typeCheckExp" f (_internal f) where
  _internal f =
    case f of
      -- Numbers Values
      ExpInt _ -> return $ TypeNFunc $ TypeInt
    -- Boolean Values
      ExpTrue -> return $ TypeNFunc $ TypeBool
      ExpFalse -> return $ TypeNFunc $ TypeBool
    -- Object Values
      ExpObj obj -> getObj obj --return $ TypeNFunc $ TypeBool -- TODO:
      ExpNull -> return $ TypeNFunc $ TypeVoid
      ExpChar c -> return $ TypeNFunc $ TypeChar
    -- -- -- Arithmetic operations
      ExpAdd e1 e2 -> ensureInt e1 >> ensureInt e2
      ExpSub e1 e2 -> ensureInt e1 >> ensureInt e2
      ExpMul e1 e2 -> ensureInt e1 >> ensureInt e2
      ExpDiv e1 e2 -> ensureInt e1 >> ensureInt e2
      ExpMod e1 e2 -> ensureInt e1 >> ensureInt e2
      ExpBracket e1 -> typeCheckExp e1
    -- -- -- Arithmetic equations
      ExpLess e1 e2 -> ensureInt e1 >> ensureInt e2 >> (return $ TypeNFunc $ TypeBool)
      ExpMore e1 e2 -> ensureInt e1 >> ensureInt e2 >> (return $ TypeNFunc $ TypeBool)
      ExpLessE e1 e2 -> ensureInt e1 >> ensureInt e2 >> (return $ TypeNFunc $ TypeBool)
      ExpMoreE e1 e2 -> ensureInt e1 >> ensureInt e2 >> (return $ TypeNFunc $ TypeBool)
      ExpEq e1 e2 -> ensureInt e1 >> ensureInt e2 >> (return $ TypeNFunc $ TypeBool)
      ExpNEq e1 e2 -> ensureInt e1 >> ensureInt e2 >> (return $ TypeNFunc $ TypeBool)
    -- -- -- Boolean Operations
      ExpNegate e1 -> do
        t1 <- typeCheckExp e1
        if t1 == (TypeNFunc (TypeBool))
          then return $ TypeNFunc $ TypeBool
          else lift . lift . throwError $ TCWrongType (TypeNFunc (TypeBool)) t1
      ExpObjEq e1 e2 -> ensureObj e1 >> ensureObj e2 >> (return $ TypeNFunc $ TypeBool)
      ExpObjNEq e1 e2 -> ensureObj e1 >> ensureObj e2 >> (return $ TypeNFunc $ TypeBool)
    -- -- -- Object Operations
      ExpConstruct l -> do
        inter <- constructToInter l
        return $ TypeNFunc $ TypeObj $ InterObj inter
      ExpFunc (Name name) obj -> do
        state <- get
        let functions = stFunction state
        atp <- getObj obj
        case (Data.Map.lookup name functions, atp) of
          (Just (TypeFunc ret (InterObj l)), TypeNFunc (TypeObj (InterObj l2))) -> do
            typeInterfaceSatisfiedBy l l2
            return $ TypeNFunc $ ret
          otherwise -> lift . lift . throwError $ Unknown $ "No function or wrong type"
      ExpObjFunc obj obj2 -> do
        ftp <- getObj obj
        atp <- getObj obj2
        case (ftp, atp) of
          (TypeFunc ret (InterObj l), TypeNFunc (TypeObj (InterObj l2))) -> do
            typeInterfaceSatisfiedBy l l2
            return $ TypeNFunc $ ret
          otherwise -> lift . lift . throwError $ TCWrongType (TypeFunc TypeInt (InterObj [])) ftp
      ExpLambda tp inter stmt -> do
        -- TODO (Sprawdzenie czy wewnętrzna funcka jest ok)
        return $ TypeFunc tp inter
      -- All implemented
      -- otherwise -> lift . lift . throwError $ Unknown $ "Not Implemented: typeCheckExp " ++ (show f)

constructToInter :: [Construct_Interface] -> TypeChecker [Interface_list]
constructToInter l = _internal l [] where
  _internal [] l = return l
  _internal (ConsInter (Name name) exp:t) l = do
    mntp <- maybeGetRegister name
    case mntp of
      Nothing -> _internal t l
      Just ntp -> do
        etp <- typeCheckExp exp
        typeSatisfiedBy ntp etp
        _internal t (Interface (Name name):l)

ensureInt :: Exp -> TypeChecker TypeAll
ensureInt e1 = do
  t1 <- typeCheckExp e1
  if t1 == (TypeNFunc (TypeInt))
    then return $ TypeNFunc $ TypeInt
    else lift . lift . throwError $ TCWrongType (TypeNFunc (TypeInt)) t1

ensureBool :: Exp -> TypeChecker TypeAll
ensureBool e1 = do
  t1 <- typeCheckExp e1
  if t1 == (TypeNFunc (TypeBool))
    then return $ TypeNFunc $ TypeBool
    else lift . lift . throwError $ TCWrongType (TypeNFunc (TypeBool)) t1
    
ensureObj :: Exp -> TypeChecker TypeAll
ensureObj e1 = do
  t1 <- typeCheckExp e1
  case t1 of
    (TypeNFunc (TypeObj _)) -> return $ t1
    otherwise -> lift . lift . throwError $ TCWrongType (TypeNFunc (TypeInt)) t1
    
-- Helper functions

getRegister :: String -> TypeChecker TypeAll
getRegister s = do
  maybeReg <- maybeGetRegister s
  case maybeReg of
    Nothing -> lift . lift . throwError $ TCUndeclaredRegister $ s
    Just x -> return x

maybeGetRegister :: String -> TypeChecker (Maybe TypeAll)
maybeGetRegister s = do
  state <- get
  let registers = stRegister state
  case Data.Map.lookup s registers of
    Nothing -> return $ Nothing
    Just x -> return $ Just x
    
logFunction :: (Show a, Show b) => Types.DebugType -> String -> a -> TypeChecker b -> TypeChecker b
logFunction dbType name param func = do
    dbState <- ldebugStartFunction dbType name param
    ret <- func
    ldebugEndFunction dbType name param ret dbState
    return ret
  where
    ldebugStartFunction :: (Show a) => Types.DebugType -> String -> a -> TypeChecker DbState
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
    ldebugEndFunction :: (Show a, Show b) => Types.DebugType -> String -> a -> b -> DbState -> TypeChecker ()
    ldebugEndFunction e s l retVal indentCurr = do
      st <- get
      if (dbDebug $ st) e
        then do
          put $ st {dbDebugIndent = indentCurr }
          let indent = replicate indentCurr ' '
          lprinterr $ indent ++ "-:" ++ s ++ " " ++ (show l) ++ " = " ++ (show retVal)
        else return ()