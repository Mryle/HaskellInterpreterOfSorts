module InterpretStmt where

import Control.Monad.State
import Data.Map

import Absgrammar

import Types
import Monad

interpretStmts :: [Stmt] -> Interpreter ()
interpretStmts l = sequence_ $ Prelude.map interpretStmt l

interpretStmt :: Stmt -> Interpreter ()
interpretStmt s = logFunction Stmt "interpretStmt" s (interpret s) where
  interpret s = do
    state <- get
    let stack = stStack state
    let dbi = dbDebugIndent state
    let prevExc = dbException $ state
    catchError (_internal s) $ \err -> do
      modify $ \s -> s {stStack = stack, dbDebugIndent = dbi, dbException = prevExc}
      ldebug Errors $ "Catched error:" ++ (show err)
      stackFrame <- getStackHead
      ldebug Errors $ show $ stackFrame
      loc <- getCurrentLoc
      variables <- getVariables
      object <- eitherLookup loc $ variables
      case Data.Map.lookup "base_errno" object of
          Nothing -> throwError err
          Just _ -> do
            let newObject = Data.Map.insert "base_errno" (VInt (errorToInt err)) object
            let newVariables = Data.Map.insert loc newObject variables
            modify $ \s -> s{stVariables = newVariables}
  _internal s = case s of
    StmtSkip -> return ()
  -- -- -- Current object operations
    StmtAdd (Name name) -> getRegisterType name >>= modifyCurrent . (addField name)
    StmtRemove (Name name) -> getRegisterType name >> modifyCurrent ( \o -> Data.Map.delete name o)
    StmtLocal (Name name) tp -> do
        reg <- tryGetRegisterType name
        case reg of
          Just t -> throwError $ RegisterExists
          Nothing -> return ()
        modifyCurrent (addField name tp)
    StmtSpare -> do
      stackFrame <- getStackHead
      let escape = stackEscape $ stackFrame
      case escape of
        Nothing -> throwError $ Unknown "No Escape function"
        Just esc -> esc ()
    StmtKill -> do
      loc <- getCurrentLoc
      variables <- getVariables
      modify $ \s -> s { stVariables = Data.Map.delete loc variables }
      stack <- getStack
      esc <- findLast loc stack Nothing
      case esc of
        Nothing -> throwError $ Unknown "Could not find escape function"
        Just escape -> escape ()
      where
        findLast loc (h:t) a = do
          if loc == (stackCurrent h)
            then findLast loc t (stackEscape h)
            else findLast loc t a
        findLast loc _ a = return a
  -- -- -- Object Manipulation
    StmtAssgn f exp -> do
        let field = _field f
        objectLoc <- getObjectLoc ( _obj f ) >>= ensureValidLoc
      -- Counting value & checking type
        tp <- tryGetRegisterType field
        val <- interpretExp exp
        nval <- case tp of
          Just t -> ensureCorrectType t val
          Nothing -> do
            ldebug Stmt $ "No type found for register " ++ (show field)
            ensureValidValue val
      -- Ensuring object has correct interface
        variables <- getVariables
        object <- eitherLookup objectLoc $ variables
        eitherLookup field object
      -- modify
        modifyObject objectLoc (Data.Map.insert field nval)
      where
        -- helper functions
        _obj :: Field -> Object
        _obj (FieldMany f (FieldSingle _)) = ObjField $ FieldSingle $ f
        _obj (FieldMany n f) = case _obj f of
          ObjField ff -> ObjField $ FieldMany n ff
        _obj f = ObjCurr
        _field :: Field -> String
        _field (FieldMany _ f) = _field f
        _field (FieldSingle (Name name)) = name
  -- -- -- Scope manipulation
    StmtRepeat -> do
      stackFrame <- getStackHead
      let escape = stackRepeat $ stackFrame
      case escape of
        Nothing -> throwError $ Unknown "No Escape function"
        Just esc -> esc ()
    StmtReturn exp -> do
      stackFrame <- getStackHead
      e1 <- interpretExp exp
      case stackReturn $ stackFrame of
        Nothing -> do
          lprint $ show stackFrame
          throwError NotAFunction
        Just r -> do
          r e1
          throwError $ Unknown "Scope should not be here"
  -- -- -- Block Statements
    StmtWith obj interface stmt -> do
      loc <- getObjectLoc obj >>= ensureValidLoc
      interpretBlockInterfaces "with" loc interface stmt
    StmtIfElse e inter1 s1 inter2 s2 -> do
      loc <- getCurrentLoc
      option <- interpretExpectBool e
      if option
        then interpretBlockInterfaces "ifT" loc inter1 s1
        else interpretBlockInterfaces "ifF" loc inter2 s2
    -- StmtWhile e inter stmt -> do -- TODO: Change to more iterating version
      -- loc <- getCurrentLoc
      -- callCC (\repeat -> do
        -- modify $ \s -> s {dbReturnCC = (Just repeat)}
        -- return ())
      -- ldebug Stmt $ "Just After Repeat"
      -- state <- get
      -- let (Just repeat) = dbReturnCC $ state
      -- val <- interpretExpectBool e
      -- if val
        -- then do
          -- interpretBlockInterfaces "while" loc inter stmt
          -- repeat ()
        -- else return ()
    StmtWhile e inter stmt -> do -- TODO: Change to more iterating version
      loc <- getCurrentLoc
      val <- interpretExpectBool e
      if val
        then do
          interpretBlockInterfaces "while" loc inter stmt
          interpretStmt (StmtWhile e inter stmt)
        else return ()
    StmtEach inter stmt -> do
        variables <- getVariables
        objs <- filterObject inter $ keys variables
        forall objs
      where
        forall [] = return ()
        forall (h:t) = interpretBlockInterfaces "each" h inter stmt >> forall t
    StmtFor inter stmt -> do
        curr <- getCurrentLoc
        variables <- getVariables
        objs <- filterObject inter $ keys variables
        forall curr objs 1
      where
        forall curr [] _ = return ()
        forall curr (h:t) n = interpretBlockInterfacesFunc "for" h curr inter stmt (Just (inj n)) >> forall curr t (n+1)
        inj n = modifyCurrent $ Data.Map.insert "base_counter" $ VInt n
    StmtNumb st en inter stmt -> do
        curr <- getCurrentLoc
        variables <- getVariables
        objs <- filterObject inter $ keys variables
        forall curr objs (fromInteger st) (fromInteger en)
      where
        forall curr [] _ _= return ()
        forall curr (h:t) n en 
          | n < en = interpretBlockInterfacesFunc "number" h curr inter stmt (Just (inj n)) >> forall curr t (n+1) en
          | n > en = interpretBlockInterfacesFunc "number" h curr inter stmt (Just (inj n)) >> forall curr t (n-1) en
          | otherwise = return ()
        inj n = modifyCurrent $ Data.Map.insert "base_counter" $ VInt n
    StmtNumbNew st en inter stmt -> do
        curr <- getCurrentLoc
        variables <- getVariables
        objs <- filterObject inter $ keys variables
        forall curr objs (fromInteger st) (fromInteger en)
      where
        addInterfaces (InterObj []) loc = return ()
        addInterfaces (InterObj (Interface (Name name):t)) loc = do
          tp <- getRegisterType name
          modifyObject (LocObj loc) $ addField name tp
          addInterfaces (InterObj t) loc
        forall curr [] n en =
          if n == en
            then return ()
            else do
              loc <- constructObjEmpty
              addInterfaces inter loc
              forall curr (LocObj loc:[]) n en
        forall curr (h:t) n en 
          | n < en = do
            interpretBlockInterfacesFunc "numberNew" h curr inter stmt (Just (inj n)) 
            forall curr t (n+1) en
          | n > en = do
            interpretBlockInterfacesFunc "numberNew" h curr inter stmt (Just (inj n))
            forall curr t (n-1) en
          | otherwise = return ()
        inj n = modifyCurrent $ Data.Map.insert "base_counter" $ VInt n
  -- Function Statements (Need to catch NoReturn, and rethrow everything else
    StmtFunc name obj -> do
      state <- get
      let stack = stStack state
      let dbi = dbDebugIndent state
      let prevExc = dbException $ state
      catchError (interpretExp (ExpFunc name obj)) $ \err -> do
        modify $ \s -> s {stStack = stack, dbDebugIndent = dbi, dbException = prevExc}
        case err of
          NoReturn -> return $ VObj $ LocNoObj
          otherwise -> throwError $ err
      return ()
    StmtObjFunc field obj -> do
      state <- get
      let stack = stStack state
      let dbi = dbDebugIndent state
      let prevExc = dbException $ state
      catchError (interpretExp (ExpObjFunc (ObjField field) obj)) $ \err -> do
        modify $ \s -> s {stStack = stack, dbDebugIndent = dbi, dbException = prevExc}
        case err of
          NoReturn -> return $ VObj $ LocNoObj
          otherwise -> throwError $ err
      return ()
    StmtConstruct inter -> interpretExp (ExpConstruct inter) >> return ()
    -- All implemented
    -- otherwise -> throwError $ Unknown $ "Not Implemented " ++ (show s)

-- Interpret Exp
interpretExp :: Exp -> Interpreter TypedValue
interpretExp f = logFunction Exp "interpretExp" f (_internal f) where
  _internal f =
    case f of
    -- Numbers Values
      ExpInt n -> return $ VInt $ fromInteger $ n
    -- Boolean Values
      ExpTrue -> return $ VBool $ True
      ExpFalse -> return $ VBool $ False
    -- Object Values
      ExpObj obj -> getObjectValue obj >>= ensureValidValue
      ExpNull -> return $ VObj $ LocNoObj
      ExpChar c -> return $ VChar $ c
    -- -- -- Arithmetic operations
      ExpAdd e1 e2 -> interpretExpOperation e1 e2 truePredicate (" + ", (+))
      ExpSub e1 e2 -> interpretExpOperation e1 e2 truePredicate (" - ", (-))
      ExpMul e1 e2 -> interpretExpOperation e1 e2 truePredicate (" * ", (*))
      ExpDiv e1 e2 -> interpretExpOperation e1 e2 non0Second (" / ", (div))
      ExpMod e1 e2 -> interpretExpOperation e1 e2 non0Second (" % ", (mod))
      ExpBracket e1 -> interpretExp e1
    -- -- -- Arithmetic equations
      ExpLess e1 e2 -> interpretExpCompare e1 e2 (" < ", (<))
      ExpMore e1 e2 -> interpretExpCompare e1 e2 (" > ", (>))
      ExpLessE e1 e2 -> interpretExpCompare e1 e2 (" <= ", (<=))
      ExpMoreE e1 e2 -> interpretExpCompare e1 e2 (" <= ", (>=))
      ExpEq e1 e2 -> interpretExpCompare e1 e2 (" == ", (==))
      ExpNEq e1 e2 -> interpretExpCompare e1 e2 (" != ", (/=))
    -- -- -- Boolean Operations
      ExpNegate e1 -> interpretExpectBool e1 >>= return . VBool . not
      ExpObjEq e1 e2 -> do
        l1 <- interpretExpectLoc e1 >>= ensureValidLoc
        l2 <- interpretExpectLoc e2 >>= ensureValidLoc
        case (l1,l2) of
          (LocObj n1, LocObj n2) -> return $ VBool $ (n1 == n2)
          (LocNoObj, LocNoObj) -> return $ VBool $ True
          otherwise -> return $ VBool $ False
      ExpObjNEq e1 e2 -> interpretExpectBool (ExpObjEq e1 e2) >>= return . VBool . not
    -- -- -- Object Operations
      ExpConstruct l -> do
        nloc <- constructObjEmpty
        interpretAddInterfaces (LocObj nloc) l
        return $ VObj $ LocObj $ nloc
      ExpFunc (Name name) obj -> do
        arg <- getObjectLoc obj >>= ensureValidLoc
        functions <- getFunctions
        func <- eitherLookup name $ functions
        returns <- stashReturns
        ret <- (funcExec func) $ VObj $ arg
        restoreReturns returns
        return ret
      ExpObjFunc obj obj2 -> do
        val <- interpretExp $ ExpObj $ obj
        arg <- interpretExp $ ExpObj $ obj2
        case val of
          VFunc func -> do
            returns <- stashReturns
            ret <- (funcExec func) $ arg
            restoreReturns returns
            return ret
          VObj LocNoObj -> throwError NoObject
          otherwise -> throwError WrongType
        
      ExpLambda tp inter stmt -> getCurrentLoc >>= \curr ->
          return $ VFunc $ TypedFunc {
            funcRetType = tp,
            funcInType = inter,
            funcExec = lambda curr,
            funcCode = stmt
            }
        where
          lambda prev (VObj arg) = do
            stackIndex <- getStackNumb
            val <- callCC $ \ret -> do
              interpretBlockInterfacesFunc "lambda" arg prev inter stmt $ Just $ stackFillReturn ret
              throwError NoReturn
            stackRestore stackIndex
            ensureCorrectType (TypeNFunc tp) val
            return $ val
      -- All implemented
      -- otherwise -> throwError $ Unknown $ "Not Implemented: interpretExp " ++ (show f)

-- Helping functions

type CompareFunc = (String, Int -> Int -> Bool)
type Predicate = Int -> Int -> Bool
type IntFunc = (String, Int -> Int -> Int)

constructObjEmpty :: Interpreter Int
constructObjEmpty = do
  state <- get
  variables <- getVariables
  let nloc = 1 + (stObjCounter $ state)
  let nvar = Data.Map.insert (LocObj nloc) Data.Map.empty $ variables
  put $ state {stObjCounter = nloc, stVariables = nvar}
  return nloc

interpretAddInterfaces :: Loc -> [Construct_Interface] -> Interpreter ()
interpretAddInterfaces loc [] = return ()
interpretAddInterfaces loc (ConsInter (Name name) e:t) = do
  tp <- getRegisterType name
  val <- interpretExp e
  nval <- ensureCorrectType tp val
  modifyObject loc (Data.Map.insert name nval)
  interpretAddInterfaces loc t

interpretExpCompare :: Exp -> Exp -> CompareFunc -> Interpreter TypedValue
interpretExpCompare e1 e2 (s, f) = do
  n1 <- interpretExpectInt e1
  n2 <- interpretExpectInt e2
  return $ VBool $ f n1 n2

interpretExpOperation :: Exp -> Exp -> Predicate -> IntFunc -> Interpreter TypedValue
interpretExpOperation e1 e2 p (name, f) = do
  n1 <- interpretExpectInt e1
  n2 <- interpretExpectInt e2
  if (p n1 n2)
    then return $ VInt $ f n1 n2
    else throwError Arithmetic

-- -- Helper functions

checkObjectInterfaces :: Obj -> Interface_specifier -> Interpreter Bool
checkObjectInterfaces m i = logFunction Store "checkInterfaces" (m, i) (_internal m i) where
  _internal m (InterObj []) = return True
  _internal m (InterObj (Interface (Name n):t)) = 
    case Data.Map.lookup n m of
      Nothing -> return False
      Just _ -> checkObjectInterfaces m (InterObj t)


      
-- TODO
ensureCorrectType :: TypeAll -> TypedValue -> Interpreter TypedValue
ensureCorrectType tt tv = logFunction Store "ensureCorrectType" (tt, tv) (_internal tt tv) where
  _internal (TypeNFunc (TypeInt)) (VInt n) = return $ VInt $ n
  _internal (TypeNFunc (TypeBool)) (VBool n) = return $ VBool $ n
  _internal (TypeNFunc (TypeChar)) (VChar n) = return $ VChar $ n
  _internal (TypeNFunc (TypeObj i)) (VObj (LocObj l)) = do
    variables <- getVariables
    let pobj = Data.Map.lookup (LocObj l) variables
    case pobj of
      Nothing -> return $ VObj $ LocNoObj
      (Just obj) -> do
        corr <- checkObjectInterfaces obj i
        if corr
          then return $ VObj $ LocObj $ l
          else throwError WrongType
  _internal (TypeNFunc (TypeObj _)) (VObj LocNoObj) = return $ VObj $ LocNoObj
  _internal (TypeNFunc (TypeVoid)) (VObj LocNoObj) = return $ VObj $ LocNoObj
  _internal (TypeFunc retTp (InterObj inter1)) (VObj LocNoObj) = return $ VObj $ LocNoObj
  _internal (TypeFunc retTp (InterObj inter1)) (VFunc func) = do
      let ret = funcRetType func
      let (InterObj inter2) = funcInType func
      interfaceSatisfiedBy inter1 inter2
      if retTp == ret
        then return (VFunc func)
        else throwError WrongType
    where
      interfaceSatisfiedBy :: [Interface_list] -> [Interface_list] -> Interpreter ()
      interfaceSatisfiedBy [] t2 = return ()
      interfaceSatisfiedBy (h:t) t2 = do
        if elem h t2
          then interfaceSatisfiedBy t t2
          else throwError WrongType
  _internal _ _ = throwError WrongType
  
ensureValidLoc :: Loc -> Interpreter Loc
ensureValidLoc l = do
  (VObj l2) <- ensureValidValue $ (VObj l)
  return l2
  
ensureValidValue :: TypedValue -> Interpreter TypedValue
ensureValidValue tt = logFunction Store "ensureValidValue" tt (_internal tt) where
  _internal (VObj (LocObj l)) = do
    variables <- getVariables
    let pobj = Data.Map.lookup (LocObj l) variables
    case pobj of
      Nothing -> return $ VObj $ LocNoObj
      (Just obj) -> return $ VObj $ LocObj $ l
  _internal t = return t

filterObject :: Interface_specifier -> [Loc] -> Interpreter [Loc]
filterObject inter l = _filter l [] where
  _filter [] a = return $ reverse $ a
  _filter (h:t) a = do
    variables <- getVariables
    object <- eitherLookup h $ variables
    correct <- checkObjectInterfaces object inter
    if correct
      then _filter t (h:a)
      else _filter t a
  
interpretBlockInterfacesFunc :: String -> Loc -> Loc -> Interface_specifier -> [Stmt] -> Maybe (Interpreter ()) -> Interpreter ()
interpretBlockInterfacesFunc name act prev inter stmt funcPrep =
  interpretBlockInterfacesAll name act prev inter stmt funcPrep Nothing

interpretBlockInterfacesAll :: String -> Loc -> Loc -> Interface_specifier -> [Stmt] -> Maybe (Interpreter ()) -> Maybe (Interpreter ()) -> Interpreter ()
interpretBlockInterfacesAll name act prev inter stmt funcPrep funcInner = do
  variables <- getVariables
  object <- eitherLookup act $ variables
  correct <- checkObjectInterfaces object inter
  if correct
    then interpretBlock name act prev stmt funcPrep funcInner
    else return () -- TODO: Fill Error code
    
interpretBlockInterfaces :: String -> Loc -> Interface_specifier -> [Stmt] -> Interpreter ()
interpretBlockInterfaces name loc inter stmt = do
  curr <- getCurrentLoc
  interpretBlockInterfacesFunc name loc curr inter stmt Nothing

interpretBlock :: String -> Loc -> Loc -> [Stmt] -> Maybe(Interpreter ()) -> Maybe(Interpreter ()) -> Interpreter ()
interpretBlock name curr prev stmts funcPrep funcInner = do
  stackIndex <- getStackNumb
  stackPush name curr prev
  -- TODO: Repeat not working . Probably it should be pushed here.
  callCC (\repeat -> do
    stackFillRepeat $ repeat
    --modify $ \s -> s {dbReturnCC = (Just repeat)} -- Using: stackFillRepeat $ repeat
    return ())
  case funcPrep of
    Nothing -> return ()
    Just f -> f
  state <- get
  let dbi = dbDebugIndent state
  let prevExc = dbException $ state
  --let (Just repeat) = dbReturnCC $ state
  callCC $ (\escape -> do
    stackFillEscape $ escape
    --stackFillRepeat $ repeat
    case funcInner of
      Nothing -> return ()
      Just f -> f
    interpretStmts stmts
    )
  modify $ \s -> s{dbDebugIndent = dbi, dbException = prevExc}
  stackRestore stackIndex

addField :: String -> TypeAll -> ObjModifyFunc
addField name (TypeNFunc TypeInt) = Data.Map.insert name (VInt 0)
addField name (TypeNFunc TypeBool) = Data.Map.insert name (VBool False)
addField name (TypeNFunc TypeChar) = Data.Map.insert name (VChar ' ')
addField name (TypeNFunc (TypeObj _)) = Data.Map.insert name (VObj LocNoObj)
addField name (TypeNFunc (TypeVoid)) = Data.Map.insert name (VObj LocNoObj)
addField name (TypeFunc _ _) = Data.Map.insert name (VObj LocNoObj)

truePredicate _ _ = True
non0Second _ 0 = False
non0Second _ _ = True

interpretExpectInt e = interpretExp e >>= ensureTypeInt
interpretExpectBool e = interpretExp e >>= ensureTypeBool
interpretExpectLoc e = interpretExp e >>= ensureTypeLoc
interpretExpectChar e = interpretExp e >>= ensureTypeChar

ensureTypeInt :: TypedValue -> Interpreter Int
ensureTypeInt (VInt n) = return n
ensureTypeInt t = throwError WrongType
--  $ "Got " ++ (show t) ++ " where expected value of type Int"

ensureTypeBool :: TypedValue -> Interpreter Bool
ensureTypeBool (VBool n) = return n
ensureTypeBool t = throwError WrongType

ensureTypeLoc :: TypedValue -> Interpreter Loc
ensureTypeLoc (VObj l) = return l
ensureTypeLoc t = throwError WrongType
--  $ "Got " ++ (show t) ++ " where expected value of type Bool"

ensureTypeChar :: TypedValue -> Interpreter Char
ensureTypeChar (VChar c) = return c
ensureTypeChar t = throwError WrongType


------ Store functions

-- Shortcut getters

getVariables :: Interpreter (Map Loc Obj)
getVariables = get >>= return . stVariables

getStack :: Interpreter Stack
getStack = get >>= return . stStack

getFunctions :: Interpreter (Map String TypedFunc)
getFunctions = get >>= return . stFunction

getStackHead :: Interpreter StackEntry
getStackHead = do
  stack <- getStack
  case stack of
    [] -> throwError EndOfStack
    (h:t) -> return $ h
    
getStackNumb :: Interpreter Int
getStackNumb = do
  stackFrame <- getStackHead
  return $ stackNumber $ stackFrame

-- Stack Operations

modifyStackHead :: (StackEntry -> StackEntry) -> Interpreter ()
modifyStackHead modif = do
  stack <- getStack
  case stack of
    [] -> throwError EndOfStack
    (h:t) -> modify $ \s -> s { stStack = (modif h:t)}

stackRestore n = do
    ldebug Store $ "Restoring stack to " ++ (show n)
    internal n
  where
    internal n = do
      stackFrame <- getStackHead
      if stackNumber stackFrame <= n
        then return ()
        else do
          stackPop
          internal n

stackPop :: Interpreter ()
stackPop = logFunction Store "stackPop" () _stackPop where
  _stackPop = do
    state <- get
    -- Deleting local variables
    stackFrame <- getStackHead
    ldebug Store $ "Popping stack frame:" ++ (show stackFrame)
    let locals = stackLocals $ stackFrame
    variables <- getVariables
    currentLoc <- getCurrentLoc
    case Data.Map.lookup currentLoc variables of
      Just currentObj -> do
        currentObj <- eitherLookup currentLoc variables
        changedObj <- deleteLocals locals currentObj
        let newVariables = Data.Map.insert currentLoc changedObj variables
        -- Popping stack
        (h:t) <- getStack
        put $ state { stVariables = newVariables, stStack = t}
      Nothing -> do
        -- Popping stack - no current
        (h:t) <- getStack
        put $ state {stStack = t}
        
    
  deleteLocals [] obj = return $ obj
  deleteLocals (h:t) obj = deleteLocals t $ Data.Map.delete h obj

stackPush :: String -> Loc -> Loc -> Interpreter ()
stackPush name loc prev = logFunction Store "stackPush" () _stackPush where
  _stackPush = do
    currentStack <- getStack
    numb <- case currentStack of
      [] -> return 0
      h:t -> return $ 1 + (stackNumber h)
    let entry = StackEntry {
          stackName = name,
          stackCurrent = loc,
          stackLocals = [],
          stackPrev = prev,
          stackReturn = Nothing,
          stackEscape = Nothing,
          stackRepeat = Nothing,
          stackNumber = numb
        }
    case currentStack of
      [] -> do
        let newStack = entry : currentStack
        ldebug Store $ show entry
        modify $ \s -> s { stStack = newStack }
      h:t -> do
        let oldEscape = stackReturn h
        let escapedEntry = entry {stackReturn = oldEscape}
        let newStack = escapedEntry : currentStack
        modify $ \s -> s { stStack = newStack }
    stackFrame <- getStackHead
    ldebug Store $ show stackFrame

stackFillEscape :: (() -> Interpreter ()) -> Interpreter ()
stackFillEscape esc = modifyStackHead $ \s -> s { stackEscape = Just esc }
stackFillRepeat rep = modifyStackHead $ \s -> s { stackRepeat = Just rep }
stackFillReturn ret = modifyStackHead $ \s -> s { stackReturn = Just ret }

stashReturns = do
  stack <- getStackHead
  return (stackEscape stack, stackRepeat stack, stackReturn stack)
  
restoreReturns (esc, rep, ret) = do
  modifyStackHead $ \s -> s { stackEscape = esc }
  modifyStackHead $ \s -> s { stackRepeat = rep }
  modifyStackHead $ \s -> s { stackReturn = ret }

  
  
-- Register operations

getRegisterType :: String -> Interpreter TypeAll
getRegisterType name = logFunction Store "getRegisterType" name _internal where
  _internal = do
    state <- get
    let registers = stRegister $ state
    eitherLookup name registers
    
tryGetRegisterType :: String -> Interpreter (Maybe TypeAll)
tryGetRegisterType name =  logFunction Store "tryGetRegisterType" name _internal where
  _internal = catchError makeJust (\_ -> return Nothing)
  makeJust = getRegisterType name >>= return . Just
  
-- Object Operations

getObjectModifyState :: String -> Loc -> Interpreter ()
getObjectModifyState s loc =
  if s == "base_prev"
    then stackPop 
    else modifyStack s loc >> return ()
  where
  modifyStack s loc = do
    stack <- getStack
    case stack of
      (h:t) -> do
        stackPop
        modifyStack s loc
      [] -> stackPush "internal" loc LocNoObj

getObjectValue :: Object -> Interpreter TypedValue
getObjectValue f = logFunction Store "getObjectValue" f (_getObject f) where
  _getObject f = case f of
    (ObjField field) -> getFieldValue field
    ObjCurr -> do
      state <- get
      stackFrame <- getStackHead
      return $ VObj $ stackCurrent $ stackFrame
  getFieldValue f = logFunction Store "getField" f (_getField f)
  _getField f = case f of
    (FieldSingle (Name name)) -> fetchObject name
    (FieldMany (Name name) field) -> do
      obj <- fetchObject name
      case obj of
        (VObj (LocObj n)) -> do
          let loc = LocObj n
          state <- get
          getObjectModifyState name loc
          r <- getFieldValue field
          modify $ (\s -> state)
          return r
        (VObj LocNoObj) -> throwError NoObject
        otherwise -> throwError WrongType
  fetchObject name = do
    variables <- getVariables
    stackHead <- getStackHead
    let loc = stackCurrent stackHead
    current <- eitherLookup loc $ variables
    if name == "base_prev"
      then return $ VObj $ stackPrev $ stackHead
      else eitherLookup name current >>= return

getObject :: Loc -> Interpreter Obj
getObject loc = do
  variables <- getVariables
  object <- eitherLookup loc variables
  return object

getObjectLoc :: Object -> Interpreter Loc
getObjectLoc obj = logFunction Store "getObjectLoc" obj _getLoc where
  _getLoc = do
    val <- getObjectValue obj
    case val of
      (VObj (LocObj n)) -> return $ LocObj $ n
      otherwise -> throwError $ NoObject
      
getCurrentLoc :: Interpreter Loc
getCurrentLoc = getObjectLoc ObjCurr
      
type ObjModifyFunc = (Obj -> Obj)
  
modifyObject :: Loc -> ObjModifyFunc -> Interpreter ()
modifyObject loc func = logFunction Store "modifyObject" loc _internal where
  _internal = do
    variables <- getVariables
    object <- eitherLookup loc $ variables
    let newVariables = Data.Map.insert loc (func object) $ variables
    modify $ \s -> s{stVariables = newVariables}

modifyCurrent :: ObjModifyFunc -> Interpreter ()
modifyCurrent f = do
    objectLoc <- getCurrentLoc
    modifyObject objectLoc f


-- Helper Functions

eitherLookup :: Ord k => k -> Map k a -> Interpreter a
eitherLookup f m = case Data.Map.lookup f m of
  Nothing -> throwError NoObject
  Just x -> return x

eitherJust :: Maybe a -> Interpreter a
eitherJust f = case f of
  Nothing -> throwError NoObject
  Just x -> return x