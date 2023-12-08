{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Use const" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Main (main) where

import Control.Monad (ap, foldM, foldM_, liftM)
import Data.Foldable (foldlM)
import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Debug.Trace
import Text.ParserCombinators.Parsec

data Statement = Expression OExpression | Binding Binding

-- | Expressions evaluate to something tangible
data OExpression
  = -- concrete value
    ENum Int
  | EBool Bool
  | IfElse OExpression OExpression OExpression
  | -- Types are first-class values
    EType OType
  | -- Expression captures
    Quote OExpression
  | Equal OExpression OExpression
  | -- Functions
    Lambda [String] OEnv OExpression
  | NativeCall String
  | Call OExpression [OExpression]
  | TypeOf OExpression
  | -- Names
    Let [Binding] OExpression
  | Name String
  | RuntimeError String
  deriving (Eq, Ord)

instance Show OExpression where
  show (ENum n) = show n
  show (EBool b) = show b
  show (IfElse cond trueExpr falseExpr) = "if " ++ show cond ++ " then " ++ show trueExpr ++ " else " ++ show falseExpr
  show (EType typ) = "[type {" ++ show typ ++ "}]"
  show (Let bindings expr) = "let " ++ (List.map show bindings & unwords) ++ " in  \x1b[1m" ++ show expr ++ "\x1b[22m"
  show (Name n) = n
  show (RuntimeError e) = "RuntimeError: " ++ e
  show (NativeCall name) = "[Native fn `" ++ name ++ "`]"
  show (Call fn args) = "(" ++ show fn ++ " " ++ (List.map show args & unwords) ++ ")"
  show (Lambda args _ body) = "(\\" ++ unwords args ++ " -> " ++ show body ++ ")"
  show (Quote expr) = "quote(" ++ show expr ++ ")"
  show (TypeOf expr) = "typeof(" ++ show expr ++ ")"
  show (Equal a b) = "(" ++ show a ++ " == " ++ show b ++ ")"

-- | Bindings only modify the environment
data Binding
  = BindValue String OExpression
  | BindType OExpression OType
  deriving (Eq, Ord)

instance Show Binding where
  show (BindValue name expr) = name ++ " = " ++ show expr ++ ";"
  show (BindType name expr) = show name ++ " := " ++ show expr

data OType
  = TNum
  | TBool
  | -- | TFunction [OType] OType
    TApply OType [OType]
  | TType -- is of type: Type
  | TAny -- can litarally be anything
  | AnyOf [OType]
  | AllOf [OType]
  | TVar String
  | TQuote
  | TypeError String
  | TExpression OExpression
  deriving (Show, Eq, Ord)

data OEnv
  = Env (Map.Map String OExpression) (Map.Map OExpression OType) (Maybe OEnv)
  deriving (Eq, Ord)

replace :: Char -> String -> String -> String
replace from to [] = []
replace from to (x : xs) =
  if x == from
    then to ++ replace from to xs
    else x : replace from to xs

instance Show OEnv where
  show (Env bindings tBindings mParent) =
    let parentStr = maybe "" (replace '\n' "\n   " . show) mParent
     in Map.foldlWithKey (\s k v -> s ++ "  " ++ k ++ ": " ++ show v ++ "\n") "E:\n" bindings
          ++ "  parent "
          ++ parentStr

makeOakVersion :: (a -> OExpression) -> OType -> String -> (Int -> Int -> a) -> (String, ([OExpression] -> OExpression, OType))
makeOakVersion toExpr typ name fn =
  let builtinFn [ENum a, ENum b] = toExpr (fn a b)
      builtinFn exprs = (error $ "Expected two numbers for " ++ name ++ ", got " ++ show exprs)

      (lambdaEnv, _) =
        compute
          _emptyEnv
          ( do
              evalBinding (BindType (Name "x") TNum)
              evalBinding (BindType (Name "y") TNum)
          )

      typL = TExpression (Lambda ["x", "y"] _emptyEnv (EType typ))
   in (name, (builtinFn, typL))

nativeFns :: [(String, ([OExpression] -> OExpression, OType))]
nativeFns =
  [ makeOakVersion ENum TNum "+" (+),
    makeOakVersion ENum TNum "-" (-),
    makeOakVersion ENum TNum "*" (*),
    makeOakVersion EBool TBool "<" (<),
    makeOakVersion EBool TBool ">" (>),
    makeOakVersion EBool TBool ">=" (>=),
    makeOakVersion EBool TBool "<=" (<=),
    makeOakVersion EBool TBool "==" (==)
  ]

nativeCalls :: Map.Map String ([OExpression] -> OExpression, OType)
nativeCalls =
  Map.fromList nativeFns

debugPipe :: (Show b) => String -> b -> b
debugPipe name x = trace (name ++ ": " ++ show x) x

_emptyEnv :: OEnv
_emptyEnv =
  Env Map.empty Map.empty Nothing

defaultEnv :: OEnv
defaultEnv =
  let bindingsMonad =
        foldM_
          ( \_ (n, (fn, typ)) ->
              do
                evalBinding (BindType (Name n) typ)
                evalBinding (BindType (NativeCall n) typ)
                evalBinding (BindValue n (NativeCall n))
          )
          ()
          nativeFns
      (env, _) = compute _emptyEnv bindingsMonad
   in env

makeChildEnvOf :: OEnv -> OEnv
makeChildEnvOf env = Env Map.empty Map.empty (Just env)

makeChildEnv :: Computation ()
makeChildEnv =
  Computation (\env -> (makeChildEnvOf env, ()))

exitEnvToParent :: Computation ()
exitEnvToParent =
  Computation (\(Env _ _ mParent) -> (mParent & Maybe.fromJust, ()))

currentEnv :: Computation OEnv
currentEnv =
  Computation (\env -> (env, env))

inExistingParent :: Computation a -> Computation a
inExistingParent computation =
  Computation
    ( \env@(Env b tb mParent) ->
        let (newParent, res) = compute (mParent & Maybe.fromJust) computation
         in (Env b tb (Just newParent), res)
    )

inEphemeralChildEnv :: Computation b -> Computation b
inEphemeralChildEnv computation =
  do
    makeChildEnv
    res <- computation
    exitEnvToParent
    return res

setParent :: OEnv -> OEnv -> OEnv
child `setParent` parent =
  case child of
    Env bs ts (Just p) -> Env bs ts (Just $ p `setParent` parent)
    Env bs ts Nothing -> Env bs ts (Just parent)

inferDirectType :: OExpression -> Computation OType
inferDirectType expression =
  ( case expression & debugPipe "--- inferType start" of
      ENum _ -> return TNum
      EBool _ -> return TBool
      IfElse cond trueExpr falseExpr ->
        do
          inferDirectType cond -- this happens last because of hints we could get from above... ugh
          inferDirectType trueExpr
          inferDirectType falseExpr
          trueType <- inferDirectType trueExpr
          falseType <- inferDirectType falseExpr
          condType <- inferDirectType cond -- this happens last because of hints we could get from above... ugh
          if condType `isSubset` TBool
            then simplifyType $ TExpression (IfElse cond (EType trueType) (EType falseType))
            else return $ TypeError ("conditional expression " ++ show cond ++ " is not a boolean. Got " ++ show condType)
      EType _ -> return TType
      Quote _ -> return TQuote
      RuntimeError _ -> return TAny
      Name n ->
        do
          mt <- resolveType (Name n)
          let t = mt & Maybe.fromMaybe (TExpression (Name n))
          simplifyType t
      NativeCall n ->
        do
          t <- resolveType (Name n)
          return $ t & Maybe.fromJust
      Lambda args _ body ->
        do
          makeChildEnv & trace (" >> inferType going to child env in " ++ show expression)
          foldM_ (\_ n -> evalBinding (BindType (Name n) (TExpression (Name n)))) () args
          bodyType <- inferDirectType body
          argTypes <-
            foldM
              ( \ts a ->
                  do
                    t <- resolveType (Name a)
                    simpleT <- simplifyType (t & Maybe.fromJust)
                    return (simpleT : ts)
              )
              []
              (List.reverse args)
          lenv <- currentEnv
          exitEnvToParent & trace (" << inferType going to parent env in " ++ show expression)
          simplifyType $ TExpression (Lambda args lenv (EType bodyType))
      Let [] expr -> inferDirectType expr
      Let ((BindType texpr typ) : bs) expr ->
        do
          -- TODO check if there's a bound value and the type matches
          evalBinding (BindType texpr TType)
          inferDirectType (Let bs expr)
      Let ((BindValue n nVal) : bs) expr ->
        do
          evalBinding (BindValue n nVal)
          tp <- inferDirectType nVal
          evalBinding (BindType (Name n) tp)
          inferDirectType (Let bs expr)
      Call fn args ->
        do
          fnType_ <- inferDirectType fn >>= simplifyType
          argTypes_ <- foldM (\ts a -> do t <- inferDirectType a; return (t : ts)) [] args
          let (fnType, argTypes) = (fnType_, argTypes_) & debugPipe "   inferType: (fnType, argType)"
          case fnType of
            TExpression (Lambda namedArguments lenv _) ->
              do
                let (argMatches_, _) = zipAll (args, namedArguments)
                let argMatches = argMatches_ & debugPipe "   inferType: argMatches "
                foldM_
                  ( \_ (argValue, argName) -> do
                      let b =
                            argValue
                              & debugPipe
                                ("   inferType, in " ++ show expression ++ " restricting " ++ show argValue ++ " with " ++ show argName)
                      mArgType <- resolveType (Name argName)
                      let argType = mArgType & Maybe.fromMaybe (TVar argName)
                      addTypeRestrictionToExistingName b argType
                  )
                  ()
                  argMatches
            _ ->
              return (() & debugPipe ("   fnType " ++ show fnType ++ " argTypes " ++ show argTypes))

          let rawType = TApply (fnType & debugPipe "inferType: fnType") (argTypes & debugPipe "inferType: argTypes")
          simplifyType rawType
  )
    & fmap (debugPipe ("\n=== inferType of " ++ show expression ++ "\n  "))

evalType :: OExpression -> Computation OExpression
evalType expr =
  ( case expr & debugPipe "--- evalType of" of
      ENum _ -> return $ EType TNum
      EBool _ -> return $ EType TBool
      Name n ->
        do
          mType <- resolveType (Name n)
          case mType of
            Just typ -> return $ EType typ
            Nothing ->
              do
                mExpr <- resolveName n
                case mExpr of
                  Just expr -> evalType expr
                  _ -> return $ RuntimeError $ "Can't resolve name " ++ n
      Let bindings e ->
        eval (Let bindings (TypeOf e))
      NativeCall n ->
        do
          t <- resolveType (NativeCall n) & trace "resolveType native"
          evalType $ EType (t & Maybe.fromJust) -- TODO: this is hacky
      EType (TExpression expr) ->
        eval expr
      Call fn args ->
        do
          fnType <- evalType fn
          argTypes <- foldM (\ts a -> do t <- evalType a; return (t : ts)) [] (List.reverse args)
          let callType = Call fnType args
          let withGuards =  addTypeRestriction (fnType, EType TAny) callType
          eval withGuards
      Lambda argNames lenv lbody ->
        eval (Lambda argNames lenv (TypeOf lbody))
      IfElse cond trueExpr falseExpr ->
        do
          condType <- evalType cond
          let typeExpr = IfElse cond (TypeOf trueExpr) (TypeOf falseExpr)
          eval $ addTypeRestriction (cond, EType TBool) typeExpr
      EType t -> return $ EType TType
      _ -> return $ RuntimeError "unimplemented evalType"
  )
    & fmap (debugPipe ("=== evalType of " ++ show expr))

addTypeRestriction :: (OExpression, OExpression) -> OExpression -> OExpression
addTypeRestriction (typedExpr, exprType) retExpr =
  IfElse
    (Equal exprType (TypeOf typedExpr))
    retExpr
    (EType (TypeError $ "TypeError, expected " ++ show exprType ++ " but got " ++ show typedExpr))

evalEqual :: OExpression -> OExpression -> Computation Bool
evalEqual (EType TAny) (EType _) = return True
evalEqual (EType _) (EType TAny) = return True
evalEqual exprA exprB =
  if exprA == exprB
    then return True
    else do
      a <- eval exprA
      b <- eval exprA
      return $ a == b

-- TAny `isSubset` t = True
isSubset :: OType -> OType -> Bool
t `isSubset` TAny = True
t `isSubset` (TVar _) = True
(TVar _) `isSubset` t = True
-- t `isSubset` (TApply (TVar _) _) = True
(TApply (TVar _) _) `isSubset` t = True
t `isSubset` (AllOf allTypes) = List.all (\a -> t `isSubset` a) allTypes
(AllOf alltypes) `isSubset` t = List.any (\a -> a `isSubset` t) alltypes
t `isSubset` (AnyOf anyTypes) = List.any (\a -> t `isSubset` a) anyTypes
(AnyOf anyTypes) `isSubset` t = List.all (\a -> a `isSubset` t) anyTypes
t `isSubset` u = t == u

simplifyType :: OType -> Computation OType
simplifyType typ =
  case typ of
    TExpression (IfElse cond (EType trueType) (EType falseType)) ->
      do
        simpleTrue <- simplifyType trueType
        simpleFalse <- simplifyType falseType
        if simpleTrue == simpleFalse
          then return simpleTrue
          else return typ
    -- TApply (TExpression (Lambda [] _ retType)) [] ->
    --   simplifyType retType
    TExpression (EType t) ->
      return t
    TApply (TExpression (Lambda argNames lenv (EType (TExpression expr)))) argVals ->
      do
        ret <- eval (Call (Lambda argNames lenv expr) (argVals & List.map EType))
        return (TExpression ret)
    TApply TAny _ ->
      return TAny
    AllOf types ->
      let allTypes =
            List.concatMap
              ( \t -> case t of
                  AllOf subTs -> subTs
                  _ -> [t]
              )
              types
       in return $ AllOf (List.nub allTypes)
    TVar name ->
      do
        realType <- resolveType (Name name)
        return (realType & Maybe.fromMaybe typ)
    -- TApply (TExpression (Lambda (fnArgType : argTypes) _ retType)) (callArgType : callTypes) ->
    --   do
    --     fnSimple <- simplifyType fnArgType
    --     argSimple <- simplifyType callArgType
    --     if argSimple `isSubset` fnSimple
    --       then simplifyType $ TApply (TFunction argTypes retType) callTypes
    --       else
    --         return $
    --           TypeError ("provided argument is of type " ++ show argSimple ++ " not a subset of expected type " ++ show fnSimple)
    --             & debugPipe ("simplifyType. In " ++ show typ ++ ", " ++ show argSimple ++ " is not subset of " ++ show fnSimple)
    -- AllOf (t1_ : (t2_ : ts)) ->
    --   do
    --     t1 <- simplifyType t1_
    --     t2 <- simplifyType t2_
    --     if t1 `isSubset` t2
    --       then return $ AllOf (t1 : ts)
    --       else
    --         if t2 `isSubset` t1
    --           then return $ AllOf (t2 : ts)
    --           else return typ
    _ -> return typ

-- checkType :: OType -> OExpression -> OEnv -> Bool
-- checkType otype expression env =
--   (inferDirectType expression env & snd) `isSubset` otype

newtype Computation a = Computation {runInEnv :: OEnv -> (OEnv, a)}

compute :: OEnv -> Computation a -> (OEnv, a)
compute env (Computation fn) = fn env

instance Functor Computation where
  fmap = liftM

instance Applicative Computation where
  (<*>) = ap

  pure value = Computation (\e -> (e, value))

instance Monad Computation where
  Computation compA >>= fn =
    Computation $
      \env ->
        let (newEnv, newRes) = compA env
            Computation nextCompFn = fn newRes
         in nextCompFn newEnv

zipAll :: ([a], [b]) -> ([(a, b)], ([a], [b]))
zipAll (as, []) = ([], (as, []))
zipAll ([], bs) = ([], ([], bs))
zipAll (a : as, b : bs) =
  let (pairs, rests) = zipAll (as, bs)
   in ((a, b) : pairs, rests)

-- | Returns the value with no side effect on the environment
valuate :: OExpression -> OEnv -> Computation OExpression
valuate expr env =
  do
    let (_, res) = compute env (eval expr)
    return res

eval :: OExpression -> Computation OExpression
eval expr =
  ( case expr & debugPipe "--- eval" of
      IfElse condExpr trueExpr falseExpr ->
        do
          condValue <- eval condExpr
          case condValue of
            (EBool True) -> eval trueExpr
            (EBool False) -> eval falseExpr
            _ -> return (RuntimeError (show condValue ++ " isn't a boolean"))
      Name n ->
        do
          mRes <- resolveAndEval n
          let res = mRes & Maybe.fromMaybe (RuntimeError ("Can't resolve name " ++ n))
          return res
      Lambda args _ body -> Computation (\env -> (env, Lambda args env body)) -- todo verify all names bound
      Let bindings expr ->
        do
          foldM_ (const evalBinding) () bindings
          eval expr
      Call (Lambda largs lenv lbody) args ->
        do
          let (bindings, (rlargs, rargs)) = zipAll (largs, args)
          values <- foldM (\res (n, a) -> do arg <- eval a; return $ (n, arg) : res) [] (bindings & List.reverse)
          let (newEnv, _) =
                compute
                  (makeChildEnvOf lenv)
                  (foldM_ (\_ (n, x) -> evalBinding (BindValue n x)) () values)
          case (rlargs, rargs) of
            ([], []) -> valuate lbody newEnv
            (rlargs, []) -> eval (Lambda rlargs newEnv lbody)
            ([], rargs) -> do
              newBody <- valuate lbody newEnv
              eval (Call newBody rargs)
      Call (NativeCall name) args ->
        let (fn, _) = Map.lookup name nativeCalls & Maybe.fromJust
         in do
              -- TODO why does this flip?
              vargs <- foldlM (\res a -> do arg <- eval a; return $ arg : res) [] (args & List.reverse)
              let res = fn vargs
              eval res
      Call fnExpr args ->
        do
          fn <- eval fnExpr
          eval (Call fn args)
      RuntimeError e -> error (show expr)
      Equal a b ->
        do
          isEqual <- evalEqual a b
          return $ EBool isEqual
      TypeOf e ->
        do
          mt <- resolveType expr
          case mt of
            Just t -> return $ EType t
            _ -> evalType e
      _ -> return expr
  )
    & fmap (debugPipe ("=== eval of " ++ show expr))

hasBinding :: String -> OEnv -> Bool
hasBinding name (Env bindingMap _ parentEnv) =
  Map.member name bindingMap || maybe False (hasBinding name) parentEnv

hasTypeBinding :: OExpression -> Computation Bool
hasTypeBinding expr =
  Computation
    ( \env@(Env _ tBindings parentEnv) ->
        if Map.member expr tBindings
          then (env, True)
          else case parentEnv of
            Nothing -> (env, False)
            Just pEnv ->
              let (_, hasT) = compute pEnv (hasTypeBinding expr)
               in (env, hasT)
    )

orElse :: Maybe a -> Maybe a -> Maybe a
orElse _ a@(Just _) = a
orElse b _ = b

resolveType :: OExpression -> Computation (Maybe OType)
resolveType expr =
  Computation
    ( \env@(Env bindings tBindings maybeParent) ->
        case Map.lookup expr tBindings of
          Just typ ->
            (env, Just typ)
          Nothing ->
            case maybeParent of
              Nothing -> (env, Nothing)
              Just parent ->
                (env, compute parent (resolveType expr) & snd)
    )

resolveName :: String -> Computation (Maybe OExpression)
resolveName name =
  Computation
    ( \env@(Env bindings _ maybeParent) ->
        case Map.lookup name bindings of
          Just expr ->
            (env, Just expr)
          Nothing ->
            case maybeParent of
              Nothing -> (env, Nothing)
              Just parent ->
                (env, compute parent (resolveName name) & snd)
    )

resolveAndEval :: String -> Computation (Maybe OExpression)
resolveAndEval name =
  Computation
    ( \env@(Env bindings tBinds maybeParent) ->
        let mexpr = bindings & Map.lookup name
         in case mexpr of
              Just expr ->
                let (_, res) = compute env (eval expr)
                    newBindings = bindings & Map.insert name res
                 in (Env newBindings tBinds maybeParent, Just res)
              Nothing ->
                case maybeParent of
                  Nothing -> (env, Nothing)
                  Just parent ->
                    let (newParent, res) = compute parent (resolveAndEval name)
                     in (Env bindings tBinds (Just newParent), res)
    )

evalBinding :: Binding -> Computation ()
evalBinding bind =
  Computation
    ( \env@(Env bindings tBindings maybeParent) ->
        case bind of
          BindValue name expr ->
            if Map.member name bindings
              then error $ "Can't overwrite existing value binding " ++ name
              else (Env (bindings & Map.insert name expr) tBindings maybeParent, ())
          BindType name typ ->
            let newType = case Map.lookup name tBindings of
                  Just existingType -> compute env (simplifyType (AllOf [typ, existingType])) & snd
                  Nothing -> typ
             in (Env bindings (tBindings & Map.insert name newType) maybeParent, ())
    )

hasValueBinding :: String -> Computation Bool
hasValueBinding name =
  Computation (\env@(Env bindings _ _) -> (env, bindings & Map.member name))

hasName :: String -> Computation Bool
hasName name =
  Computation (\env@(Env bindings tBindings _) -> (env, Map.member name bindings || Map.member (Name name) tBindings))

addTypeRestrictionToExistingName :: OExpression -> OType -> Computation ()
addTypeRestrictionToExistingName expr typ =
  case expr & debugPipe (" ** addTypeRestrictionToExisting: type = " ++ show typ ++ " for ") of
    Name name ->
      do
        nameExists <- hasName name

        if nameExists & debugPipe (" ** addTypeRestriction: " ++ name ++ " exists? ")
          then evalBinding (BindType expr typ)
          else inExistingParent (addTypeRestrictionToExistingName expr typ)
    _ -> return ()

set :: String -> OExpression -> Binding
set = BindValue

num :: Int -> OExpression
num = ENum

n :: String -> OExpression
n = Name

nn :: String -> OExpression
nn = NativeCall

lambda :: [String] -> OExpression -> OExpression
lambda args = Lambda args defaultEnv

call :: String -> [String] -> OExpression
call fnName argNames = Call (Name fnName) (List.map Name argNames)

calln :: String -> [String] -> OExpression
calln fnName argNames = Call (NativeCall fnName) (List.map Name argNames)

main :: IO ()
main =
  let expr =
        Let
          [ set "x" (num 3),
            -- set "y" (calln "+" ["x", "x"]),
            set "y" (call "add" ["x", "x"]),
            set "add" (lambda ["x", "y"] (Call (nn "+") [n "x", n "y"])),
            set "id" (lambda ["x"] (n "x")),
            set "omega" (lambda ["x"] (call "x" ["x"])),
            set
              "fact"
              ( lambda
                  ["x"]
                  ( IfElse
                      (Call (nn "<=") [n "x", num 1])
                      (EBool False)
                      -- (IfElse (Call (nn "<=") [n "x", num 0]) (EBool False) (num 1))
                      -- (num 1)
                      (Call (nn "*") [n "x", Call (n "fact") [Call (nn "-") [n "x", num 1]]])
                  )
              )
          ]
          -- (NativeCall "+")
          -- (Call (NativeCall "+") [Name "x"])
          -- (Call (NativeCall "+") [Name "x", Name "y"])
          -- (Name "y")
          -- (num 2)
          -- (call "fact" ["y"])
          -- (call "add" ["y", "y"])
          -- (n "id")
          -- (Call (n "id") [num 3])
          -- (call "id" ["id"])
          -- (Call (Call (n "id") [n "id"]) [num 3])
          -- (Call (n "fact") [num 20])
          -- (n "omega")
          -- (call "omega" ["omega"])
          -- (Call (n "fact") [num (-2)])
          (Call (n "fact") [EBool True])
          -- (n "fact")

      _ = 0
   in do
        putStrLn ("> \x1b[1m" ++ show expr ++ "\x1b[22m")
        -- let (_, exprType) = compute defaultEnv (evalType expr)
        -- putStrLn (" := \x1b[1m" ++ show exprType ++ "\x1b[22m")
        -- let (_, res) = compute defaultEnv (eval expr)
        -- putStrLn ("  = " ++ show res)
        putStrLn ""

        putStrLn "================"
        -- let (_, exprType) = compute defaultEnv (inferDirectType expr >>= simplifyType)
        -- putStrLn (" := \x1b[1m" ++ show exprType ++ "\x1b[22m")
        let (_, exprType) = compute defaultEnv (evalType expr)
        putStrLn (" := \x1b[1m" ++ show exprType ++ "\x1b[22m")
        putStrLn ""
        putStrLn "done"
