{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Use const" #-}
module Main (main) where

import Control.Monad (ap, liftM)
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
    ENumber Int
  | EBool Bool
  | IfElse OExpression OExpression OExpression
  | -- Types are first-class values
    EType OType
  | -- Expression captures
    Quote OExpression
  | -- Functions
    Lambda [String] OEnv OExpression
  | NativeCall String
  | Call OExpression [OExpression]
  | -- Names
    Let [Binding] OExpression
  | Name String
  | RuntimeError String
  deriving (Eq, Ord)

instance Show OExpression where
  show (ENumber n) = show n
  show (EBool b) = show b
  show (IfElse cond trueExpr falseExpr) = "if " ++ show cond ++ " then " ++ show trueExpr ++ " else " ++ show falseExpr
  show (EType typ) = "[type " ++ show typ ++ "]"
  show (Let bindings expr) = "let " ++ (List.map show bindings & unwords) ++ " in " ++ show expr
  show (Name n) = n
  show (RuntimeError e) = "RuntimeError: " ++ e
  show (NativeCall name) = "Native fn <" ++ name ++ ">"
  show (Call fn args) = "(" ++ show fn ++ " " ++ (List.map show args & unwords) ++ ")"
  show (Lambda args _ body) = "(\\" ++ unwords args ++ " -> " ++ show body ++ ")"
  show (Quote expr) = "quote(" ++ show expr ++ ")"

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
  | TFunction [OType] OType
  | TApply OType [OType]
  | TType -- is of type: Type
  | TAny -- can litarally be anything
  | AnyOf OType OType
  | AllOf OType OType
  | TQuote
  | TypeError
  | TExpression OExpression
  deriving (Show, Eq, Ord)

data OEnv
  = Env (Map.Map String OExpression) (Map.Map OExpression OType) (Maybe OEnv)
  deriving (Show, Eq, Ord)

makeOakVersion :: (a -> OExpression) -> OType -> String -> (Int -> Int -> a) -> (String, ([OExpression] -> OExpression, OType))
makeOakVersion toExpr typ name fn =
  let builtinFn [ENumber a, ENumber b] = toExpr (fn a b)
      builtinFn exprs = (error $ "Expected two numbers for " ++ name ++ ", got " ++ show exprs)
   in (name, (builtinFn, TFunction [TNum, TNum] typ))

nativeFns :: [(String, ([OExpression] -> OExpression, OType))]
nativeFns =
  [ makeOakVersion ENumber TNum "+" (+),
    makeOakVersion ENumber TNum "-" (-),
    makeOakVersion ENumber TNum "*" (*),
    makeOakVersion EBool TBool "<" (<),
    makeOakVersion EBool TBool ">" (>),
    makeOakVersion EBool TBool ">=" (>=),
    makeOakVersion EBool TBool "<=" (<=),
    makeOakVersion EBool TBool "==" (==)
  ]

nativeCalls :: Map.Map String ([OExpression] -> OExpression, OType)
nativeCalls =
  Map.fromList nativeFns

debugPipe :: (Show b) => [Char] -> b -> b
debugPipe name x = traceShow (name ++ ": " ++ show x) x

_emptyEnv :: OEnv
_emptyEnv =
  Env Map.empty Map.empty Nothing

defaultEnv :: OEnv
defaultEnv =
  List.foldl
    ( \e (n, (fn, typ)) ->
        e
          & evalBinding (BindType (Name n) typ)
          & evalBinding (BindType (NativeCall n) typ)
          & evalBinding (BindValue n (NativeCall n))
    )
    _emptyEnv
    nativeFns

makeChildEnv :: OEnv -> OEnv
makeChildEnv env = Env Map.empty Map.empty (Just env)

child `setParent` parent = case child of
  Env bs ts (Just p) -> Env bs ts (Just $ p `setParent` parent)
  Env bs ts Nothing -> Env bs ts (Just parent)

inferDirectType :: OExpression -> OEnv -> OType
inferDirectType expression env =
  let ret = case expression & debugPipe "inferType of" of
        ENumber _ -> TNum
        EBool _ -> TBool
        IfElse cond trueExpr falseExpr ->
          let condType = inferDirectType cond env
              trueType = inferDirectType trueExpr env
              falseType = inferDirectType falseExpr env
           in if condType `isSubset` TBool && trueType == falseType
                then trueType
                else TypeError
        EType _ -> TType
        Quote _ -> TQuote
        RuntimeError _ -> TAny
        Name n ->
          let nType =
                do
                  nExpr <- resolveName n env
                  return $ inferDirectType nExpr env
           in nType & debugPipe ("can't resolve name " ++ n) & Maybe.fromMaybe TAny
        NativeCall n -> resolveType (Name n) env & Maybe.fromJust
        Lambda args _ body ->
          let bodyType = inferDirectType body env
              argTypes = List.map (const TAny) args
           in TFunction argTypes bodyType
        Let [] expr -> inferDirectType expr env
        Let ((BindType texpr typ) : bs) expr ->
          -- TODO check if there's a bound value and the type matches
          let newEnv = evalBinding (BindType texpr TType) env
           in inferDirectType (Let bs expr) newEnv
        Let ((BindValue n nVal) : bs) expr ->
          let newEnv =
                inferDirectType nVal env
                  & (\t -> evalBinding (BindType (Name n) t) env)
                  & (\t -> evalBinding (BindValue n nVal) env)
           in inferDirectType (Let bs expr) newEnv
        Call fn [] ->
          let fnType = inferDirectType fn env
              TFunction _ retType = fnType
           in retType
        Call fn args ->
          let fnType = inferDirectType fn env
              argTypes = List.map (`inferDirectType` env) args
           in TApply fnType argTypes & simplifyType
   in ret & debugPipe ("infered type of " ++ show expression ++ " :::: ")

TAny `isSubset` t = True
t `isSubset` TAny = True
t `isSubset` u = t == u

simplifyType :: OType -> OType
simplifyType typ =
  case typ of
    TApply (TFunction [] retType) [] ->
      simplifyType retType
    TApply (TFunction (fnArgType : argTypes) retType) (callArgType : callTypes) ->
      if callArgType `isSubset` fnArgType
        then simplifyType $ TApply (TFunction argTypes retType) callTypes
        else TypeError
    _ -> typ

checkType :: OType -> OExpression -> OEnv -> Bool
checkType otype expression env =
  inferDirectType expression env `isSubset` otype

newtype Computation a = Computation {runEnv :: OEnv -> (OEnv, a)}

instance Functor Computation where
  fmap = liftM

instance Applicative Computation where
  (<*>) = ap
  pure value = Computation (const (defaultEnv, value))

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

eval :: OExpression -> OEnv -> OExpression
eval expr env =
  let ret = case expr & debugPipe "eval start" of
        IfElse condExpr trueExpr falseExpr ->
          case eval condExpr env of
            (EBool True) -> eval trueExpr env
            (EBool False) -> eval falseExpr env
            _ -> RuntimeError $ show (eval condExpr env) ++ " isn't a boolean"
        Name n -> resolveName n env & Maybe.fromMaybe (RuntimeError ("Can't resolve name " ++ n))
        Lambda args _ body -> Lambda args env body
        Let bindings expr ->
          let newEnv = List.foldl (flip evalBinding) env bindings
           in eval expr newEnv
        Call (Lambda largs lenv lbody) args ->
          let (bindings, (rlargs, rargs)) = zipAll (largs, args)
              newEnv = List.foldl (\e (n, x) -> evalBinding (BindValue n (eval x env)) e) (makeChildEnv lenv) bindings
           in case (rlargs, rargs) of
                ([], []) -> eval lbody (newEnv) -- `setParent` env)
                (rlargs, []) -> eval (Lambda rlargs newEnv lbody) env
                ([], rargs) -> eval (Call (eval lbody newEnv) rargs) env
        Call (NativeCall name) args ->
          let (fn, _) = Map.lookup name nativeCalls & Maybe.fromJust
           in eval (fn (List.map (`eval` env) args)) env
        Call fnExpr args -> eval (Call (eval fnExpr env) args) env
        RuntimeError e -> error (show expr)
        _ -> expr
   in ret & debugPipe ((show expr) ++ " --> ")

hasBinding :: String -> OEnv -> Bool
hasBinding name (Env bindingMap _ parentEnv) =
  Map.member name bindingMap || maybe False (hasBinding name) parentEnv

hasTypeBinding :: String -> OEnv -> Bool
hasTypeBinding name (Env bindingMap _ parentEnv) =
  Map.member name bindingMap || maybe False (hasBinding name) parentEnv

orElse :: Maybe a -> Maybe a -> Maybe a
orElse a@(Just _) _ = a
orElse _ b = b

resolveType :: OExpression -> OEnv -> Maybe OType
resolveType expr env@(Env _ tBindings maybeParent) =
  tBindings
    & Map.lookup expr
    & orElse (resolveType expr =<< maybeParent)

resolveName :: String -> OEnv -> Maybe OExpression
resolveName name env@(Env bindings _ maybeParent) =
  bindings
    & Map.lookup name
    & orElse (resolveName name =<< maybeParent)

evalBinding :: Binding -> OEnv -> OEnv
evalBinding bind env@(Env bindings tBindings maybeParent) =
  case bind of
    BindValue name expr ->
      if Map.member name bindings
        then error $ "Can't overwrite existing value binding " ++ name
        else Env (bindings & Map.insert name expr) tBindings maybeParent
    BindType name typ ->
      let newType = case Map.lookup name tBindings of
            Just existingType -> AllOf typ existingType
            Nothing -> typ
       in Env bindings (tBindings & Map.insert name typ) maybeParent

set = BindValue

num = ENumber

n = Name

nn = NativeCall

lambda args = Lambda args defaultEnv

call fnName argNames = Call (Name fnName) (List.map Name argNames)

main :: IO ()
main =
  let expr =
        Let
          [ set "x" (num 3),
            set "y" (num 4),
            set "add" (lambda ["x", "y"] (Call (nn "+") [n "x", n "y"])),
            set
              "fact"
              ( lambda
                  ["n"]
                  ( IfElse
                      (Call (nn "<=") [n "n", num 1])
                      (num 1)
                      (Call (n "fact") [Call (nn "-") [n "n", num 1]])
                  )
              )
          ]
          -- (Name "x")
          -- (Call (Name "+") [Name "x", Name "y"])
          -- (call "add" ["y", "y"])
          (call "fact" ["y"])
          -- (n "fact")
   in do
        putStrLn ("> \x1b[1m" ++ show expr ++ "\x1b[22m")
        putStrLn ("  = " ++ show (eval expr defaultEnv))
        putStrLn ""
        -- putStrLn (" := " ++ show (inferDirectType expr defaultEnv & simplifyType))

        putStrLn ""
        putStrLn "done"
