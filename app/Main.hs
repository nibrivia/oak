module Main (main) where

import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Debug.Trace
import Text.ParserCombinators.Parsec

-- | Expressions evaluate to something tangible
data Expression
  = ONumber Int
  | OString String
  | OBool Bool
  | Lambda [String] Env Expression
  | Type Expression
  | TypeFun Expression Expression
  | TypeOr [Expression]
  | Quote Expression
  | Name String
  | IfElse Expression Expression Expression
  | Call Expression [Expression]
  | Error String
  | Let [Binding] Expression
  deriving (Show, Eq)

-- | Bindings only modify the environment
data Binding
  = Bind String Expression
  deriving (Show, Eq)

debugPipe :: (Show b) => String -> b -> b
debugPipe name x = traceShow (name ++ ": " ++ show x) x

data Env
  = EmptyEnv
  | Env (Map.Map String Expression) Env
  deriving (Show, Eq)

envLookup :: Env -> String -> Expression
envLookup EmptyEnv name = Error ("Value " ++ show name ++ "not found")
envLookup (Env dict parentEnv) name =
  dict & Map.lookup name & Maybe.fromMaybe (envLookup parentEnv name)

envSet :: Env -> String -> Expression -> Env
envSet (Env dict parent) name value =
  if not (Map.member name dict)
    then Env (Map.insert name value dict) parent
    else error $ "Can't override existing binding for " ++ name

makeChild :: Env -> Env
makeChild = Env Map.empty

setParent :: Env -> Env -> Env
setParent (Env dict EmptyEnv) = Env dict

defaultEnv :: Env
defaultEnv = Env Map.empty EmptyEnv

toBuiltinNum :: Expression -> Int
toBuiltinNum (ONumber n) = n

toBuiltinBool :: Expression -> Bool
toBuiltinBool (OBool b) = b

toBuiltinStr :: Expression -> String
toBuiltinStr (OString s) = s

evalBinaryNum :: Env -> (Int -> Int -> Expression) -> Expression -> Expression -> (Env, Expression)
evalBinaryNum env fn arg1 arg2 =
  let isNumber expr = case expr of
        ONumber _ -> True
        _ -> False

      varg1 = valuate env arg1
      varg2 = valuate env arg2
   in if isNumber varg1 && isNumber varg2
        then (env, fn (toBuiltinNum varg1) (toBuiltinNum varg2))
        else (env, Error "Tried to call a built-in function with a non-number argument")

-- >>> valuate defaultEnv (Value (ONumber 2))
--
eval :: Env -> Expression -> (Env, Expression)
eval env expr =
  case expr & debugPipe "Evaluating" of
    (Name name) -> (env, envLookup env name)
    (IfElse condExpr trueExpr falseExpr) ->
      case valuate env condExpr of
        OBool True -> eval env trueExpr
        OBool False -> eval env falseExpr
        _ -> (env, Error $ "conditional expressions must have a boolean argument, got " ++ show (valuate env condExpr) ++ " instead")
    (Call (Name ">") [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a > b)) arg1 arg2
    (Call (Name ">=") [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a >= b)) arg1 arg2
    (Call (Name "<") [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a < b)) arg1 arg2
    (Call (Name "<=") [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a <= b)) arg1 arg2
    (Call (Name "=") [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a == b)) arg1 arg2
    (Call (Name "-") [arg1, arg2]) -> evalBinaryNum env (\a b -> ONumber (a - b)) arg1 arg2
    (Call (Name "+") [arg1, arg2]) -> evalBinaryNum env (\a b -> ONumber (a + b)) arg1 arg2
    (Call (Name "*") [arg1, arg2]) -> evalBinaryNum env (\a b -> ONumber (a * b)) arg1 arg2
    (Call (Lambda [] lenv body) []) -> (env, valuate (setParent lenv env) body)
    (Call (Lambda [] lenv body) args) -> (env, valuate env (Call (valuate (setParent lenv env) body) args)) & debugPipe "weird call"
    (Call l@(Lambda {}) []) -> (env, l)
    (Call (Lambda (n : argNames) lenv body) (a : args)) ->
      let childEnv = bind (Bind n (valuate env a)) lenv
       in eval env (Call (Lambda argNames childEnv body) args)
    (Call (Type _) args) -> (env, Error "Can't call a type")
    (Call (ONumber _) args) -> (env, Error "Can't call a number")
    (Call fnExpr args) -> eval env (Call (valuate env fnExpr) args)
    (Let [] e) -> eval env e
    (Let (b : bs) e) ->
      let newEnv = bind b env
       in eval newEnv (Let bs e)
    (Error str) -> error str
    (Lambda names _ args) -> (env, Lambda names env args & debugPipe "lambda raw eval")
    expr -> (env, expr) -- a lot of values evaluate to themselves

bind :: Binding -> Env -> Env
bind (Bind name expr) env =
  envSet env name expr

valuate :: Env -> Expression -> Expression
valuate env expr = value
  where
    (_, value) = eval env expr

numType :: Expression
numType = Type (OString "Num")

boolType :: Expression
boolType = Type (OString "Bool")

typeType :: Expression
typeType = Type (OString "Type")

inferType :: Env -> Expression -> Expression
inferType _ (ONumber _) = numType
inferType _ (OString _) = Type (OString "String")
inferType _ (OBool _) = boolType
inferType _ (Type _) = typeType
inferType _ (TypeFun {}) = typeType
inferType _ (TypeOr {}) = typeType
inferType _ (Name "-") = TypeFun numType (TypeFun numType numType)
inferType _ (Name "+") = TypeFun numType (TypeFun numType numType)
inferType _ (Name "<=") = TypeFun numType (TypeFun numType boolType)
inferType _ (Name ">=") = TypeFun numType (TypeFun numType boolType)
inferType _ (Name "=") = TypeFun numType (TypeFun numType boolType)
inferType env (Name n) = envLookup env n & inferType env
inferType env (Let [] x) = inferType env x
inferType env (Let (b : bs) x) = inferType (bind b env) (Let bs x)
inferType env (Lambda [] lenv body) =
  inferType env body
inferType env (Lambda (n : ns) lenv body) =
  TypeFun numType (inferType env (Lambda ns lenv body))
inferType env (Call fun args) =
  let funType = inferType env fun

      callReduction :: Expression -> [Expression] -> Expression
      callReduction funType [] = funType
      callReduction (TypeFun t ts) (a : rgs) = callReduction ts rgs -- TODO if `inferType a == t`
      callReduction _ args = Error "Error during type inference of a function call"
   in callReduction funType args
inferType env (IfElse condExpr trueExpr falseExpr) =
  let trueType = inferType env trueExpr
      falseType = inferType env falseExpr
   in if trueType == falseType
        then trueType
        else IfElse condExpr trueType falseType

-- _ -> Error "conditional expressions must have a boolean argument"

main :: IO ()
main =
  -- let res = valuate defaultEnv (Call (Name "+") [ONumber 3, ONumber 2])
  let longExpr =
        Let
          [ Bind "myType" (Type (Name "x")),
            Bind "add" (Lambda ["x", "y"] defaultEnv (Call (Name "+") [Name "x", Name "y"])),
            Bind
              "fib"
              ( Lambda
                  ["x"]
                  defaultEnv
                  ( IfElse
                      (Call (Name "<=") [Name "x", ONumber 1])
                      (ONumber 1)
                      ( Call
                          (Name "+")
                          [ Call (Name "fib") [Call (Name "-") [Name "x", ONumber 1]],
                            Call (Name "fib") [Call (Name "-") [Name "x", ONumber 2]]
                          ]
                      )
                  )
              ),
            Bind "x" (ONumber 7),
            Bind "y" (ONumber 3)
          ]
          -- (Name "myType")
          -- (Name "x")
          -- (Name "y")
          -- (Name "fib")
          -- (Call (Name "add") [ONumber 2])
          (Call (Call (Name "add") [ONumber 2]) [ONumber 3])
      -- (Call (Name "fib") [Name "x"])

      x = 1
   in do
        print (valuate defaultEnv longExpr)
        print (inferType defaultEnv longExpr)
