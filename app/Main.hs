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
  = BindValue String Expression
  | BindType String Expression
  deriving (Show, Eq)

debugPipe :: (Show b) => String -> b -> b
debugPipe name x = traceShow (name ++ ": " ++ show x) x

data Env
  = EmptyEnv
  | Env (Map.Map String Expression) (Map.Map String Expression) Env
  deriving (Show, Eq)

envLookup :: Env -> String -> Expression
envLookup EmptyEnv name = Error ("Value " ++ show name ++ "not found")
envLookup (Env dict _ parentEnv) name =
  let _ = if name == "x" then debugPipe "### x" value else value
      value = dict & Map.lookup name & Maybe.fromMaybe (envLookup parentEnv name)
   in value

orElse :: Maybe a -> Maybe a -> Maybe a
orElse a@(Just x) _ = a
orElse Nothing b@(Just x) = b
orElse Nothing Nothing = Nothing

envTypeLookup :: Env -> String -> Maybe Expression
envTypeLookup EmptyEnv name = Nothing
envTypeLookup (Env _ typeDict parentEnv) name =
  typeDict & Map.lookup name & orElse (envTypeLookup parentEnv name)

envLookupAndEval :: Env -> String -> (Env, Expression)
envLookupAndEval EmptyEnv name = (EmptyEnv, anyType)
envLookupAndEval env@(Env dict _ parentEnv) name =
  case Map.lookup name dict of
    Just expr ->
      let value = valuate env expr
       in (envSetValue env name value, value & debugPipe "envLookupAndEval")
    Nothing ->
      envLookupAndEval parentEnv name

envSetValue :: Env -> String -> Expression -> Env
envSetValue (Env dict typeDict parent) name value =
  if not (Map.member name dict)
    then Env (Map.insert name value dict) typeDict parent
    else error $ "Can't override existing binding for " ++ name

envSetType :: Env -> String -> Expression -> Env
envSetType (Env valDict typeDict parent) name typeValue =
  case Map.lookup name typeDict of
    Just existingType ->
      if typeValue `isSubset` existingType == OBool True
        then Env valDict (Map.insert name typeValue typeDict) parent
        else error "Types aren't compatible"
    Nothing -> Env valDict (Map.insert name typeValue typeDict) parent

makeChild :: Env -> Env
makeChild = Env Map.empty Map.empty

setRootParent :: Env -> Env -> Env
setRootParent (Env dict typeDict EmptyEnv) newParent = Env dict typeDict newParent
setRootParent (Env dict typeDict parentEnv) newParent = Env dict typeDict (setRootParent parentEnv newParent)

defaultEnv :: Env
defaultEnv = Env Map.empty Map.empty EmptyEnv

toBuiltinNum :: Expression -> Int
toBuiltinNum (ONumber n) = n

toBuiltinBool :: Expression -> Bool
toBuiltinBool (OBool b) = b

toBuiltinStr :: Expression -> String
toBuiltinStr (OString s) = s

evalBinaryNum :: Env -> (Int -> Int -> Expression) -> Expression -> Expression -> Expression
evalBinaryNum env fn arg1 arg2 =
  let isNumber expr = case expr of
        ONumber _ -> True
        _ -> False

      varg1 = valuate env arg1
      varg2 = valuate env arg2
   in if isNumber varg1 && isNumber varg2
        then fn (toBuiltinNum varg1) (toBuiltinNum varg2)
        else Error "Tried to call a built-in function with a non-number argument"

zipFresh :: [a] -> [b] -> ([(a, b)], ([a], [b]))
zipFresh [] bs = ([], ([], bs))
zipFresh as [] = ([], (as, []))
zipFresh (a : as) (b : bs) =
  let (futurePairs, leftovers) = zipFresh as bs
   in ((a, b) : futurePairs, leftovers)

-- >>> valuate defaultEnv (Value (ONumber 2))
--
eval :: Env -> Expression -> (Env, Expression)
eval env expr =
  let res = case expr & debugPipe "Starting eval" of
        (Name name) -> envLookupAndEval env name
        (IfElse condExpr trueExpr falseExpr) ->
          ( env,
            case valuate env condExpr of
              OBool True -> valuate env trueExpr
              OBool False -> valuate env falseExpr
              _ -> Error $ "conditional expressions must have a boolean argument, got " ++ show (valuate env condExpr) ++ " instead"
          )
        (Call fnExpr args) ->
          ( env,
            case (fnExpr, args) of
              (Name ">", [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a > b)) arg1 arg2
              (Name ">=", [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a >= b)) arg1 arg2
              (Name "<", [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a < b)) arg1 arg2
              (Name "<=", [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a <= b)) arg1 arg2
              (Name "=", [arg1, arg2]) -> evalBinaryNum env (\a b -> OBool (a == b)) arg1 arg2
              (Name "-", [arg1, arg2]) -> evalBinaryNum env (\a b -> ONumber (a - b)) arg1 arg2
              (Name "+", [arg1, arg2]) -> evalBinaryNum env (\a b -> ONumber (a + b)) arg1 arg2
              (Name "*", [arg1, arg2]) -> evalBinaryNum env (\a b -> ONumber (a * b)) arg1 arg2
              (Name "inferType", [Quote x]) -> inferType env x
              (Lambda [] lenv body, []) -> valuate (setRootParent (lenv & debugPipe "lenv") env & debugPipe "lenvRooted") (body & debugPipe "evaluating body")
              (Lambda [] lenv body, args) -> valuate env (Call (valuate (setRootParent lenv env) body) args) & debugPipe "weird call"
              (l@(Lambda {}), []) -> l & debugPipe "evaluating lambda, ran out of args"
              (Lambda (n : argNames) lenv body, a : args) ->
                valuate env (Call (Lambda argNames lenv (Let [BindValue n (valuate env a)] body)) args)
              (Type _, args) -> Error "Can't call a type"
              (ONumber _, args) -> Error "Can't call a number"
              _ -> valuate env (Call (valuate env fnExpr) args)
          )
        (Let [] e) -> eval env e
        (Let bs e) ->
          let childEnv = makeChild env
              newEnv = List.foldl (flip bind) childEnv bs
           in eval newEnv e
        (Error str) -> error str
        (Lambda names EmptyEnv args) -> (env, Lambda names env args & debugPipe "lambda raw eval")
        expr -> (env, expr) -- a lot of values evaluate to themselves
      (resEnv, value) = res
   in (resEnv, value & debugPipe (" = eval " ++ show expr))

bind :: Binding -> Env -> Env
bind (BindValue name expr) env =
  envSetValue env name expr
bind (BindType name expr) env =
  envSetType env name expr

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

anyType :: Expression
anyType = Type (OString "Any")

isSubset :: Expression -> Expression -> Expression
(Type t) `isSubset` (Type (OString "Any")) = OBool True
(TypeFun _ _) `isSubset` (Type (OString "Any")) = OBool True
(Type t) `isSubset` (Type u) =
  if u == typeType || u == anyType
    then OBool True
    else OBool ((t == u) & debugPipe " !!!! Manual type checking")
t `isSubset` u = Error "Can't check if nontypes are subsets"

isInstanceOf :: Env -> Expression -> Expression -> Expression
isInstanceOf env expr typ@(Type (OString "Any")) = OBool True
isInstanceOf env expr typ@(Type _) = inferType env expr `isSubset` typ
isInstanceOf _ _ _ = Error "Can't check if value is subset of non-type"

-- | >>> callReduction (TypeFun numType numType) [numType] == numType
callReduction :: Env -> Expression -> [Expression] -> Expression
callReduction _ funType [] = funType
callReduction env (TypeFun t ts) (a : rgs) =
  if isInstanceOf env a t == OBool True
    then callReduction env ts rgs -- TODO argument binding
    else Error "Infertype: wrong argument type"
callReduction _ _ _ = Error "Error during type inference of a function call"

inferPass :: Env -> Expression -> Expression
inferPass env expression = Error "noType"

checkType :: Env -> Expression -> Expression -> (Env, Expression)
checkType env expr typ = (env, OBool True)

toFunType :: [Expression] -> Expression
toFunType = foldr TypeFun anyType

inferType :: Env -> Expression -> Expression
inferType env expr =
  case expr & debugPipe "inferType" of
    ONumber _ -> numType
    OString _ -> Type (OString "String")
    OBool _ -> boolType
    Type _ -> typeType
    TypeFun {} -> typeType
    TypeOr {} -> typeType
    Name "-" -> TypeFun numType (TypeFun numType numType)
    Name "+" -> TypeFun numType (TypeFun numType numType)
    Name "<=" -> TypeFun numType (TypeFun numType boolType)
    Name ">=" -> TypeFun numType (TypeFun numType boolType)
    Name "=" -> TypeFun numType (TypeFun numType boolType)
    Name "inferType" -> TypeFun (Type (OString "Quote")) typeType
    Name n -> case envTypeLookup env n of
      Just t -> t
      Nothing -> envLookup env n & inferType env
    Let bs x ->
      valuate env (Let bs (Call (Name "inferType") [Quote x]))
    Lambda [] lenv body ->
      inferType env body
    Lambda (n : ns) lenv body ->
      TypeFun anyType (inferType env (Lambda ns lenv body))
    Call (Name n) args ->
      let existingFunType = envTypeLookup env n & Maybe.fromMaybe anyType
          argTypes = List.map (inferType env) args
          requiredType = toFunType argTypes
       in if (requiredType `isSubset` existingFunType) == OBool True
            then callReduction env requiredType args
            else error $ "Call type " ++ show requiredType ++ " not compatible with existing definion " ++ show existingFunType
    Call fun args ->
      let funType = inferType env fun
       in callReduction env funType args
    IfElse condExpr trueExpr falseExpr ->
      -- TODO check typeof condExpr is bool
      let trueType = inferType env trueExpr
          falseType = inferType env falseExpr
       in if trueType == falseType
            then trueType
            else IfElse condExpr trueType falseType

main :: IO ()
main =
  let longExpr =
        Let
          [ BindValue "myType" (Type (Name "x")),
            BindValue "add" (Lambda ["x", "y"] EmptyEnv (Call (Name "+") [Name "x", Name "y"])),
            BindValue
              "fib"
              ( Lambda
                  ["x"]
                  EmptyEnv
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
            BindValue "y" (ONumber 3),
            BindValue "a" (Call (Name "+") [Name "y", ONumber 4])
          ]
          -- (Name "myType")
          -- (Name "x")
          -- (Name "a")
          -- (Name "fib")
          -- (Name "add")
          (Call (Name "add") [ONumber 2])
      -- (Call (Call (Name "add") [ONumber 2]) [ONumber 3])
      -- (Call (Name "inferType") [Quote (Name "fib")])
      -- (Call (Name "fib") [Name "a"])

      x = 1
   in do
        putStrLn ""
        putStrLn ("> " ++ show longExpr)
        print (valuate defaultEnv longExpr)

        putStrLn ""
        putStrLn "> inferType ..."
        print (inferType defaultEnv longExpr)

        putStrLn ""
        putStrLn "done"
