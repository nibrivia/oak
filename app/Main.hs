module Main where

import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

type OName = String

data Expression
  = ONumber Int
  | OString String
  | OBool Bool
  | OLambda [OName] Expression
  | OType String
  | OExpression Expression
  | Name OName
  | Define OName Expression
  | IfElse Expression Expression Expression
  | Call Expression [Expression]
  | Error String
  | Noop
  deriving (Show)

type Env = Map.Map OName Expression

defaultEnv :: Env
defaultEnv = Map.empty

inferType :: Env -> Expression -> Expression
inferType _ (ONumber _) = OType "Num"
inferType _ (OString _) = OType "String"
inferType _ (OBool _) = OType "Bool"
inferType _ (OLambda _ _) = OType "Function?"
inferType _ (OType _) = OType "Type"
inferType env (Name n) = valuate env (Name n) & inferType env
inferType _ (Define _ _) = OType "Definition"
inferType env (Call fun _) =
  let _ = inferType env fun
   in Error "call type not implemented"
inferType env (IfElse condExpr trueExpr falseExpr) =
  case valuate env condExpr of
    OBool True -> inferType env trueExpr
    OBool False -> inferType env falseExpr
    _ -> Error "conditional expressions must have a boolean argument"

-- >>> valuate defaultEnv (Value (ONumber 2))
--
eval :: Env -> Expression -> (Env, Expression)
eval env (Name name) =
  (env, Maybe.fromMaybe (Error "Can't find value in environment") (Map.lookup name env))
eval env (Define name expression) = (Map.insert name expression env, Noop)
eval env (IfElse condExpr trueExpr falseExpr) =
  case valuate env condExpr of
    OBool True -> eval env trueExpr
    OBool False -> eval env falseExpr
    _ -> (env, Error "conditional expressions must have a boolean argument")
eval env (Call (Name "+") args) =
  (env, ONumber (List.map (valuate env >> (\(ONumber i) -> i)) args & List.sum))
eval env (Call (OLambda [] body) []) = (env, valuate env body)
eval env (Call (OLambda [] body) args) = (env, valuate env (Call (valuate env body) args))
eval env (Call (OLambda _ _) []) = (env, Error "Not enough arguments supplied to function")
eval env (Call (OLambda (n : argNames) body) (a : args)) =
  let (childEnv, _) = eval env (Define n a)
      value = valuate childEnv (Call (OLambda argNames body) args)
   in (env, value)
eval env expr = (env, expr) -- a lot of values evaluate to themselves

valuate :: Env -> Expression -> Expression
valuate env expr = value where (_, value) = eval env expr

main :: IO ()
main =
  let res = valuate defaultEnv (Call (Name "+") [ONumber 3, ONumber 2])
   in print res
