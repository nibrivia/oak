{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

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
  | Call OExpression [OExpression]
  | -- Names
    Let [Binding] OExpression
  | Name String
  | RuntimeError String
  deriving (Show, Eq)

-- | Bindings only modify the environment
data Binding
  = BindValue String OExpression
  | BindType String OExpression
  deriving (Show, Eq)

data OType
  = TNum
  | TBool
  | TFunction OType OType
  | TType -- is of type: Type
  | TAny -- can litarally be anything
  | AnyOf OType OType
  | AllOf OType OType
  | TExpression
  deriving (Show, Eq)

data OEnv
  = Env (Map.Map String OExpression) OEnv
  | EmptyEnv
  deriving (Show, Eq)

inferDirectType :: OEnv -> OExpression -> Maybe OType
inferDirectType env expression =
  case expression of
    ENumber _ -> Just TNum
    EBool _ -> Just TBool
    EType _ -> Just TType
    Quote _ -> Just TExpression
    _ -> Nothing

checkType :: OEnv -> OType -> OExpression -> Maybe Bool
checkType env otype expression =
  case inferDirectType env expression of
    Just infType -> Just (infType == otype)
    Nothing -> Nothing

newtype Computation a = Computation {runEnv :: OEnv -> (OEnv, a)}

instance Functor Computation where
  fmap = liftM

instance Applicative Computation where
  (<*>) = ap
  pure value = Computation (\_ -> (EmptyEnv, value))

instance Monad Computation where
  Computation compA >>= fn =
    Computation $
      \env ->
        let (newEnv, newRes) = compA env
            Computation nextCompFn = fn newRes
         in nextCompFn newEnv

valuate expr env = value where (_, value) = eval expr env

eval :: OExpression -> OEnv -> (OEnv, OExpression)
eval expr env =
  case expr of
    IfElse condExpr trueExpr falseExpr ->
      case valuate trueExpr env of
        (EBool True) -> (env, trueExpr)
        (EBool False) -> (env, falseExpr)
        _ -> (env, RuntimeError "boolean isn't a boolean")
    _ -> (env, expr)

main :: IO ()
main =
  do
    putStrLn ""
    putStrLn "done"
