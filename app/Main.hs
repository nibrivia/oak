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
  show (NativeCall name) = "[Native fn `" ++ name ++ "`]"
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

makeChildEnv :: OEnv -> OEnv
makeChildEnv env = Env Map.empty Map.empty (Just env)

setParent :: OEnv -> OEnv -> OEnv
child `setParent` parent =
  case child of
    Env bs ts (Just p) -> Env bs ts (Just $ p `setParent` parent)
    Env bs ts Nothing -> Env bs ts (Just parent)

inferDirectType :: OExpression -> Computation OType
inferDirectType expression =
  case expression & debugPipe "\n--- start inferType of" of
    ENumber _ -> return TNum
    EBool _ -> return TBool
    IfElse cond trueExpr falseExpr ->
      do
        condType <- inferDirectType cond
        trueType <- inferDirectType trueExpr
        falseType <- inferDirectType falseExpr
        if condType `isSubset` TBool && trueType == falseType
          then return trueType
          else return TypeError
    EType _ -> return TType
    Quote _ -> return TQuote
    RuntimeError _ -> return TAny
    Name n ->
      -- let nType =
      --       do
      --         nExpr <- resolveName n
      --         return $ inferDirectType nExpr
      -- in -- in nType & Maybe.fromMaybe TAny
      return TAny
    NativeCall n -> Computation (\env -> (env, resolveType (Name n) env & Maybe.fromJust))
    Lambda args _ body ->
      do
        bodyType <- inferDirectType body
        let argTypes = List.map (const TAny) args
        return $ TFunction argTypes bodyType
    Let [] expr -> inferDirectType expr
    Let ((BindType texpr typ) : bs) expr ->
      do
        -- TODO check if there's a bound value and the type matches
        evalBinding (BindType texpr TType)
        inferDirectType (Let bs expr)
    Let ((BindValue n nVal) : bs) expr ->
      do
        tp <- inferDirectType nVal
        evalBinding (BindType (Name n) tp)
        evalBinding (BindValue n nVal)
        inferDirectType (Let bs expr)
    Call fn [] ->
      do
        fnType <- inferDirectType fn
        let TFunction _ retType = fnType
        return retType
    Call fn args ->
      do
        fnType <- inferDirectType fn
        -- argTypes <- List.map (\t -> inferDirectType t env) args & foldM (>=>) args
        argTypes <-
          foldM
            ( \ts a ->
                do
                  t <- inferDirectType a
                  return (t : ts)
            )
            []
            args
        return (TApply fnType argTypes & simplifyType)

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
    return (res & debugPipe "valuate res")

eval :: OExpression -> Computation OExpression
eval expr =
  case expr & debugPipe "expr" of
    IfElse condExpr trueExpr falseExpr ->
      do
        condValue <- eval condExpr
        case condValue & debugPipe ("eval condValue " ++ show condExpr ++ " ") of
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
        let (bindings, (rlargs, rargs)) = zipAll (largs, args) & debugPipe "lambda zip res"
        values <-
          foldM
            ( \res (n, a) -> do
                arg <- eval a
                return $ (n, arg) : res
            )
            []
            (bindings & List.reverse)
        let (newEnv, _) =
              compute
                (makeChildEnv lenv)
                (foldM_ (\_ (n, x) -> evalBinding (BindValue n x)) () values)
        case (rlargs, rargs) of
          ([], []) -> valuate lbody newEnv & trace "default"
          (rlargs, []) -> eval (Lambda rlargs newEnv lbody) & trace "rlargs"
          ([], rargs) -> do
            newBody <- valuate lbody newEnv
            eval (Call newBody rargs)
    Call (NativeCall name) args ->
      let (fn, _) = Map.lookup name nativeCalls & Maybe.fromJust
       in do
            vargs <-
              foldlM
                ( \res a -> do
                    arg <- eval a
                    -- TODO why does this flip?
                    return $ arg : res
                )
                []
                (args & List.reverse)
            let res = fn vargs
            eval res
    -- eval (fn (List.map (\e -> e e env) args))
    Call fnExpr args ->
      do
        fn <- eval fnExpr
        eval (Call fn args)
    RuntimeError e -> error (show expr)
    _ -> return expr

hasBinding :: String -> OEnv -> Bool
hasBinding name (Env bindingMap _ parentEnv) =
  Map.member name bindingMap || maybe False (hasBinding name) parentEnv

hasTypeBinding :: String -> OEnv -> Bool
hasTypeBinding name (Env bindingMap _ parentEnv) =
  Map.member name bindingMap || maybe False (hasBinding name) parentEnv

orElse :: Maybe a -> Maybe a -> Maybe a
orElse _ a@(Just _) = a
orElse b _ = b

resolveType :: OExpression -> OEnv -> Maybe OType
resolveType expr env@(Env _ tBindings maybeParent) =
  tBindings
    & Map.lookup expr
    & orElse (resolveType expr =<< maybeParent)

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
    ( \(Env bindings tBindings maybeParent) ->
        case bind of
          BindValue name expr ->
            if Map.member name bindings
              then error $ "Can't overwrite existing value binding " ++ name
              else (Env (bindings & Map.insert name expr) tBindings maybeParent, ())
          BindType name typ ->
            let newType = case Map.lookup name tBindings of
                  Just existingType -> AllOf typ existingType
                  Nothing -> typ
             in (Env bindings (tBindings & Map.insert name newType) maybeParent, ())
    )

set :: String -> OExpression -> Binding
set = BindValue

num :: Int -> OExpression
num = ENumber

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
          [ set "y" (calln "+" ["x", "x"]),
            set "x" (num 3),
            set "add" (lambda ["x", "y"] (Call (nn "+") [n "x", n "y"])),
            set
              "fact"
              ( lambda
                  ["x"]
                  ( IfElse
                      (Call (nn "<=") [n "x", num 1])
                      (num 1)
                      (Call (nn "*") [n "x", Call (n "fact") [Call (nn "-") [n "x", num 1]]])
                  )
              )
          ]
          -- (Call (NativeCall "+") [Name "x", Name "y"])
          -- (Name "y")
          -- (num 2)
          -- (n "fact")
          -- (call "add" ["y", "y"])
          (call "fact" ["y"])

      _ = 0
   in do
        putStrLn ("> \x1b[1m" ++ show expr ++ "\x1b[22m")
        let (_, res) = compute defaultEnv (eval expr)
        putStrLn ("  = " ++ show res)
        putStrLn ""

        putStrLn "================"
        let (_, exprType) = compute defaultEnv (inferDirectType expr)
        putStrLn (" := " ++ show exprType)
        putStrLn ""
        putStrLn "done"
