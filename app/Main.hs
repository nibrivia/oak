module Main where

data Expression
  = Value String
  | Define String Expression
  | Call Expression [Expression]
  | Lambda [String] Expression
  deriving (Show)


{-|
>>> sum 3 4
>>> sum
-}
sum a b = a + b

main :: IO ()
main = putStrLn "Hello, Haskell!"
