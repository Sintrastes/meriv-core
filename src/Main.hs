module Main where

import Meriv.Types
import Data.Typeable
import Data.Functor.Identity

data MySchema =
    Person
  | Place
  | Thing

data MyEntity (t :: MvType MySchema) where
  Nate :: MyEntity ('MvBaseT 'Person)
  Will :: MyEntity ('MvBaseT 'Person)
  NewYork :: MyEntity ('MvBaseT 'Place)
  Guitar  :: MyEntity ('MvBaseT 'Thing)
  LivesIn :: MyEntity ('MvFunT ('MvBaseT 'Person) ('MvFunT ('MvBaseT 'Place) 'MvPredT))

example :: MvTerm Identity MySchema MyEntity 'MvPredT
example =
  MvApp (MvApp (MvEntity $ Identity LivesIn)
     (MvEntity $ Identity Nate))
     (MvEntity $ Identity NewYork)

main :: IO ()
main = putStrLn "Hello, Haskell!"
