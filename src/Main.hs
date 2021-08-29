module Main where

import Meriv.Types
import Data.Typeable
import Data.Functor.Identity
import Data.Singletons.TH

data MySchema =
    Person
  | Place
  | Thing

$(genSingletons [''MySchema])

data MyEntity (t :: MvType MySchema) where
  Nate :: MyEntity ('MvBaseT 'Person)
  Will :: MyEntity ('MvBaseT 'Person)
  NewYork :: MyEntity ('MvBaseT 'Place)
  Guitar  :: MyEntity ('MvBaseT 'Thing)
  LivesIn :: MyEntity ('MvFunT ('MvBaseT 'Person) ('MvFunT ('MvBaseT 'Place) 'MvPredT))

example :: MvTerm Identity MySchema MyEntity 'MvPredT
example =
  MvApp (MvApp (MvEntity (SMvFunT (SMvBaseT SPerson) (SMvFunT (SMvBaseT SPlace) SMvPredT)) $ Identity LivesIn)
     (MvEntity (SMvBaseT SPerson) $ Identity Nate))
     (MvEntity (SMvBaseT SPlace) $ Identity NewYork)

main :: IO ()
main = putStrLn "Hello, Haskell!"
