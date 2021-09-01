
module Main where

import Meriv.Types
import Data.Typeable
import Data.Functor.Identity
import Data.Singletons.TH
import Meriv.Util.Functor
import Control.Monad.Tree
import Meriv.Interp

data MySchema =
    Person
  | Place
  | Thing

$(genSingletons [''MySchema])

data MyEntity (t :: MvType MySchema) where
  Nate         :: MyEntity ('MvBaseT 'Person)
  Will         :: MyEntity ('MvBaseT 'Person)
  NewYorkCity  :: MyEntity ('MvBaseT 'Place)
  NewYorkState :: MyEntity ('MvBaseT 'Place)
  Guitar       :: MyEntity ('MvBaseT 'Thing)
  LivesIn      :: MyEntity ('MvFunT ('MvBaseT 'Person)
                               ('MvFunT ('MvBaseT 'Place) 'MvPredT))
  SubsetOf     :: MyEntity ('MvFunT ('MvBaseT 'Place)
                               ('MvFunT ('MvBaseT 'Place) 'MvPredT))

livesIn f = MvEntity (f LivesIn)

subsetOf f = MvEntity (f SubsetOf)

example :: GroundMvTerm MySchema MyEntity 'MvPredT
example =
  MvApp (MvApp (livesIn Id)
     (MvEntity $ Id Nate))
     (MvEntity $ Id NewYorkCity)

exampleProgram = MvRules
  [
    MvClause
      (SomeMvTerm $ MvApp
         (MvApp (livesIn Ground) (MvEntity $ Var (SMvBaseT SPerson) "X"))
	 (MvEntity $ Var (SMvBaseT SPlace) "Z"))
      [
        (SomeMvTerm $ MvApp
	   (MvApp (livesIn Ground) (MvEntity $ Var (SMvBaseT SPerson) "X"))
	   (MvEntity $ Var (SMvBaseT SPlace) "Y"))
      , (SomeMvTerm $ MvApp
           (MvApp (subsetOf Ground) (MvEntity $ Var (SMvBaseT SPlace) "Y"))
	   (MvEntity $ Var (SMvBaseT SPlace) "Z"))
      ]
  ]

main :: IO ()
main = 
    -- let searchResults = bfs $ search exampleProgram (MvGoal [
    --         SomeMvTerm $ MvApp (MvApp (livesIn Ground) (MvEntity $ Ground Nate))
    --	        (MvEntity $ Var (SMvBaseT SPlace) "X")
    --       ]
    --      )
    putStrLn "Hello, Meriv!"
