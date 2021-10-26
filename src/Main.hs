
module Main where

import Meriv.Types
import Data.Typeable
import Data.Functor.Identity
import Meriv.Util.Functor
import Data.Singletons
import Control.Unification
import Data.Singletons.TH
import Control.Monad.Tree
import Meriv.Interp
import GHC.Types

data MySchema =
    Person
  | Place
  | Thing deriving(Show)

{-
type PersonSym0 :: MySchema
type family PersonSym0 :: MySchema where
    PersonSym0 = 'Person
type PlaceSym0 :: MySchema
type family PlaceSym0 :: MySchema where
    PlaceSym0 = 'Place
type ThingSym0 :: MySchema
type family ThingSym0 :: MySchema where
    ThingSym0 = 'Thing
type SMySchema :: MySchema -> Type
data SMySchema :: MySchema -> Type
  where
    SPerson :: SMySchema ('Person :: MySchema)
    SPlace :: SMySchema ('Place :: MySchema)
    SThing :: SMySchema ('Thing :: MySchema)
type instance Sing @MySchema = SMySchema
instance SingKind MySchema where
    type Demote MySchema = MySchema
    fromSing SPerson = Person
    fromSing SPlace = Place
    fromSing SThing = Thing
    toSing Person = SomeSing SPerson
    toSing Place = SomeSing SPlace
    toSing Thing = SomeSing SThing
instance SingI 'Person where
    sing = SPerson
instance SingI 'Place where
    sing = SPlace
instance SingI 'Thing where
    sing = SThing
-}

$(genSingletons [''MySchema])
$(singDecideInstances [''MySchema])

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

instance SinglyTyped MySchema MyEntity where
    getTypeSing = \case
        Nate         -> SMvBaseT SPerson
        Will         -> SMvBaseT SPerson
        NewYorkCity  -> SMvBaseT SPlace
        NewYorkState -> SMvBaseT SPlace
        Guitar       -> SMvBaseT SThing
        LivesIn      -> SMvFunT (SMvBaseT SPerson) (SMvFunT (SMvBaseT SPlace) SMvPredT)

instance ShowAllTypes MyEntity where
    showAll = \case
        Nate         -> "nate"
        will         -> "will"
        NewYorkCity  -> "new_york_city"
        NewYorkState -> "new_york_state"
        Guitar       -> "guitar"
        LivesIn      -> "lives_in"
        SubsetOf     -> "subset_of"

instance EntityEq MySchema MyEntity where
    Nate `entityEquals` Nate = True 
    Will `entityEquals` Will = True
    NewYorkCity `entityEquals` NewYorkCity = True
    NewYorkState `entityEquals` NewYorkState = True
    Guitar `entityEquals` Guitar = True 
    LivesIn `entityEquals` LivesIn = True 
    SubsetOf `entityEquals` SubsetOf = True
    _ `entityEquals` _ = False   

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
           (MvApp (livesIn Ground) (MvEntity $ Ground Nate))
	           (MvEntity $ Ground NewYorkCity))
        []
    , MvClause
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

typeOfSome (SomeMvTerm x) = fromSing $ typeOfMv x

main :: IO ()
main = do
    let term1 = SomeMvTerm $ MvEntity $ Ground Nate
    let nyc = SomeMvTerm $ MvEntity $ Ground NewYorkCity
    let term2 = SomeMvTerm $ MvEntity $ Var (SMvBaseT SPerson) "X"
    let term3 = SomeMvTerm $ MvApp
           (MvApp (livesIn Ground) (MvEntity $ Ground Nate))
	           (MvEntity $ Ground NewYorkCity)
    let term4 = SomeMvTerm $ MvApp
           (MvApp (livesIn Ground) (MvEntity $ Ground Nate))
	           (MvEntity $ Var (SMvBaseT SPlace) "X")
    let term5 = SomeMvTerm $ MvEntity $ Var (SMvBaseT SPlace) "X"
    let term6 = SomeMvTerm $ MvEntity $ Ground NewYorkCity
    let unifier = unify term1 term2
    print (typeOfSome nyc)
    print unifier
    let unifier2 = unify term3 term4
    print unifier2
    print $ unify term5 term6
    let searchResults = bfs $ search exampleProgram (MvGoal [
            SomeMvTerm $ MvApp (MvApp (livesIn Ground) (MvEntity $ Ground Nate))
            (MvEntity $ Var (SMvBaseT SPlace) "X")
          ])
    print searchResults
