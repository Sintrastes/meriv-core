
module Main where

import Meriv.Query
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
import Data.Singletons.Prelude.List

data MySchema =
    Person
  | Place
  | Thing deriving(Show, Eq, Ord)

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
    Nate           :: MyEntity ('MvBaseT 'Person)
    Will           :: MyEntity ('MvBaseT 'Person)
    NewYorkCity    :: MyEntity ('MvBaseT 'Place)
    NewYorkState   :: MyEntity ('MvBaseT 'Place)
    Guitar         :: MyEntity ('MvBaseT 'Thing)
    DirectLivesIn  :: MyEntity ('MvFunT ('MvBaseT 'Person)
                               ('MvFunT ('MvBaseT 'Place) 'MvPredT))
    LivesIn        :: MyEntity ('MvFunT ('MvBaseT 'Person)
                               ('MvFunT ('MvBaseT 'Place) 'MvPredT))
    SubsetOf       :: MyEntity ('MvFunT ('MvBaseT 'Place)
                               ('MvFunT ('MvBaseT 'Place) 'MvPredT))
    DirectSubsetOf :: MyEntity ('MvFunT ('MvBaseT 'Place)
                               ('MvFunT ('MvBaseT 'Place) 'MvPredT))

instance SinglyTyped MySchema MyEntity where
    getTypeSing = \case
        Nate           -> SMvBaseT SPerson
        Will           -> SMvBaseT SPerson
        NewYorkCity    -> SMvBaseT SPlace
        NewYorkState   -> SMvBaseT SPlace
        Guitar         -> SMvBaseT SThing
        LivesIn        -> SMvFunT (SMvBaseT SPerson) (SMvFunT (SMvBaseT SPlace) SMvPredT)
        DirectLivesIn  -> SMvFunT (SMvBaseT SPerson) (SMvFunT (SMvBaseT SPlace) SMvPredT)
        SubsetOf       -> SMvFunT (SMvBaseT SPlace) (SMvFunT (SMvBaseT SPlace) SMvPredT)
        DirectSubsetOf -> SMvFunT (SMvBaseT SPlace) (SMvFunT (SMvBaseT SPlace) SMvPredT)

instance ShowAllTypes MyEntity where
    showAll = \case
        Nate           -> "nate"
        Will           -> "will"
        NewYorkCity    -> "new_york_city"
        NewYorkState   -> "new_york_state"
        Guitar         -> "guitar"
        LivesIn        -> "lives_in"
        DirectLivesIn        -> "lives_in"
        SubsetOf       -> "subset_of"
        DirectSubsetOf -> "direct_subset_of"

instance EntityEq MySchema MyEntity where
    Nate `entityEquals` Nate = True 
    Will `entityEquals` Will = True
    NewYorkCity `entityEquals` NewYorkCity = True
    NewYorkState `entityEquals` NewYorkState = True
    Guitar `entityEquals` Guitar = True 
    LivesIn `entityEquals` LivesIn = True 
    DirectLivesIn `entityEquals` DirectLivesIn = True 
    SubsetOf `entityEquals` SubsetOf = True
    DirectSubsetOf `entityEquals` DirectSubsetOf = True
    _ `entityEquals` _ = False   

livesIn f t = MvEntity (f t LivesIn)

directLivesIn f t = MvEntity (f t DirectLivesIn)

subsetOf f t = MvEntity (f t SubsetOf)

directSubsetOf f t = MvEntity (f t DirectSubsetOf)

example :: GroundMvTerm MySchema MyEntity 'MvPredT
example =
  MvApp (MvApp (livesIn Id livesInType)
     (MvEntity $ Id (SMvBaseT SPerson) Nate))
     (MvEntity $ Id (SMvBaseT SPlace) NewYorkCity)

exampleProgram = MvRules
  [
      -- direct_lives_in(nate, new_york_city)
      MvClause
        (SomeMvTerm SMvPredT $ MvApp
           (MvApp (directLivesIn Ground livesInType) (MvEntity $ Ground (SMvBaseT SPerson) Nate))
	           (MvEntity $ Ground (SMvBaseT SPlace) NewYorkCity))
        []
    -- subset_of(new_york_city, new_york_state)
    , MvClause 
        (SomeMvTerm SMvPredT $ MvApp
            (MvApp (subsetOf Ground subsetOfType) (MvEntity $ Ground (SMvBaseT SPlace) NewYorkCity))
	            (MvEntity $ Ground (SMvBaseT SPlace) NewYorkState))
        []
    -- lives_in(X,Z) :- direct_lives_in(X,Y), subset_of(Y,Z).
    , MvClause
        (SomeMvTerm SMvPredT $ MvApp
           (MvApp (livesIn Ground livesInType) (MvEntity $ Var (SMvBaseT SPerson) "X"))
	           (MvEntity $ Var (SMvBaseT SPlace) "Z"))
        [
          (SomeMvTerm SMvPredT $ MvApp
	     (MvApp (directLivesIn Ground livesInType) (MvEntity $ Var (SMvBaseT SPerson) "X"))
	     (MvEntity $ Var (SMvBaseT SPlace) "Y"))
        , (SomeMvTerm SMvPredT $ MvApp
             (MvApp (subsetOf Ground subsetOfType) (MvEntity $ Var (SMvBaseT SPlace) "Y"))
	     (MvEntity $ Var (SMvBaseT SPlace) "Z"))
        ]
    -- lives_in(X,Y) :- direct_lives_in(X,Y).
    , MvClause
        (SomeMvTerm SMvPredT $ MvApp
           (MvApp (livesIn Ground livesInType) (MvEntity $ Var (SMvBaseT SPerson) "X"))
	           (MvEntity $ Var (SMvBaseT SPlace) "Y"))
        [
          (SomeMvTerm SMvPredT $ MvApp
	     (MvApp (directLivesIn Ground livesInType) (MvEntity $ Var (SMvBaseT SPerson) "X"))
	     (MvEntity $ Var (SMvBaseT SPlace) "Y"))
        ]
  ]

typeOfSome (SomeMvTerm _ x) = fromSing $ typeOfMv x

livesInType = (SMvFunT (SMvBaseT SPerson)
                               (SMvFunT (SMvBaseT SPlace) SMvPredT))

subsetOfType = SMvFunT (SMvBaseT SPlace)
                               (SMvFunT (SMvBaseT SPlace) SMvPredT)

main :: IO ()
main = do
    -- Setup:
    let term1 = SomeMvTerm (SMvBaseT SPerson) $ MvEntity $ Ground (SMvBaseT SPerson) Nate -- nate
    let term2 = SomeMvTerm (SMvBaseT SPerson) $ MvEntity $ Var (SMvBaseT SPerson) "X" -- X: Person
    
    let term3 = SomeMvTerm SMvPredT $ MvApp
           (MvApp (livesIn Ground livesInType) (MvEntity $ Ground (SMvBaseT SPerson) Nate))
	           (MvEntity $ Ground (SMvBaseT SPlace) NewYorkCity) -- livesIn(nate, new_york_city)
    let term4 = SomeMvTerm SMvPredT $ MvApp
           (MvApp (livesIn Ground livesInType) (MvEntity $ Ground (SMvBaseT SPerson) Nate))
	           (MvEntity $ Var (SMvBaseT SPlace) "X") -- livesIn(nate, X: Place)
	           
    let term5 = SomeMvTerm (SMvBaseT SPlace) $ MvEntity $ Var (SMvBaseT SPlace) "X" -- X: Place
    let term6 = SomeMvTerm (SMvBaseT SPlace) $ MvEntity $ Ground (SMvBaseT SPlace) NewYorkCity -- new_york_city
    
    -- Unification examles:
    let unifier = unify term1 term2
    putStrLn "Typing test:"
    -- print $ term6
    print $ typeOfSome term6
    putStrLn "First Unification Test: (X = nate)"
    print unifier
    let unifier2 = unify term3 term4
    putStrLn "Second Unification Test: (X = new york city)"
    print unifier2
    putStrLn "Third Unification Test: (X = new york city)"
    print $ unify term5 term6
    putStrLn "Search test:"
    -- Search example:

    -- lives_in(nate, X)
    let goal = MvGoal [
            SomeMvTerm SMvPredT $ MvApp (MvApp (livesIn Ground livesInType) (MvEntity $ Ground (SMvBaseT SPerson) Nate))
            (MvEntity $ Var (SMvBaseT SPlace) "X")
          ]
    
    let searchResults = bfs $ search exampleProgram goal
    print searchResults
    -- Query API example:
    -- let Just query = mkQuery ((SMvBaseT SPlace) `SCons` SNil) goal id
    -- print $ runQuery bfs query exampleProgram
    pure ()
    
