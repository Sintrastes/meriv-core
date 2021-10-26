-- | This module exposes a typed Query interface for Meriv. Since the
--   unification backend that Meriv uses for it's serach procedure is
--   un-typed, this query interface provides a typesafe interface
--   to interface with this underlying engine.
--

module Meriv.Query(
    Query,
    mkQuery,
    runQuery
) where

import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude.List
import Meriv.Types
import Meriv.Util.Functor
import Meriv.Util.HList
import Data.List
import Control.Unification

-- | A query is a goal with a specified list of 
--   free variables of specific types, specified by an
--   SList of MerivTypes. Queries are constructed
--   with the smart constructor mkQuery.
data Query s e v a = forall (as :: [MerivType t]). Query {
    queryType :: SList as,
    queryGoal :: MvGoal v,
    getResult :: HList (FMapTerms s e v as) -> a
}

-- | Smart constructor for queries. The given term's free variables
--   should be numbered 0 to n, where n is the length of the passes
--   SList, and each variable should have a type that corresponds to
--   the type specified in the SList. Otherwise, this function will return 
--   Nothing.
mkQuery :: forall t m g (as :: [MerivType t]). (
    SingKind t, 
    Eq (Demote t),
    Ord t, Ord (Demote t),
    HasTypedVariables (Goal Nat t m g) (MerivType (Demote t)) t) 
  => SList as 
  -> MvGoal s e v
  -> (HList (FMapTerms s e v as) -> a)
  -> Maybe (MvQuery s e v a)
mkQuery types goal = if variableOccurances == queryVariables
  then Just $ Query types goal
  else Nothing
    where variableOccurances = fmap snd $ sort $ typedVariables goal
          queryVariables = fromSing types

-- | Execute a Meriv query by providing a search function and program.
runQuery :: (SearchTree v s e -> [MvSolution v s e]) -> Query s e v a -> [a]
runQuery searchFn query program = 
    coerceSearchResult (queryType query) $
        searchFn $ search program (queryGoal query) 

-- | Partial function. Coerces an untyped Solution, obtained by running a search procedure on a goal
--   into a list of terms of the specified type. The variables in the solution
--   must be numbered from 0 to n, where the types of the bindings correspond to the types specified
--   in the SList, otherwise this function will fail.
coerceSearchResult :: forall s e v (as :: [MvType s]). _ => SList as -> Solution Nat t m -> List (FMapTerms s e v as) 
coerceSearchResult ss (Solution solution) = coerceSearchResult' ss (Solution $ sort solution)

coerceSearchResult' :: forall s e v (as :: [MerivType t]). SList as -> Solution s e v -> List (FMapTerms s e v as) 
coerceSearchResult' SNil (Solution _) = Nil
coerceSearchResult' (SCons x xs) (Solution ((_,y):ys)) = 
    coerceSomeExpr x y :. coerceSearchResult' xs (Solution ys)