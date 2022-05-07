-- | This module exposes a typed Query interface for Meriv. Since the
--   unification backend that Meriv uses for it's serach procedure is
--   untyped, this query interface provides a typesafe interface
--   to interface with this underlying engine.
--

module Meriv.Query(
    MvQuery,
    mkQuery,
    runQuery
) where

import Prelude hiding (sort)
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude.List
import Meriv.Interp
import Meriv.Types
import Meriv.Util.Functor
import Meriv.Util.HList
import Data.List
import Control.Unification
import BasePrelude as BP

type family FMapTerms s e (as :: [MvType t]) :: [*] where
  FMapTerms s e '[] = '[]
  FMapTerms s e (x ': xs) = MvTerm s e IdT x ': FMapTerms s e xs

-- | A query is a goal with a specified list of 
--   free variables of specific types, specified by an
--   SList of MerivTypes. Queries are constructed
--   with the smart constructor mkQuery.
data MvQuery s e v a = forall (as :: [MvType s]). MvQuery {
    queryType :: SList as,
    queryGoal :: MvGoal v s e,
    getResult :: HList (FMapTerms s e as) -> a
}

-- | Smart constructor for queries. The given term's free variables
--   should be numbered 0 to n, where n is the length of the passes
--   SList, and each variable should have a type that corresponds to
--   the type specified in the SList. Otherwise, this function will return 
--   Nothing.
mkQuery :: forall s e a (as :: [MvType s]). (
    Eq s, Ord (Demote s), SingKind s,
    HasTypedVariables (MvGoal String s e) (MvType (Demote s)) String) 
  => SList as 
  -> MvGoal String s e
  -> (HList (FMapTerms s e as) -> a)
  -> Maybe (MvQuery s e String a)
mkQuery types goal select = if variableOccurances BP.== queryVariables
  then Just $ MvQuery types goal select
  else Nothing
    where variableOccurances = fmap snd $ sort $ typedVariables goal
          queryVariables = fromSing types

-- | Execute a Meriv query by providing a search function and program.
runQuery :: _ => (SearchTree v s e -> [MvSolution v s e]) -> MvQuery s e v a -> MvRules v s e -> [a]
runQuery searchFn (MvQuery queryType queryGoal getResult) program = getResult <$> 
    coerceSearchResult queryType <$>
        (searchFn $ search program queryGoal)

-- | Partial function. Coerces an untyped Solution, obtained by running a search procedure on a goal
--   into a list of terms of the specified type. The variables in the solution
--   must be numbered from 0 to n, where the types of the bindings correspond to the types specified
--   in the SList, otherwise this function will fail.
coerceSearchResult :: forall s e v (as :: [MvType s]). _ => SList as -> MvSolution v s e -> HList (FMapTerms s e as) 
coerceSearchResult ss (MvSolution solution) = coerceSearchResult' ss (MvSolution $ sort solution)

coerceSearchResult' :: forall s e v (as :: [MvType s]). SDecide s => SList as -> MvSolution v s e -> HList (FMapTerms s e as) 
coerceSearchResult' SNil (MvSolution _) = HNil
coerceSearchResult' (SCons x xs) (MvSolution ((_,y):ys)) = 
    coerceSomeTerm x y `HCons` coerceSearchResult' xs (MvSolution ys)
