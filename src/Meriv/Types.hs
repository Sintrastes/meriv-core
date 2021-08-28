
module Meriv.Types where

import qualified BasePrelude as BP
import Data.Typeable
import Control.Unification
import Data.Functor.Identity
import Meriv.Util.Functor

data MvType s where
  MvHsT   :: TypeRep -> MvType s 
  MvBaseT :: s -> MvType s
  MvFunT  :: MvType s -> MvType s -> MvType s
  MvPredT :: MvType s

instance PartialOrd s => PartialOrd (MvType s) where
  MvPredT    <= MvPredT      = True
  MvFunT x y <= MvFunT x' y' = x >= x' && y <= y' 
  MvBaseT x  <= MvBaseT y     = x <= y
  MvHsT x    <= MvHsT y      = x BP.== y
  _          <= _            = False

data MvTerm f s (e :: MvType s -> *) (t :: MvType s) where
  MvHs      :: (Eq a, Typeable a) => f a -> MvTerm f s e ('MvHsT typeRep)
  MvEntity  :: f (e x) -> MvTerm f s e x
  MvApp     :: MvTerm f s e ('MvFunT x y) -> MvTerm f s e x -> MvTerm f s e y

type GroundMvTerm s (e :: MvType s -> *) t
  = MvTerm Identity s e t 

data SomeMvTerm f s (e :: MvType s -> *)
  = forall t. SomeMvTerm (MvTerm f s e t) 

type SomeGroundMvTerm s (e :: MvType s -> *)
  = SomeMvTerm Identity s e

instance Eq a => Unifiable (MvTerm (VarT a) s e 'MvPredT) a where
  data Unifier (MvTerm (VarT a) s e 'MvPredT) a
    = MvUnifier [(a, SomeMvTerm (VarT a) s e)]

  compose (MvUnifier u1) (MvUnifier u2) = MvUnifier $  
      undefined
      -- Todo: Need to mapMaybe here based on whether or not
      -- the types line up.
      -- (map (\(v, SomeMvTerm t) -> (v, SomeMvTerm $ subs (MvUnifier u2) t)) u1) ++ u2

  subs u term = case term of
      MvHs (Var v)     -> undefined
      MvEntity (Var v) -> undefined
      MvApp x y        -> undefined
      otherwise        -> term
  
  unify (MvApp x y) (MvApp x' y') = do
      -- Note: Need to use singletons here to
      -- check if the two types are the same.
      -- xu <- unify x x'
      -- yu <- unify y y' 
      return $ undefined -- xu `compose` yu

newtype MvGoal a s (e :: MvType s -> *)
  = MvGoal [SomeMvTerm (VarT a) s e]

data MvClause a s (e :: MvType s -> *) = MvClause {
  head :: SomeMvTerm (VarT a) s e,
  body :: [SomeMvTerm (VarT a) s e]
}

newtype MvSolution v s (e :: MvType s -> *)
  = MvSolution [(v, SomeGroundMvTerm s e)]

type MvRule a s (e :: MvType s -> *)
  = MvClause a s e

newtype MvRules a s (e :: MvType s -> *)
  = MvRules [MvRule a s e]