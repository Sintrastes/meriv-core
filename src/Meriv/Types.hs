
module Meriv.Types where

import qualified BasePrelude as BP
import Data.Typeable
import Control.Unification
import Data.Functor.Identity
import Meriv.Util.Functor
import Data.Singletons.TH
import Data.Singletons.Base.TypeRepTYPE

data MvType s where
  MvHsT   :: TYPE -> MvType s 
  MvBaseT :: s -> MvType s
  MvFunT  :: MvType s -> MvType s -> MvType s
  MvPredT :: MvType s

instance PartialOrd s => PartialOrd (MvType s) where
  MvPredT    <= MvPredT      = True
  MvFunT x y <= MvFunT x' y' = x >= x' && y <= y' 
  MvBaseT x  <= MvBaseT y     = x <= y
  MvHsT x    <= MvHsT y      = x BP.== y
  _          <= _            = False

$(genSingletons [''MvType])
$(singDecideInstances [''MvType])

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
  newtype Unifier (MvTerm (VarT a) s e 'MvPredT) a
    = MvUnifier [(a, SomeMvTerm (VarT a) s e)]
        deriving(Semigroup, Monoid)
  
  compose (MvUnifier u1) (MvUnifier u2) = MvUnifier $  
      undefined
      -- Todo: Need to mapMaybe here based on whether or not
      -- the types line up.
      -- (map (\(v, SomeMvTerm t) -> (v, SomeMvTerm $ subs (MvUnifier u2) t)) u1) ++ u2

  subs u term = case term of
      MvHs     (Var v) -> undefined
      MvEntity (Var v) -> undefined
      MvApp x y        -> MvApp (subs u x) (subs u y)
      otherwise        -> term
  
  unify (MvApp x y) (MvApp x' y') = do
      -- Note: Need to use singletons here to
      -- check if the two types are the same.
      xu <- unify x x'
      -- yu <- unify y y' 
      return $ undefined -- xu `compose` yu
  unify (MvEntity (Var x)) e@(MvEntity (Ground y)) = return $ MvUnifier [(x, SomeMvTerm e)]
  unify e@(MvEntity (Ground y)) (MvEntity (Var x)) = return $ MvUnifier [(x, SomeMvTerm e)]
  unify (MvHs (Var x)) e@(MvHs (Ground y)) = return $ MvUnifier [(x, SomeMvTerm e)]
  unify e@(MvHs (Ground y)) (MvHs (Var x)) = return $ MvUnifier [(x, SomeMvTerm e)]

newtype MvGoal a s (e :: MvType s -> *)
  = MvGoal [SomeMvTerm (VarT a) s e]

data MvClause a s (e :: MvType s -> *) = MvClause {
  head :: SomeMvTerm (VarT a) s e,
  body :: [SomeMvTerm (VarT a) s e]
}

type MvRule a s (e :: MvType s -> *)
  = MvClause a s e

newtype MvRules a s (e :: MvType s -> *)
  = MvRules [MvRule a s e]

-- | Converts an expression into a ground expression
--   if it has no free variables.
ground :: MvTerm (VarT v) s e t -> Maybe (MvTerm Identity s e t)
ground = \case
  MvHs (Ground x) -> Just $ MvHs (Identity x)
  MvHs (Ground x) -> Just $ MvHs (Identity x)
  MvApp mX mY -> do
    x <- ground mX
    y <- ground mY
    return $ MvApp x y
  otherwise -> Nothing

groundSome (SomeMvTerm e)
  = SomeMvTerm <$> ground e
