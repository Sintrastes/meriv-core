
module Meriv.Types where

import qualified BasePrelude as BP
import Data.Typeable
import Control.Unification
import Data.Functor.Identity
import Meriv.Util.Functor
import Data.Singletons.Decide
import Data.Singletons.Base.TH
import Data.Kind
import Data.Typeable
import GHC.Exts
import Data.Singletons.TH.CustomStar
import Unsafe.Coerce

-- Note: We have to use this, because
-- singletons does not currently play well with
-- TypeRep
data HsRep =
    IntR
  | StringR
  | MaybeR HsRep
    deriving (Eq, Ord, Read, Show)

type family ToHsType (r :: HsRep) :: * where
  ToHsType IntR    = Int
  ToHsType StringR = String
  
data MvType s where
  MvHsT   :: HsRep -> MvType s 
  MvBaseT :: s -> MvType s
  MvFunT  :: MvType s -> MvType s -> MvType s
  MvPredT :: MvType s

instance PartialOrd s => PartialOrd (MvType s) where
  MvPredT    <= MvPredT      = True
  MvFunT x y <= MvFunT x' y' = x >= x' && y <= y' 
  MvBaseT x  <= MvBaseT y    = x <= y
  MvHsT x    <= MvHsT y      = x BP.== y
  _          <= _            = False

$(genSingletons [''HsRep, ''MvType])
$(singDecideInstances [''HsRep, ''MvType])

data MvTerm f s (e :: MvType s -> *) (t :: MvType s) where
  MvHs      :: Sing ('MvHsT @s rep) -> f (ToHsType rep) -> MvTerm f s e ('MvHsT rep)
  MvEntity  :: Sing x -> f (e x) -> MvTerm f s e x
  MvApp     :: MvTerm f s e ('MvFunT x y) -> MvTerm f s e x -> MvTerm f s e y

typeOfMv :: MvTerm f s e t -> Sing t
typeOfMv (MvHs s _) = s
typeOfMv (MvEntity s _) = s
typeOfMv (MvApp f x) = typeOfMv f `unsafeTypeApp` typeOfMv x
  where unsafeTypeApp (SMvFunT x y) _ = unsafeCoerce y

type GroundMvTerm s (e :: MvType s -> *) t
  = MvTerm Identity s e t 

data SomeMvTerm f s (e :: MvType s -> *)
  = forall t. SomeMvTerm (MvTerm f s e t) 

type SomeGroundMvTerm s (e :: MvType s -> *)
  = SomeMvTerm Identity s e

instance Eq a => Unifiable (MvTerm (VarT a) s e t) a where
  newtype Unifier (MvTerm (VarT a) s e t) a
    = MvUnifier [(a, SomeMvTerm (VarT a) s e)]
        deriving(Semigroup, Monoid)
  
  compose (MvUnifier u1) (MvUnifier u2) = MvUnifier $  
      undefined
      -- Todo: Need to mapMaybe here based on whether or not
      -- the types line up.
      -- (map (\(v, SomeMvTerm t) -> (v, SomeMvTerm $ subs (MvUnifier u2) t)) u1) ++ u2

  subs u term = case term of
      MvHs     s (Var v) -> maybe term (coerceSomeTerm s) (lookup v u)
      MvEntity s (Var v) -> maybe term (coerceSomeTerm s) (lookup v u)
      MvApp x y          -> MvApp (subs u x) (subs u y)
      otherwise          -> term
  
  unify (MvApp x y) (MvApp x' y') = do
      -- Note: Need to use singletons here to
      -- check if the two types are the same.
      xu <- unify x x'
      yu <- unify y y' 
      return $ undefined -- xu `compose` yu
  unify (MvEntity t1 (Var x)) e@(MvEntity t2 (Ground y)) =
      case t1 %~ t2 of 
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing
  unify e@(MvEntity t1 (Ground y)) (MvEntity t2 (Var x)) =
      case t1 %~ t2 of 
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing
  unify (MvHs t1 (Var x)) e@(MvHs t2 (Ground y)) = return $ MvUnifier [(x, SomeMvTerm e)]
  unify e@(MvHs t1 (Ground y)) (MvHs t2 (Var x)) = return $ MvUnifier [(x, SomeMvTerm e)]

instance Eq a => Unifiable (SomeMvTerm (VarT a) s e) a where
  newtype Unifier (SomeMvTerm (VarT a) s e) a
    = SomeMvUnifier [(a, SomeMvTerm (VarT a) s e)]
        deriving(Semigroup, Monoid)
  
  compose (SomeMvUnifier u1) (SomeMvUnifier u2) = SomeMvUnifier $  
      undefined
      -- Todo: Need to mapMaybe here based on whether or not
      -- the types line up.
      -- (map (\(v, SomeMvTerm t) -> (v, SomeMvTerm $ subs (MvUnifier u2) t)) u1) ++ u2

coerceSomeTerm :: Sing t -> SomeMvTerm f s e -> MvTerm f s e t
coerceSomeTerm _ (SomeMvTerm x) = unsafeCoerce x

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
  MvHs s (Ground x) -> Just $ MvHs s (Identity x)
  MvEntity s (Ground x) -> Just $ MvEntity  s (Identity x)
  MvApp mX mY -> do
    x <- ground mX
    y <- ground mY
    return $ MvApp x y
  otherwise -> Nothing

groundSome (SomeMvTerm e)
  = SomeMvTerm <$> ground e
