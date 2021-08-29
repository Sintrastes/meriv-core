
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
import Data.Maybe

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

-- | Type class for a schema whose entities types can
-- be inferred.
class SingKind s => SinglyTyped s (e :: MvType s -> *) where
  getTypeSing :: e x -> Sing x

typeOfMv :: MvTerm f s e t -> Sing t
typeOfMv (MvHs s _) = s
typeOfMv (MvEntity s x) = s
typeOfMv (MvApp f x) = resultType (typeOfMv f)

resultType :: Sing ('MvFunT x y) -> Sing y
resultType (SMvFunT a b) = b  

type GroundMvTerm s (e :: MvType s -> *) t
  = MvTerm Identity s e t

data SomeMvTerm f s (e :: MvType s -> *)
  = forall t. SomeMvTerm (MvTerm f s e t)

type SomeGroundMvTerm s (e :: MvType s -> *)
  = SomeMvTerm Identity s e

type CommonUnifier s e a = [(a, SomeMvTerm (VarT a) s e)]

fromSomeUnifier (SomeMvUnifier u) = MvUnifier u

instance (SDecide s, Eq a) => Unifiable (MvTerm (VarT a) s e t) a where
  newtype Unifier (MvTerm (VarT a) s e t) a
    = MvUnifier (CommonUnifier s e a)
        deriving(Semigroup, Monoid)

  compose (MvUnifier u1) (MvUnifier u2) = MvUnifier $
      (map (\(v, SomeMvTerm t) -> (v, SomeMvTerm $ subs (MvUnifier u2) t)) u1)
         ++ u2

  subs (MvUnifier u) term = case term of
      MvHs     s (Var v) -> maybe term (coerceSomeTerm s) (lookup v u)
      MvEntity s (Var v) -> maybe term (coerceSomeTerm s) (lookup v u)
      MvApp x y          -> MvApp (subs (MvUnifier u) x) (subs (MvUnifier u) y)
      otherwise          -> term

  unify (MvApp x y) (MvApp x' y') = do
      -- Note: Need to use singletons here to
      -- check if the two types are the same.
      xu <- case typeOfMv x %~ typeOfMv x' of
                Proved Refl -> fromSomeUnifier <$> unify (SomeMvTerm x) (SomeMvTerm x')
                otherwise   -> Nothing
      yu <- case typeOfMv y %~ typeOfMv y' of
                Proved Refl -> fromSomeUnifier <$> unify (SomeMvTerm y) (SomeMvTerm y')
                otherwise   -> Nothing
      return $ xu `compose` yu
  unify (MvEntity t1 (Var x)) e@(MvEntity t2 (Ground y)) =
      case t1 %~ t2 of
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing
  unify e@(MvEntity t1 (Ground y)) (MvEntity t2 (Var x)) =
      case t1 %~ t2 of
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing
  unify (MvHs t1 (Var x)) e@(MvHs t2 (Ground y)) =
      case t1 %~ t2 of
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing
  unify e@(MvHs t1 (Ground y)) (MvHs t2 (Var x)) =
      case t1 %~ t2 of
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing

instance Eq a => Unifiable (SomeMvTerm (VarT a) s e) a where
  newtype Unifier (SomeMvTerm (VarT a) s e) a
    = SomeMvUnifier (CommonUnifier s e a)
        deriving(Semigroup, Monoid)

  compose (SomeMvUnifier u1) (SomeMvUnifier u2) = SomeMvUnifier $
      (map (\(v, t) -> (v, subs (SomeMvUnifier u2) t)) u1) ++ u2

  subs (SomeMvUnifier u) term = undefined

  unify x y = undefined

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
