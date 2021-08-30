
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

data MvTerm s (e :: MvType s -> *) (f :: MvType s -> * -> *) (t :: MvType s) where
  MvHs      :: Sing ('MvHsT @s rep) -> f ('MvHsT @s rep) (ToHsType rep) -> MvTerm s e f ('MvHsT rep)
  MvEntity  :: f x (e x) -> MvTerm s e f x
  MvApp     :: MvTerm s e f ('MvFunT x y) -> MvTerm s e f x -> MvTerm s e f y

-- | Type class for a schema whose entities types can
-- be inferred.
class SingKind s => SinglyTyped s (e :: MvType s -> *) where
  getTypeSing :: e x -> Sing x

typeOfGroundMv :: SinglyTyped s e => MvTerm s e IdT t -> Sing t
typeOfGroundMv (MvHs s x) = s
typeOfGroundMv (MvEntity (Id x)) = getTypeSing x
typeOfGroundMv (MvApp f x) = resultType (typeOfGroundMv f)

typeOfMv :: SinglyTyped s e => MvTerm s e (VarT a) t -> Sing t
typeOfMv (MvHs s x)            = s
typeOfMv (MvEntity (Ground x)) = getTypeSing x
typeOfMv (MvEntity (Var s x))  = s
typeOfMv (MvApp f x)           = resultType (typeOfMv f)

resultType :: Sing ('MvFunT x y) -> Sing y
resultType (SMvFunT a b) = b  

type GroundMvTerm s (e :: MvType s -> *) t
  = MvTerm s e IdT t

data SomeMvTerm s (e :: MvType s -> *) f
  = forall t. SomeMvTerm (MvTerm s e f t)

type SomeGroundMvTerm s (e :: MvType s -> *)
  = SomeMvTerm s e IdT

type CommonUnifier s e a = [(a, SomeMvTerm s e (VarT a))]

fromSomeUnifier (SomeMvUnifier u) = MvUnifier u

toSomeUnifier (MvUnifier u) = SomeMvUnifier u

instance (SDecide s, SinglyTyped s e, Eq a) => Unifiable (MvTerm s e (VarT a) t) a where
  newtype Unifier (MvTerm s e (VarT a) t) a
    = MvUnifier (CommonUnifier s e a)
        deriving(Semigroup, Monoid)

  compose (MvUnifier u1) (MvUnifier u2) = MvUnifier $
      (map (\(v, SomeMvTerm t) -> (v, SomeMvTerm $ subs (MvUnifier u2) t)) u1)
         ++ u2

  subs (MvUnifier u) term = case term of
      MvHs   _ (Var s v) -> maybe term (coerceSomeTerm s) (lookup v u)
      MvEntity (Var s v) -> maybe term (coerceSomeTerm s) (lookup v u)
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
  unify (MvEntity (Var t1 x)) e@(MvEntity (Ground y)) = let t2 = typeOfMv e in
      case t1 %~ t2 of
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing
  unify e@(MvEntity (Ground y)) (MvEntity (Var t1 x)) = let t2 = typeOfMv e in
      case t1 %~ t2 of
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing
  unify (MvHs _ (Var t1 x)) e@(MvHs t2 (Ground y)) = 
      case t1 %~ t2 of
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing
  unify e@(MvHs t2 (Ground y)) (MvHs _ (Var t1 x)) = 
      case t1 %~ t2 of
          Proved Refl -> return $ MvUnifier [(x, SomeMvTerm e)]
          otherwise   -> Nothing

instance (SDecide s, SinglyTyped s e, Eq a) => Unifiable (SomeMvTerm s e (VarT a)) a where
  newtype Unifier (SomeMvTerm s e (VarT a)) a
    = SomeMvUnifier (CommonUnifier s e a)
        deriving(Semigroup, Monoid)

  compose (SomeMvUnifier u1) (SomeMvUnifier u2) = SomeMvUnifier $
      (map (\(v, t) -> (v, subs (SomeMvUnifier u2) t)) u1) ++ u2

  subs (SomeMvUnifier u) (SomeMvTerm term)
      = SomeMvTerm $ subs (MvUnifier u) term

  unify (SomeMvTerm x) (SomeMvTerm y) =
      case typeOfMv x %~ typeOfMv y of
          Proved Refl -> toSomeUnifier <$> unify x y
	  otherwise   -> Nothing

coerceSomeTerm :: Sing t -> SomeMvTerm s e f -> MvTerm s e f t
coerceSomeTerm _ (SomeMvTerm x) = unsafeCoerce x

newtype MvGoal a s (e :: MvType s -> *)
  = MvGoal [SomeMvTerm s e (VarT a)]

data MvClause a s (e :: MvType s -> *) = MvClause {
  head :: SomeMvTerm s e (VarT a),
  body :: [SomeMvTerm s e (VarT a)]
}

type MvRule a s (e :: MvType s -> *)
  = MvClause a s e

newtype MvRules a s (e :: MvType s -> *)
  = MvRules [MvRule a s e]

-- | Converts an expression into a ground expression
--   if it has no free variables.
ground :: MvTerm s e (VarT v) t -> Maybe (MvTerm s e IdT t)
ground = \case
  MvHs s (Ground x) -> Just $ MvHs s (Id x)
  MvEntity (Ground x) -> Just $ MvEntity (Id x)
  MvApp mX mY -> do
    x <- ground mX
    y <- ground mY
    return $ MvApp x y
  otherwise -> Nothing

groundSome (SomeMvTerm e)
  = SomeMvTerm <$> ground e
