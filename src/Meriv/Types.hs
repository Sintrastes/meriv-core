
module Meriv.Types where

import qualified BasePrelude as BP
import Data.Typeable
import Control.Unification
import Data.Functor.Identity
import Meriv.Util.Functor
import Data.Singletons.Decide
import Data.Kind
import Data.Typeable
import GHC.Exts
import Data.Singletons
import Unsafe.Coerce
import Data.Maybe
import Data.Type.Coercion
import Data.Type.Equality

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

instance Show s => Show (MvType s) where
  show (MvHsT x)    = show x
  show (MvBaseT x)  = show x
  show (MvFunT x y) = show x ++ " -> " ++ show y
  show MvPredT = "pred" 

instance PartialOrd s => PartialOrd (MvType s) where
  MvPredT    <= MvPredT      = True
  MvFunT x y <= MvFunT x' y' = x >= x' && y <= y'
  MvBaseT x  <= MvBaseT y    = x <= y
  MvHsT x    <= MvHsT y      = x BP.== y
  _          <= _            = False

type IntRSym0 :: HsRep
type family IntRSym0 :: HsRep where
  IntRSym0 = 'IntR
type StringRSym0 :: HsRep
type family StringRSym0 :: HsRep where
  StringRSym0 = 'StringR
type MaybeRSym0 :: (~>) HsRep HsRep
data MaybeRSym0 :: (~>) HsRep HsRep
  where
      MaybeRSym0KindInference :: SameKind (Apply MaybeRSym0 arg_a4tv) (MaybeRSym1 arg_a4tv) =>
                                   MaybeRSym0 a6989586621679026998
type instance Apply MaybeRSym0 a6989586621679026998 = 'MaybeR a6989586621679026998
type MaybeRSym1 :: HsRep -> HsRep
type family MaybeRSym1 (a6989586621679026998 :: HsRep) :: HsRep where
      MaybeRSym1 a6989586621679026998 = 'MaybeR a6989586621679026998
type SHsRep :: HsRep -> Type
data SHsRep :: HsRep -> Type
      where
        SIntR :: SHsRep ('IntR :: HsRep)
        SStringR :: SHsRep ('StringR :: HsRep)
        SMaybeR :: forall (n_a4tx :: HsRep).
                   (Sing n_a4tx) -> SHsRep ('MaybeR n_a4tx :: HsRep)
type instance Sing @HsRep = SHsRep
instance SingKind HsRep where
      type Demote HsRep = HsRep
      fromSing SIntR = IntR
      fromSing SStringR = StringR
      fromSing (SMaybeR b_a4tz) = MaybeR (fromSing b_a4tz)
      toSing IntR = SomeSing SIntR
      toSing StringR = SomeSing SStringR
      toSing (MaybeR (b_a4tB :: Demote HsRep))
        = case toSing b_a4tB :: SomeSing HsRep of {
            SomeSing c_a4tC -> SomeSing (SMaybeR c_a4tC) }
instance SingI 'IntR where
      sing = SIntR
instance SingI 'StringR where
      sing = SStringR
instance SingI n_a4tx => SingI ('MaybeR (n_a4tx :: HsRep)) where
      sing = SMaybeR sing
instance SingI (MaybeRSym0 :: (~>) HsRep HsRep) where
      sing = (singFun1 @MaybeRSym0) SMaybeR
type MvHsTSym0 :: forall (s_a1tI :: Type).
                      (~>) HsRep (MvType s_a1tI)
data MvHsTSym0 :: (~>) HsRep (MvType s_a1tI)
      where
        MvHsTSym0KindInference :: SameKind (Apply MvHsTSym0 arg_a4uu) (MvHsTSym1 arg_a4uu) =>
                                  MvHsTSym0 a6989586621679027059
type instance Apply MvHsTSym0 a6989586621679027059 = 'MvHsT a6989586621679027059
type MvHsTSym1 :: forall (s_a1tI :: Type). HsRep -> MvType s_a1tI
type family MvHsTSym1 (a6989586621679027059 :: HsRep) :: MvType s_a1tI where
      MvHsTSym1 a6989586621679027059 = 'MvHsT a6989586621679027059
type MvBaseTSym0 :: forall (s_a1tJ :: Type).
                        (~>) s_a1tJ (MvType s_a1tJ)
data MvBaseTSym0 :: (~>) s_a1tJ (MvType s_a1tJ)
      where
        MvBaseTSym0KindInference :: SameKind (Apply MvBaseTSym0 arg_a4uw) (MvBaseTSym1 arg_a4uw) =>
                                    MvBaseTSym0 a6989586621679027061
type instance Apply MvBaseTSym0 a6989586621679027061 = 'MvBaseT a6989586621679027061
type MvBaseTSym1 :: forall (s_a1tJ :: Type).
                        s_a1tJ -> MvType s_a1tJ
type family MvBaseTSym1 (a6989586621679027061 :: s_a1tJ) :: MvType s_a1tJ where
      MvBaseTSym1 a6989586621679027061 = 'MvBaseT a6989586621679027061
type MvFunTSym0 :: forall (s_a1tK :: Type).
                       (~>) (MvType s_a1tK) ((~>) (MvType s_a1tK) (MvType s_a1tK))
data MvFunTSym0 :: (~>) (MvType s_a1tK) ((~>) (MvType s_a1tK) (MvType s_a1tK))
      where
        MvFunTSym0KindInference :: SameKind (Apply MvFunTSym0 arg_a4uy) (MvFunTSym1 arg_a4uy) =>
                                   MvFunTSym0 a6989586621679027063
type instance Apply MvFunTSym0 a6989586621679027063 = MvFunTSym1 a6989586621679027063
type MvFunTSym1 :: forall (s_a1tK :: Type).
                       MvType s_a1tK -> (~>) (MvType s_a1tK) (MvType s_a1tK)
data MvFunTSym1 (a6989586621679027063 :: MvType s_a1tK) :: (~>) (MvType s_a1tK) (MvType s_a1tK)
      where
        MvFunTSym1KindInference :: SameKind (Apply (MvFunTSym1 a6989586621679027063) arg_a4uy) (MvFunTSym2 a6989586621679027063 arg_a4uy) =>
                                   MvFunTSym1 a6989586621679027063 a6989586621679027064
type instance Apply (MvFunTSym1 a6989586621679027063) a6989586621679027064 = 'MvFunT a6989586621679027063 a6989586621679027064
type MvFunTSym2 :: forall (s_a1tK :: Type).
                       MvType s_a1tK -> MvType s_a1tK -> MvType s_a1tK
type family MvFunTSym2 (a6989586621679027063 :: MvType s_a1tK) (a6989586621679027064 :: MvType s_a1tK) :: MvType s_a1tK where
      MvFunTSym2 a6989586621679027063 a6989586621679027064 = 'MvFunT a6989586621679027063 a6989586621679027064
type MvPredTSym0 :: forall (s_a1tL :: Type). MvType s_a1tL
type family MvPredTSym0 :: MvType s_a1tL where
      MvPredTSym0 = 'MvPredT
type SMvType :: forall (s_a1tH :: Type). MvType s_a1tH -> Type
data SMvType :: forall (s_a1tH :: Type). MvType s_a1tH -> Type
      where
        SMvHsT :: forall (s_a1tI :: Type) (n_a4uC :: HsRep).
                  (Sing n_a4uC) -> SMvType ('MvHsT n_a4uC :: MvType s_a1tI)
        SMvBaseT :: forall (s_a1tJ :: Type) (n_a4uE :: s_a1tJ).
                    (Sing n_a4uE) -> SMvType ('MvBaseT n_a4uE :: MvType s_a1tJ)
        SMvFunT :: forall (s_a1tK :: Type)
                          (n_a4uG :: MvType s_a1tK)
                          (n_a4uH :: MvType s_a1tK).
                   (Sing n_a4uG)
                   -> (Sing n_a4uH)
                   -> SMvType ('MvFunT n_a4uG n_a4uH :: MvType s_a1tK)
        SMvPredT :: forall (s_a1tL :: Type).
                    SMvType ('MvPredT :: MvType s_a1tL)
type instance Sing @(MvType s_a1tH) = SMvType
instance SingKind s_a1tH => SingKind (MvType s_a1tH) where
  type Demote (MvType s_a1tH) = MvType (Demote s_a1tH)
  fromSing (SMvHsT b_a4uK) = MvHsT (fromSing b_a4uK)
  fromSing (SMvBaseT b_a4uL) = MvBaseT (fromSing b_a4uL)
  fromSing (SMvFunT b_a4uM b_a4uN)
        = (MvFunT (fromSing b_a4uM)) (fromSing b_a4uN)
  fromSing SMvPredT = MvPredT
  toSing (MvHsT (b_a4uP :: Demote HsRep))
        = case toSing b_a4uP :: SomeSing HsRep of {
            SomeSing c_a4uQ -> SomeSing (SMvHsT c_a4uQ) }
  toSing (MvBaseT (b_a4uR :: Demote s_a1tJ))
        = case toSing b_a4uR :: SomeSing s_a1tJ of {
            SomeSing c_a4uS -> SomeSing (SMvBaseT c_a4uS) }
  toSing
        (MvFunT (b_a4uT :: Demote (MvType s_a1tK))
                (b_a4uU :: Demote (MvType s_a1tK)))
        = case
              ((,) (toSing b_a4uT :: SomeSing (MvType s_a1tK)))
                (toSing b_a4uU :: SomeSing (MvType s_a1tK))
          of {
            (,) (SomeSing c_a4uV) (SomeSing c_a4uW)
              -> SomeSing ((SMvFunT c_a4uV) c_a4uW) }
  toSing MvPredT = SomeSing SMvPredT
instance SingI n_a4uC => SingI ('MvHsT (n_a4uC :: HsRep)) where
      sing = SMvHsT sing
instance SingI (MvHsTSym0 :: (~>) HsRep (MvType s_a1tI)) where
      sing = (singFun1 @MvHsTSym0) SMvHsT
instance SingI n_a4uE => SingI ('MvBaseT (n_a4uE :: s_a1tJ)) where
      sing = SMvBaseT sing
instance SingI (MvBaseTSym0 :: (~>) s_a1tJ (MvType s_a1tJ)) where
      sing = (singFun1 @MvBaseTSym0) SMvBaseT
instance (SingI n_a4uG, SingI n_a4uH) =>
             SingI ('MvFunT (n_a4uG :: MvType s_a1tK) (n_a4uH :: MvType s_a1tK)) where
      sing = (SMvFunT sing) sing
instance SingI (MvFunTSym0 :: (~>) (MvType s_a1tK) ((~>) (MvType s_a1tK) (MvType s_a1tK))) where
      sing = (singFun2 @MvFunTSym0) SMvFunT
instance SingI d_a4uI =>
             SingI (MvFunTSym1 (d_a4uI :: MvType s_a1tK) :: (~>) (MvType s_a1tK) (MvType s_a1tK)) where
      sing
        = (singFun1 @(MvFunTSym1 (d_a4uI :: MvType s_a1tK)))
            (SMvFunT (sing @d_a4uI))
instance SingI 'MvPredT where
      sing = SMvPredT

instance SDecide HsRep => SDecide HsRep where
      (%~) SIntR SIntR = Proved Refl
      (%~) SIntR SStringR = Disproved (\ x_a9gP -> case x_a9gP of)
      (%~) SIntR (SMaybeR _) = Disproved (\ x_a9gQ -> case x_a9gQ of)
      (%~) SStringR SIntR = Disproved (\ x_a9gR -> case x_a9gR of)
      (%~) SStringR SStringR = Proved Refl
      (%~) SStringR (SMaybeR _) = Disproved (\ x_a9gS -> case x_a9gS of)
      (%~) (SMaybeR _) SIntR = Disproved (\ x_a9gT -> case x_a9gT of)
      (%~) (SMaybeR _) SStringR = Disproved (\ x_a9gU -> case x_a9gU of)
      (%~) (SMaybeR a_a9gV) (SMaybeR b_a9gW)
        = case ((%~) a_a9gV) b_a9gW of
            Proved Refl -> Proved Refl
            Disproved contra_a9gX
              -> Disproved
                   (\ refl_a9gY -> case refl_a9gY of { Refl -> contra_a9gX Refl })
instance SDecide HsRep =>
             TestEquality (SHsRep :: HsRep -> Type) where
      testEquality = decideEquality
instance SDecide HsRep =>
             TestCoercion (SHsRep :: HsRep -> Type) where
      testCoercion = decideCoercion
instance (SDecide HsRep,
              SDecide s_a1tH,
              SDecide (MvType s_a1tH)) =>
             SDecide (MvType s_a1tH) where
      (%~) (SMvHsT a_a9hb) (SMvHsT b_a9hc)
        = case ((%~) a_a9hb) b_a9hc of
            Proved Refl -> Proved Refl
            Disproved contra_a9hd
              -> Disproved
                   (\ refl_a9he -> case refl_a9he of { Refl -> contra_a9hd Refl })
      (%~) (SMvHsT _) (SMvBaseT _)
        = Disproved (\ x_a9hf -> case x_a9hf of)
      (%~) (SMvHsT _) (SMvFunT _ _)
        = Disproved (\ x_a9hg -> case x_a9hg of)
      (%~) (SMvHsT _) SMvPredT = Disproved (\ x_a9hh -> case x_a9hh of)
      (%~) (SMvBaseT _) (SMvHsT _)
        = Disproved (\ x_a9hi -> case x_a9hi of)
      (%~) (SMvBaseT a_a9hj) (SMvBaseT b_a9hk)
        = case ((%~) a_a9hj) b_a9hk of
            Proved Refl -> Proved Refl
            Disproved contra_a9hl
              -> Disproved
                   (\ refl_a9hm -> case refl_a9hm of { Refl -> contra_a9hl Refl })
      (%~) (SMvBaseT _) (SMvFunT _ _)
        = Disproved (\ x_a9hn -> case x_a9hn of)
      (%~) (SMvBaseT _) SMvPredT = Disproved (\ x_a9ho -> case x_a9ho of)
      (%~) (SMvFunT _ _) (SMvHsT _)
        = Disproved (\ x_a9hp -> case x_a9hp of)
      (%~) (SMvFunT _ _) (SMvBaseT _)
        = Disproved (\ x_a9hq -> case x_a9hq of)
      (%~) (SMvFunT a_a9hr a_a9hs) (SMvFunT b_a9ht b_a9hu)
        = case ((,) (((%~) a_a9hr) b_a9ht)) (((%~) a_a9hs) b_a9hu) of
            (,) (Proved Refl) (Proved Refl) -> Proved Refl
            (,) (Disproved contra_a9hv) _
              -> Disproved
                   (\ refl_a9hw -> case refl_a9hw of { Refl -> contra_a9hv Refl })
            (,) _ (Disproved contra_a9hv)
              -> Disproved
                   (\ refl_a9hw -> case refl_a9hw of { Refl -> contra_a9hv Refl })
      (%~) (SMvFunT _ _) SMvPredT
        = Disproved (\ x_a9hx -> case x_a9hx of)
      (%~) SMvPredT (SMvHsT _) = Disproved (\ x_a9hy -> case x_a9hy of)
      (%~) SMvPredT (SMvBaseT _) = Disproved (\ x_a9hz -> case x_a9hz of)
      (%~) SMvPredT (SMvFunT _ _)
        = Disproved (\ x_a9hA -> case x_a9hA of)
      (%~) SMvPredT SMvPredT = Proved Refl
instance (SDecide HsRep,
              SDecide s_a1tH,
              SDecide (MvType s_a1tH)) =>
             TestEquality (SMvType :: MvType s_a1tH
                                                         -> Type) where
      testEquality = decideEquality
instance (SDecide HsRep,
              SDecide s_a1tH,
              SDecide (MvType s_a1tH)) =>
             TestCoercion (SMvType :: MvType s_a1tH
                                                         -> Type) where
      testCoercion = decideCoercion

data MvTerm s (e :: MvType s -> *) (f :: MvType s -> * -> *) (t :: MvType s) where
  MvHs      :: Sing ('MvHsT @s rep) -> f ('MvHsT @s rep) (ToHsType rep) -> MvTerm s e f ('MvHsT rep)
  MvEntity  :: f x (e x) -> MvTerm s e f x
  MvApp     :: MvTerm s e f ('MvFunT x y) -> MvTerm s e f x -> MvTerm s e f y

instance (ShowAllTypes e) => Show (MvTerm s e IdT t) where
    -- show (MvHs SIntR x)    = show x
    -- show (MvHs SStringR x) = show x
    show (MvEntity (Id x)) = showAll x
    show (MvApp x y)       = show x ++ " " ++ show y

instance (ShowAllTypes e) => Show (MvTerm s e (VarT String) t) where
    -- show (MvHs SIntR x)    = show x
    -- show (MvHs SStringR x) = show x
    show (MvEntity (Ground x)) = showAll x
    show (MvEntity (Var _ x))  = x
    show (MvApp x y)           = show x ++ " " ++ show y

class ShowAllTypes (e :: MvType s -> *) where
    showAll :: e t -> String

instance ShowAllTypes e => Show (SomeMvTerm s e IdT) where
  show (SomeMvTerm x) = show x

instance ShowAllTypes e => Show (SomeMvTerm s e (VarT String)) where
  show (SomeMvTerm x) = show x

instance Variable (SomeMvTerm s e (VarT String)) String where
    variables (SomeMvTerm x) = variables x

instance Variable (MvTerm s e (VarT String) t) String where
    variables (MvHs _ (Var _ x)) = [x]
    variables (MvEntity (Var _ x)) = [x]
    variables (MvApp x y) = variables x ++ variables y
    variables _ = []

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

instance (SDecide s, EntityEq s e, SinglyTyped s e, Eq a) => Unifiable (MvTerm s e (VarT a) t) a where
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
  unify (MvEntity (Ground x)) e@(MvEntity (Ground y)) | x `entityEquals` y = return $ MvUnifier []
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
  unify _ _ = Nothing

class EntityEq s (e :: MvType s -> *) | s -> e where
    entityEquals :: e t -> e t -> Bool

instance (ShowAllTypes e) => Show (Unifier (MvTerm s e (VarT String) t) String) where
  show (MvUnifier x) = show x

instance (ShowAllTypes e) => Show (Unifier (SomeMvTerm s e (VarT String)) String) where
  show (SomeMvUnifier x) = show x

instance (SDecide s, EntityEq s e, SinglyTyped s e, Eq a) => Unifiable (SomeMvTerm s e (VarT a)) a where
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

instance Freshenable (MvClause String s e) String where
  freshen vars (MvClause head body) = MvClause (freshen vars head) (freshen vars <$> body)

instance Freshenable (SomeMvTerm s e (VarT String)) String where
  freshen vars (SomeMvTerm x) = SomeMvTerm $ freshen vars x

instance Freshenable (MvTerm s e (VarT String) t) String where
  freshen vars (MvHs t (Var s x))   | x `BP.elem` vars = freshen vars $ MvHs t (Var s ('\'':x))
  freshen vars (MvEntity (Var t x)) | x `BP.elem` vars = freshen vars $ MvEntity (Var t ('\'':x))
  freshen vars (MvApp x y) = MvApp (freshen vars x) (freshen vars y)
  freshen vars x = x

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
