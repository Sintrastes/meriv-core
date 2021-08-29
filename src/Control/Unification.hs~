
module Control.Unification where

-- type Unifier v x = [(v,x)]

class Variable t v | t -> v where
  variables :: t -> [v]

class HasTypedVariables term typ v | term -> v, term -> typ, typ -> v where
  typedVariables :: term -> [(v, typ)]

class Unifiable t v | t -> v where
  data Unifier t v
  emptyUnifier :: Unifier t v

  subs  :: Unifier t v -> t -> t
  unify :: t -> t -> Maybe (Unifier t v)
  compose :: Unifier t v -> Unifier t v -> Unifier t v

  allUnify :: [t] -> [t] -> Maybe (Unifier t v)
  allUnify [] [] = Just emptyUnifier
  allUnify (x:xs) (y:ys) = do
    u  <- unify x y
    us <- allUnify xs ys
    return $ u `compose` us

class Freshenable x v | x -> v where
  freshen :: [v] -> x -> x