
module Meriv.Util.HList where

data HList as where
    HNil :: HList '[]
    HCons :: a -> HList as -> HList (a ': as)