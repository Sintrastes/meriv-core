
module Meriv.Util.Functor where

data VarT x a
  = Ground a
  | Var x