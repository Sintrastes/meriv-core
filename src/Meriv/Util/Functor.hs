
module Meriv.Util.Functor where

import Data.Singletons

data VarT x t a
  = Ground a
  | Var (Sing t) x

data IdT t a = Id a