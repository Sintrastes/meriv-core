
module Meriv.Util.Functor where

import Data.Singletons

data VarT x e t
  = Ground (Sing t) (e t)
  | Var (Sing t) x

data IdT e t = Id (Sing t) (e t)
