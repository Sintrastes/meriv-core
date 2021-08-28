{-# language NoImplicitPrelude #-}

module Prelude
  ( module C
  , module Prelude
  , module Data.PartialOrd
  ) where

import BasePrelude as C hiding ((<=),(>=),(==),(>),(<),compare,elem,(/=),notElem)
import BasePrelude as BasePrelude
import Data.PartialOrd

-- instance Ord a => PartialOrd a where
--   x <= y = x BasePrelude.<= y