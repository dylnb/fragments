
module Padded where

import Control.Applicative
import Data.Traversable
import Data.List

data Padded m = (:-) {trunk :: [m], padding :: m} deriving (Show, Eq)

instance Applicative Padded where
  pure = ([] :-)
  (fs :- f) <*> (ss :- s) = zapp fs ss :- f s where
    zapp  []        ss        = map f ss
    zapp  fs        []        = map ($ s) fs
    zapp  (f : fs)  (s : ss)  = f s : zapp fs ss

instance Functor Padded where
  fmap = (<*>) . pure
