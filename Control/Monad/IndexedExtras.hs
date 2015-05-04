module Control.Monad.IndexedExtras where

import Control.Monad.Indexed
import Control.Monad.Indexed.Cont
import Data.Functor.Identity
import Prelude hiding (Monad(..))


-- Data constructor for IxCont
ixcont :: ((a -> o) -> r) -> IxCont r o a
ixcont m = IxCont $ IxContT $ \k -> Identity $ m (runIdentity . k)


-- Rebuild some useful Control.Monad auxiliary functions
ixliftM :: IxMonad m => (t -> b) -> m i k t -> m i k b
ixliftM f m = ireturn f `iap` m

ixliftM2 :: IxMonad m => (t -> t1 -> b) -> m i j t -> m j k t1 -> m i k b
ixliftM2 f m1 m2 = ireturn f `iap` m1 `iap` m2

iguard :: IxMonadZero m => Bool -> m i i ()
iguard b = if b then ireturn () else imzero
