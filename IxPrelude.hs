{-# LANGUAGE RebindableSyntax #-}

module IxPrelude where

import Control.Monad.Indexed
import Control.Monad.Indexed.State
import Control.Monad.Indexed.Cont
import Data.Functor.Identity
import Prelude hiding (Monad(..))

-- Reenabling conditional syntax
ifThenElse :: Bool -> t -> t -> t
ifThenElse e1 e2 e3 = if e1 then e2 else e3


-- Rebinding the essential Monad operators to enable do-notation even for
-- indexed monads
(>>=) :: IxMonad m => m i j a -> (a -> m j k b) -> m i k b
ixmon >>= k = ibind k ixmon

return :: IxPointed m => a -> m i i a
return = ireturn

(>>) :: IxMonad m => m i j a -> m j k b -> m i k b
ixmon >> ixmon' = ixmon >>= const ixmon'

fail :: IxMonad m => m i j a
fail = fail


-- Reclaiming some useful Control.Monad auxiliary functions, using their
-- analogs in the Control.Monad.Indexed library
modify :: IxMonadState m => (i -> j) -> m i j ()
modify = imodify

gets :: IxMonadState m => (i -> a) -> m i i a
gets = igets

ixcont :: ((a -> o) -> r) -> IxCont r o a
ixcont m = IxCont $ IxContT $ \k -> Identity $ m (runIdentity . k)

liftM :: IxMonad m => (t -> b) -> m i k t -> m i k b
liftM f m = do x <- m
               return (f x)

liftM2 :: IxMonad m => (t -> t1 -> b) -> m i j t -> m j k t1 -> m i k b
liftM2 f m1 m2 = do x1 <- m1
                    x2 <- m2
                    return (f x1 x2)

mplus :: IxMonadPlus m => m i j a -> m i j a -> m i j a
mplus = implus

mzero :: IxMonadZero m => m i j a
mzero = imzero

guard :: IxMonadZero m => Bool -> m i i ()
guard b = if b then return () else imzero
