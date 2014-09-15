{-# LANGUAGE RebindableSyntax #-}

module IxPrelude where

import Control.Monad.Indexed
import Control.Monad.Indexed.State
import Control.Monad.Indexed.Cont
import Data.Functor.Identity
import Prelude hiding (Monad(..))

-- Reenable conditional syntax
ifThenElse :: Bool -> t -> t -> t
ifThenElse e1 e2 e3 = if e1 then e2 else e3


-- Rebind the essential Monad operators to support do-notation for
-- indexed monads
(>>=) :: IxMonad m => m i j a -> (a -> m j k b) -> m i k b
ixmon >>= k = ibind k ixmon

return :: IxPointed m => a -> m i i a
return = ireturn

(>>) :: IxMonad m => m i j a -> m j k b -> m i k b
ixmon >> ixmon' = ixmon >>= const ixmon'

fail :: IxMonad m => m i j a
fail = fail


-- Data constructor for IxCont
ixcont :: ((a -> o) -> r) -> IxCont r o a
ixcont m = IxCont $ IxContT $ \k -> Identity $ m (runIdentity . k)


-- Reclaim some useful Control.Monad auxiliary functions
liftM :: IxMonad m => (t -> b) -> m i k t -> m i k b
liftM f m = do x <- m
               return (f x)

liftM2 :: IxMonad m => (t -> t1 -> b) -> m i j t -> m j k t1 -> m i k b
liftM2 f m1 m2 = do x1 <- m1
                    x2 <- m2
                    return (f x1 x2)

guard :: IxMonadZero m => Bool -> m i i ()
guard b = case b of True -> return (); _ -> imzero
