module Control.Monad.IxExtras where

import Control.Monad
import Control.Monad.Indexed
import Control.Monad.Indexed.Cont
import Data.Functor.Identity
import Prelude hiding (Monad(..))


-- Data constructor for IxCont
ixcont :: ((a -> o) -> r) -> IxCont r o a
ixcont m = IxCont $ IxContT $ \k -> Identity $ m (runIdentity . k)


ixlift :: Monad m => m a -> IxCont (m b) (m b) a
ixlift m = ixcont $ \k -> m >>= k

iixlift :: Monad m => IxCont r r (m a) -> IxCont r r (IxCont (m b) (m b) a)
iixlift = liftM ixlift

-- Rebuild some useful Control.Monad auxiliary functions
ixliftM :: IxMonad m => (t -> b) -> m i k t -> m i k b
ixliftM f m = ireturn f `iap` m

ixliftM2 :: IxMonad m => (t -> t1 -> b) -> m i j t -> m j k t1 -> m i k b
ixliftM2 f m1 m2 = ireturn f `iap` m1 `iap` m2

iguard :: IxMonadZero m => Bool -> m i i ()
iguard b = if b then ireturn () else imzero

lap :: IxCont r o a -> IxCont o r' (a -> b) -> IxCont r r' b
lap = ixliftM2 (flip ($))

rap :: IxCont r o (a -> b) -> IxCont o r' a -> IxCont r r' b
rap = ixliftM2 ($)

cap :: IxCont r o (a -> Bool) -> IxCont o r' (a -> Bool) -> IxCont r r' (a -> Bool)
cap = ixliftM2 (liftM2 (&&))

llap :: IxCont s t (IxCont r o a) -> IxCont t s' (IxCont o r' (a -> b)) -> IxCont s s' (IxCont r r' b)
llap = ixliftM2 lap

rrap :: IxCont s t (IxCont r o (a -> b)) -> IxCont t s' (IxCont o r' a) -> IxCont s s' (IxCont r r' b)
rrap = ixliftM2 rap

ccap :: IxCont s t (IxCont r o (a -> Bool)) -> IxCont t s' (IxCont o r' (a -> Bool)) 
                                  -> IxCont s s' (IxCont r r' (a -> Bool))
ccap = ixliftM2 cap

(</>) :: IxCont r o (a -> b) -> IxCont o r' a -> IxCont r r' b
(</>) = rap
infixr 9 </>

(<//>) :: IxCont s t (IxCont r o (a -> b)) -> IxCont t s' (IxCont o r' a) -> IxCont s s' (IxCont r r' b)
(<//>) = rrap
infixr 9 <//>

(<\>) :: IxCont r o a -> IxCont o r' (a -> b) -> IxCont r r' b
(<\>) = lap
infixr 9 <\>

(<\\>) :: IxCont s t (IxCont r o a) -> IxCont t s' (IxCont o r' (a -> b)) -> IxCont s s' (IxCont r r' b)
(<\\>) = llap
infixr 9 <\\>

(<|>) :: IxCont r o (a -> Bool) -> IxCont o r' (a -> Bool) -> IxCont r r' (a -> Bool)
(<|>) = cap
infixr 9 <|>

(<||>) :: IxCont s t (IxCont r o (a -> Bool)) -> IxCont t s' (IxCont o r' (a -> Bool)) 
                                  -> IxCont s s' (IxCont r r' (a -> Bool))
(<||>) = ccap
infixr 9 <||>
