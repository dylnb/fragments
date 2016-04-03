{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}

-------------------------------------------------------------------------------------------
-- https://hackage.haskell.org/package/indexed-extras-0.1.1
-------------------------------------------------------------------------------------------
module IxCont where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Indexed
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Indexed.Trans

newtype IxContT m r o a = IxContT { runIxContT :: (a -> m o) -> m r }

ilower :: Monad m => IxContT m r a a -> m r 
ilower m = runIxContT m return

instance IxFunctor (IxContT m) where
  imap f m = IxContT $ \c -> runIxContT m (c . f)

instance IxPointed (IxContT m) where
  ireturn a = IxContT ($a)

instance Monad m => IxApplicative (IxContT m) where
  iap = iapIxMonad

instance Monad m => IxMonad (IxContT m) where
  ibind f c = IxContT $ \k -> runIxContT c $ \a -> runIxContT (f a) k

instance Monad m => Functor (IxContT m i j) where
  fmap = imap

instance Monad m => Applicative (IxContT m i i) where
  pure = ireturn
  (<*>) = iap

instance Monad m => Monad (IxContT m i i) where
  return = ireturn
  m >>= k = ibind k m

instance IxMonadTrans IxContT where
  ilift m = IxContT (m >>=)

instance MonadReader e m => MonadReader e (IxContT m i i) where
  ask = ilift ask
  local f m = IxContT $ \c -> do
    r <- ask
    local f (runIxContT m (local (const r) . c))

instance MonadState e m => MonadState e (IxContT m i i) where
  get = ilift get
  put = ilift . put

instance MonadIO m => MonadIO (IxContT m i i) where
  liftIO = ilift . liftIO 

type IxCont = IxContT Identity

runIxCont :: IxCont r o a -> (a -> o) -> r 
runIxCont m k = runIdentity $ runIxContT m (return . k)

ixcont :: ((a -> o) -> r) -> IxCont r o a
ixcont m = IxContT $ \k -> Identity $ m (runIdentity . k)

ixlift :: Monad m => m a -> IxCont (m b) (m b) a
ixlift m = ixcont $ \k -> m >>= k

iixlift :: Monad m => IxCont r r (m a) -> IxCont r r (IxCont (m b) (m b) a)
iixlift = liftM ixlift

iliftM :: IxMonad m => (t -> b) -> m i k t -> m i k b
iliftM f m = ireturn f `iap` m

iliftM2 :: IxMonad m => (t -> t1 -> b) -> m i j t -> m j k t1 -> m i k b
iliftM2 f m1 m2 = ireturn f `iap` m1 `iap` m2

iguard :: IxMonadZero m => Bool -> m i i ()
iguard b = if b then ireturn () else imzero

lap :: IxCont r o a -> IxCont o r' (a -> b) -> IxCont r r' b
lap = iliftM2 (flip ($))

rap :: IxCont r o (a -> b) -> IxCont o r' a -> IxCont r r' b
rap = iliftM2 ($)

cap :: IxCont r o (a -> Bool) -> IxCont o r' (a -> Bool) -> IxCont r r' (a -> Bool)
cap = iliftM2 (liftM2 (&&))

llap :: IxCont s t (IxCont r o a) -> IxCont t s' (IxCont o r' (a -> b)) -> IxCont s s' (IxCont r r' b)
llap = iliftM2 lap

rrap :: IxCont s t (IxCont r o (a -> b)) -> IxCont t s' (IxCont o r' a) -> IxCont s s' (IxCont r r' b)
rrap = iliftM2 rap

ccap :: IxCont s t (IxCont r o (a -> Bool)) -> IxCont t s' (IxCont o r' (a -> Bool)) 
                                  -> IxCont s s' (IxCont r r' (a -> Bool))
ccap = iliftM2 cap

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
