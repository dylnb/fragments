{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE FunctionalDependencies #-}
-- {-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE FlexibleContexts #-}

module Grammar where

import Control.Monad.State

type E = String
type T = Bool
type Stack = [E]

type D = StateT Stack []
type F a = D a -> D a
data K r o a = Tower {runTower :: (a -> o) -> r}

-- ------------------------------------------------
-- Modes of combination
-- ------------------------------------------------

-- Recursive forward application ------------------

type family f :/: g where
  (a -> b) :/: a = b
  (K c d f) :/: (K d e x) = K c e (f :/: x)

infixr 9 ~/~
class AppR f g where
  (~/~) :: f -> g -> f :/: g
instance AppR (a -> b) a where
  f ~/~ x = f x
instance (d ~ d', AppR in1 in2) => AppR (K c d in1) (K d' e in2) where
  mf ~/~ mx = Tower $ \k -> runTower mf (\f -> runTower mx (\x -> k (f ~/~ x)))

-- Recursive backward application -----------------

type family f :\: g where
  a :\: (a -> b) = b
  (K c d x) :\: (K d e f) = K c e (x :\: f)

infixr 9 ~\~
class AppL f g where
  (~\~) :: f -> g -> f :\: g
instance AppL a (a -> b) where
  x ~\~ f = f x
instance (d ~ d', AppL in1 in2) => AppL (K c d in1) (K d' e in2) where
  mx ~\~ mf = Tower $ \k -> runTower mx (\x -> runTower mf (\f -> k (x ~\~ f)))

-- Recursive predicate modification ----------------

type family f :|: g where
  (a -> T) :|: (a -> T) = a -> T
  (K c d f) :|: (K d e g) = K c e (f :|: g)

infixr 9 ~|~
class AppC f g where
  (~|~) :: f -> g -> f :|: g
instance AppC (a -> T) (a -> T) where
  f ~|~ g = \x -> f x && g x
instance (d ~ d', AppC in1 in2) => AppC (K c d in1) (K d' e in2) where
  mf ~|~ mg = Tower $ \k -> runTower mf (\f -> runTower mg (\g -> k (f ~|~ g)))

-- Special cases of above (for the type checker) --

mf </> mx = Tower $ \k -> runTower mf (\f -> runTower mx (\x -> k (f x)))
mf <//> mx = Tower $ \k -> runTower mf (\f -> runTower mx (\x -> k (f </> x)))
mx <\> mf = Tower $ \k -> runTower mx (\x -> runTower mf (\f -> k (f x)))
mx <\\> mf = Tower $ \k -> runTower mx (\x -> runTower mf (\f -> k (x <\> f)))
mf <|> mg = Tower $ \k -> runTower mf (\f -> runTower mg (\g -> k (\x -> f x && g x)))
mf <||> mg = Tower $ \k -> runTower mf (\f -> runTower mg (\g -> k (f <|> g)))

-- Recursive evaluation ---------------------------

class Low r o a where
  lowr :: K r o a -> r
instance Low r (D a) a where
  lowr t = runTower t return
instance (Low r' o' a, o ~ r') => Low r o (K r' o' a) where
  lowr t = runTower t lowr

-- Convenience functions --------------------------

u :: a -> K (D r) (D r) a
u x = Tower (return x >>=)

uu :: a -> K (D r') (D r') (K (D r) (D r) a)
uu = u . u

ilowr :: Low r o a => K (D r') o' (K r o a) -> K (D r') o' r
ilowr = (u lowr </>)

reset :: (r ~ D b, Low r o a) => K r o a -> K (D r') (D r') b
reset t = Tower (lowr t >>=)

-- ------------------------------------------------

-- class LowersTo m ret | m -> ret where
--   low :: m -> ret
-- instance {-# OVERLAPPING #-} LowersTo (K ret (D a) a) ret where
--   low m = runTower m return
-- instance {-# OVERLAPPABLE #-} LowersTo a o => LowersTo (K r o a) r where
--   low m = runTower m low

-- reset :: LowersTo m (D a) => m -> K (D r) (D r) a
-- reset t = Tower (low t >>=)

-- ilower :: K (D r) o (K a1 (D a) a) -> K (D r) o a1
-- ilower = (unit lower </>)

-- ilow :: LowersTo t a => K (D r) o t -> K (D r) o a
-- ilow = (unit low </>)

-- lower :: K r (D a) a -> r
-- lower m = runTower m return

-- llower :: K r o (K o (D a) a) -> r
-- llower m = runTower m lower
