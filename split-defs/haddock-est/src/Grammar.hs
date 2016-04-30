module Grammar where

import Control.Monad.State
import Control.Monad.Indexed
import IxCont

type Ent = String
type Stack = [Ent]

type D = StateT Stack []
type F a = D a -> D a
type K = IxCont

type E r     = K r r Ent
type T r     = K r r Bool
type ET r    = K r r (Ent -> Bool)
type EET r   = K r r (Ent -> Ent -> Bool)
type EEET r  = K r r (Ent -> Ent -> Ent -> Bool)
type TTT r   = K r r (Bool -> Bool -> Bool)

-- ------------------------------------------------

lower :: K r (D a) a -> r
lower m = runIxCont m return

llower :: K t r (K r (D a) a) -> t
llower mm = runIxCont mm lower

llower1 :: K t r' (K r (D a) a) -> K t r' r
llower1 = iliftM lower

eval :: K (D b) (D a) a -> [(b, Stack)]
eval = flip runStateT [] . lower 

eeval :: K (D b) r (K r (D a) a) -> [(b, Stack)]
eeval = flip runStateT [] . llower

_push :: D Ent -> D Ent
_push m = m >>= \x -> state (\s -> (x,s++[x]))

push :: K r (D o) Ent -> K r (D o) Ent
push m = m >>>= \x -> ixlift (modify (++[x])) >>>= \_ -> return x

ppush :: K t s (K r (D o) Ent) -> K t s (K r (D o) Ent)
ppush = iliftM push

