module Rels where

import qualified Prelude as P
import BasicPrelude hiding (lift, (</>))
import Data.List (nub)
import Control.Monad.State
import Control.Monad.Indexed
import Control.Monad.IxExtras
import Control.Monad.Indexed.Cont
import Control.Exception (assert)

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
llower1 = ixliftM lower

eval :: K (D b) (D a) a -> [(b, Stack)]
eval = flip runStateT [] . lower 

eeval :: K (D b) r (K r (D a) a) -> [(b, Stack)]
eeval = flip runStateT [] . llower

_push :: D Ent -> D Ent
_push m = m >>= \x -> state (\s -> (x,s++[x]))

push :: K r (D o) Ent -> K r (D o) Ent
push m = m >>>= \x -> ixlift (modify (++[x])) >>>= \_ -> return x

ppush :: K t s (K r (D o) Ent) -> K t s (K r (D o) Ent)
ppush = ixliftM push

-- ------------------------------------------------

domain :: [Ent]
domain = ["J", "M", "B", "S"]

-- ------------------------------------------------

john, mary :: E (D r)
john = return "J"
mary = return "M"

boy, girl :: ET (D r)
boy = return (\x -> x `elem` ["J", "B", "F"])
girl = return (\x -> x `elem` ["M"])

likes, is :: EET (D r)
likes = return (\x y -> (y,x) `elem` [("J","B"), ("J","M"), ("B","M")])
is = return (==)

_some :: (Ent -> D Bool) -> D Ent
_some p = do x <- lift domain
             p x >>= guard
             return x

some :: K (D Ent) (D Bool) Ent
some = ixcont _some

the :: Int -> F r -> K (D r) (D r) (K (D Ent) (D Bool) Ent)
the n t = ixcont $ \c -> unique n . t $ c (push some)

the' :: Int -> K (D r) (D r) (K (D Ent) (D Bool) Ent)
the' n = the n id

_every :: (Ent -> D Bool) -> E (D Bool)
_every p = ixcont $ \k -> _neg $ _some p >>= _neg . k

every :: K (E (D Bool)) (D Bool) Ent
every = ixcont _every


unique :: Int -> F a
unique n m = StateT $ \s ->
  let xs = runStateT m s
  in  assert (1 == length (nub [s!!n | (_,s) <- xs])) xs

-- biggest :: Int -> DFoc Bool -> StateT Env [] Bool
-- -- find those outputs of the focus that are among the "biggest" outputs of
-- -- any of the alternatives (might be empty)
-- biggest n m =
--   StateT $ \g -> intersectBy (equating testRef) (pt_outs g) (sup $ alt_outs g)
--     where -- project out the nth component of some output's state
--           testRef = (!!n) . snd
--           -- keep only those outputs with the largest testRefs
--           sup = last . groupBy (equating testRef) . sortBy (comparing testRef)
--           -- grab the alternatives at some input state
--           alt_outs = filter fst . concat . alts . runListT . runStateT m
--           -- grab the focus at some input state
--           pt_outs = filter fst . pt . runListT . runStateT m


tallest :: Int -> F a
tallest n m = StateT $ \s -> 
  let xs = runStateT m s
      testRef = (!!n) . snd
  in  last . groupBy (equating testRef) . sortBy (comparing testRef) $ xs
  -- in  foldr maxes (take 1 xs) (tail xs)
  --       where maxes x@(_,sx) ys@((_,sy):_) =
  --               case compare (sx!!n) (sy!!n) of
  --                 GT -> [x]
  --                 EQ -> x:ys
  --                 LT -> ys

conj :: TTT (D r)
conj = return (&&)

disj :: IxMonadPlus m => m i j a -> m i j a -> m i j a
disj = implus

_neg :: D Bool -> D Bool
_neg m = StateT $ \s -> [(not $ any fst $ runStateT m s, s)]

neg :: K (D r) (D r) (D Bool -> D Bool)
neg = return _neg


{-

eval $ (push $ ixlift . lower $ some <\> boy) <\> boy

eval $ (ixlift . llower $ the' 0 <\\> return boy) <\> boy

eval $ (ixlift . llower $ the' 0 <\\> return girl) <\> girl

eval $ push john <\> likes </> (ixlift . llower $ the' 1 <\\> return boy)

eval $ push john <\> likes </> (ixlift . llower $ the' 0 <\\> return boy)

eval $ push john <\> (ixlift . llower $ return likes <//> (iixlift . llower1 $ the' 1 <\\> return boy))

eval $ push john <\> (ixlift . llower $ return likes <//> (iixlift . llower1 $ the' 0 <\\> return boy))

eval $ ppush (return john) <\\> is <//> (return ixlift </> llower1 (the 1 (tallest 1) <\\> return boy))

-}

-- who :: D Bool -> D a -> D a
-- who rc dp = dp >> rc >>= guard
