{-# LANGUAGE Rank2Types #-}
 
module RelDefs where

import Model.Model
import Data.List (nub)
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Indexed
import Control.Monad.IxExtras
import Control.Monad.Indexed.Cont
import Control.Exception (assert)

-- =================
-- ** TYPE SYSTEM ** 
-- =================

type Stack  = [Ent]
data Post   = Post (forall a. [(a,Stack)] -> [(a, Stack)])
              -- Posts are necessarily generic in the type of a;
              -- they care only about the stacks that values are paired with
-- type M      = StateT Stack []
type M a    = WriterT Post (StateT Stack []) a
              -- M a := s -> [((a,h),s)]
type K      = IxCont
              -- K r o a := (a -> o) -> r

type E r     = K r r Ent
type T r     = K r r Bool
type ET r    = K r r (Ent -> Bool)
type EET r   = K r r (Ent -> Ent -> Bool)
type EEET r  = K r r (Ent -> Ent -> Ent -> Bool)
type TTT r   = K r r (Bool -> Bool -> Bool)

instance Show Post where
  show = const "<fun>"
instance Monoid Post where
  mempty = Post id
  (Post m) `mappend` (Post n) = Post (n . m)


-- =======================
-- ** MONAD COMBINATORS **
-- =======================

-- Units and Binds
-- ------------------------------------------------
-- synonyms for the monad operators of StateT and IxCont

unit :: a -> M a
unit = return
-- ignoring type constructors:
-- unit x = \s -> [(x,s)]

(--@) :: M a -> (a -> M b) -> M b
(--@) = (>>=)
-- ignoring type constructors:
-- m --@ f = \s -> concat [f x s' | (x,s') <- m s]
infixl 1 --@

-- 'ixlift' is semantically equivalent to (--@), but adds a type constructor
-- around the continuation 
ixlift :: M a -> K (M b) (M b) a
ixlift m = ixcont $ \k -> m --@ k

iixlift :: K r r (M a) -> K r r (K (M b) (M b) a)
iixlift = liftM ixlift

-- Scope Sequencing Combinator
(--*) :: K r o a -> (a -> K o r' b) -> K r r' b
(--*) = (>>>=)
-- ignoring type constructors:
-- m --* f = \k -> m (\x -> f x k)
infixl 1 --*
-- ------------------------------------------------


-- Scope Shift
-- ------------------------------------------------
-- inject values into trivial (pure) computations

-- First-Order Scope ("Montague lift")
kunit :: a -> K (M r) (M r) a 
kunit = return
-- equivalent to:
-- kunit = lift . unit
--   (where 'lift' is the transformer of the K type: \m k -> m --@ k)
-- ignoring type constructors:
--       = \x k -> k x
  
-- Second-Order Scope ("Internal lift")
kkunit :: K r r a -> K r r (K (M r') (M r') a)
kkunit = liftM kunit
-- equivalent to:
-- kkunit m = kunit kunit ~/~ m
--          = do x <- m
--               kunit $ kunit x
-- ignoring type constructors:
--          = \c -> m (\x -> c (kunit x))
-- ------------------------------------------------


-- Left and Right Continuized Application
-- ------------------------------------------------
-- lift forward and backward function application through the monad(s)

-- First-Order Continuized Application

lap :: K r o a -> K o r' (a -> b) -> K r r' b
lap = ixliftM2 (flip ($))
-- equivalent to:
-- lap = \m h -> do x <- m
--                  f <- h
--                  kunit (f x)
-- ignoring type constructors:
--     = \m h k -> m (\x -> h (\f -> k (f x)))

rap :: K r o (a -> b) -> K o r' a -> K r r' b
rap = ixliftM2 ($)
-- equivalent to:
-- rap = \h m -> do f <- h
--                  x <- m
--                  kunit (f x)
-- ignoring type constructors:
--     = \h m k -> h (\f -> m (\x -> k (f x)))

cap :: K r o (a -> Bool) -> K o r' (a -> Bool) -> K r r' (a -> Bool)
cap = ixliftM2 (liftM2 (&&))

-- Second-Order Continuized Application

llap :: K s t (K r o a) -> K t s' (K o r' (a -> b)) -> K s s' (K r r' b)
llap = ixliftM2 lap
-- equivalent to:
-- llap = \M H -> do m <- M
--                   h <- H
--                   kunit (m `lap` h)
-- ignoring type constructors:
--      = \M H k -> M (\m -> H (\h -> k (m `lap` h)))

rrap :: K s t (K r o (a -> b)) -> K t s' (K o r' a) -> K s s' (K r r' b)
rrap = ixliftM2 rap
-- equivalent to:
-- rrap = \H M -> do h <- H
--                   m <- M
--                   kunit (h `rap` m)
-- ignoring type constructors:
--      = \H M k -> H (\h -> M (\m -> k (h `rap` m)))

ccap :: K s t (K r o (a -> Bool)) -> K t s' (K o r' (a -> Bool)) 
                                  -> K s s' (K r r' (a -> Bool))
ccap = ixliftM2 cap

-- Infix combinators for left and right application

(</>) :: K r o (a -> b) -> K o r' a -> K r r' b
(</>) = rap
infixr 9 </>

(<//>) :: K s t (K r o (a -> b)) -> K t s' (K o r' a) -> K s s' (K r r' b)
(<//>) = rrap
infixr 9 <//>

(<\>) :: K r o a -> K o r' (a -> b) -> K r r' b
(<\>) = lap
infixr 9 <\>

(<\\>) :: K s t (K r o a) -> K t s' (K o r' (a -> b)) -> K s s' (K r r' b)
(<\\>) = llap
infixr 9 <\\>

(<|>) :: K r o (a -> Bool) -> K o r' (a -> Bool) -> K r r' (a -> Bool)
(<|>) = cap
infixr 9 <|>

(<||>) :: K s t (K r o (a -> Bool)) -> K t s' (K o r' (a -> Bool)) 
                                  -> K s s' (K r r' (a -> Bool))
(<||>) = ccap
infixr 9 <||>
-- ------------------------------------------------


-- Program Evaluation
-- ------------------------------------------------
-- execute programmatic meanings with trivial continuations/states

-- First-Order Lower
lower :: K r (M a) a -> r
lower m = runIxCont m unit
-- ignoring type constructors:
-- lower = kunit unit
--       = \m -> m unit

-- Second-Order (Total) Lower
llower :: K t r (K r (M a) a) -> t
llower mm = runIxCont mm lower
-- equivalent to:
-- llower = lower . join
--   (where 'join' is the join of the Cont monad: \M -> M --* id)
--        = \mm -> runIxCont (mm --* id) unit
-- ignoring type constructors:
-- llower = kunit lower
--        = \M -> M (\m -> m unit)

llower1 :: K t r' (K r (M a) a) -> K t r' r
llower1 = ixliftM lower

-- Evaluation in context, filtering with postsups
run :: Stack -> M a -> [(a, Stack)]
run s m =
  let outs = runStateT (runWriterT m) s
      outs' = [(x,st) | ((x,_),st) <- outs]
  in  case outs of
        [] -> []
        (((_, Post h), _) : _) -> h outs'
-- should be:
--   outs >>= \((x,Endo h),s') -> h outs'
-- but because this is a list rather than a set, we'll end up with crazy
-- amounts of duplication, so we fake it by just using the head's h to
-- filter the outputs (this is ok because all outputs will have the same h)

-- First-Order Default Evaluation
eval :: K (M b) (M a) a -> [(b, Stack)]
eval = run [] . lower

-- Second-Order Default Evaluation
eeval :: K (M b) r (K r (M a) a) -> [(b, Stack)]
eeval = run [] . llower
-- ------------------------------------------------


-- Scope Capture
-- ------------------------------------------------
-- force evaluation of quantificational constituents, delimiting their scope
-- filter outputs through accumulated postsups

-- First-Order Reset
res :: K (M r) (M a) a -> K (M r') (M r') r
res m = ixlift . lift $ StateT (\s -> run s $ lower m)
-- equivalent to:
-- res m = ixcont $ \k -> do x <- lower m
--                           k x
-- ignoring type constructors:
--       = \k -> m unit --@ k
--       = \k s -> concat [k x s' | (x,s') <- m unit s]

-- Second-Order Total Reset
rres :: K (M b) r (K r (M a) a) -> K (M u) (M u) (K (M r') (M r') b)
rres m = kkunit . ixlift . lift $ StateT (\s -> run s $ llower m)
-- ignoring type constructors:
-- rres = \M c -> llower M --@ \a -> c (kunit a)
--      = \M c s -> concat [c (kunit m) s' | (m,s') <- llower M s]

-- Second-Order Inner Reset
rres1 :: K t s (K (M r) (M a) a) -> K t s (K (M r') (M r') r)
rres1 = ixliftM res
-- equivalent to:
-- rres1 = \mm -> $ do m <- mm
--                     kunit (res m)
-- ignoring type constructors:
--       = \M c -> M (\m -> c (res m))

-- Second-Order Staged Reset (preserves scopal structure)
-- note that this won't type out for 3-level towers topped by universals;
-- they'll be forced to use the total reset
rres2 :: K (M u) (M (K (M r) (M r) r)) (K (M r) (M a) a) -> K (M r') (M r') u
rres2 = res . rres1
-- equivalent to:
-- rres2 = \mm -> res $ do m <- mm
--                         kunit (res m)
-- ignoring type constructors:
--       = \M -> lift $ M (\m -> unit (res m))
--       = \M c s -> concat [c m s' | (m,s') <- M (unit . res) s]
-- ------------------------------------------------


-- Stack Update
-- ------------------------------------------------
-- extract drefs from continuized individuals and append them to the stack

_up :: M Ent -> M Ent
_up m = do x <- m
           modify (++[x])
           unit x
-- ignoring type constructors:
--    = \s -> [(x, s'++[x]) | (x,s') <- m s]

-- First-Order Push
up :: K r (M o) Ent -> K r (M o) Ent
up m = m --* \x -> ixlift (modify (++[x])) --* \_ -> kunit x
-- equivalent to:
-- up m = do x <- m
--           ixlift (modify (++[x]))
--           kunit x
-- ignoring type constructors:
--   = \k -> m (\x s -> k x (s++[x]))

-- Second-Order Push
uup :: K t s (K r (M o) Ent) -> K t s (K r (M o) Ent)
uup = ixliftM up
-- equivalent to:
-- uup = ((unit up) ~/~)
--     = \mm -> do m <- mm
--                 kunit (up m)
-- ignoring type constructors:
--     = \M k -> M (\m -> k (up m))



-- ==================
-- ** THE LANGUAGE **
-- ==================

-- PREDICATES
-- ===========

-- Transitive Verbs
-- ------------------------------------------------
likes, envies, pities, listensTo, overwhelm :: EET (M r)
[likes, envies, pities, listensTo, overwhelm] =
  map kunit [_likes, _envies, _pities, _listensTo, _overwhelm]
-- ------------------------------------------------

-- Ditransitive Verbs
-- ------------------------------------------------
gave :: EEET (M r)
gave = kunit _gave
-- ------------------------------------------------


-- CONNECTIVES
-- ===========

-- Boolean Operators
-- ------------------------------------------------
conj :: TTT (M r)
conj = kunit (&&)

disj :: IxMonadPlus m => m i j a -> m i j a -> m i j a
disj = implus

_neg :: M Bool -> M Bool
_neg m = lift $ StateT $ \s -> [(not $ any fst $ run s m, s)]
-- this will flush postsups! good, bad?

neg :: K (M r) (M r) (M Bool -> M Bool)
neg = kunit _neg
-- ------------------------------------------------


-- ADJECTIVES
-- ==========

-- Intersective Adjectives
-- ------------------------------------------------
short, tall :: K (M r) (M r) ((Ent -> Bool) -> Ent -> Bool)
[short, tall] = map kunit [_short, _tall]
-- ------------------------------------------------

-- Relational Adjectives
-- ------------------------------------------------
fav :: K (M r) (M r)  ((Ent -> Bool) -> Ent -> Ent)
fav = kunit _fav
-- ------------------------------------------------


-- PREPOSITIONS
-- ============

-- ------------------------------------------------
of_ :: K (M r) (M r) ((Ent -> Bool) -> Ent -> Ent -> Bool)
of_ = kunit _of
-- ------------------------------------------------


-- NOMINALS
-- ========

-- Proper Names
-- ------------------------------------------------
b1, b2, b3, b4, b5, b6 :: E (M r)
[b1, b2, b3, b4, b5, b6] = map kunit boys

g1, g2, g3, g4, g5, g6 :: E (M r)
[g1, g2, g3, g4, g5, g6] = map kunit girls

p1, p2, p3, p4, p5, p6 :: E (M r)
[p1, p2, p3, p4, p5, p6] = map kunit poems
-- ------------------------------------------------

-- Pronouns
-- ------------------------------------------------
-- pronouns are indexed from the back of the stack;
-- out-of-bounds indices throw "Assertion failed" errors :)
_pro :: Int -> M Ent
_pro n = gets $ \s -> assert (length s >= n + 1) $ reverse s !! n

pro :: Int -> E (M r)
pro n = ixlift (_pro n)
-- equivalent to:
-- pro n = lift $ do s <- iget
--                   unit (reverse s !! n)
-- ignoring type constructors:
--       = \k -> \s -> k (reverse s !! n) s

-- convenience pronoun for grabbing the most recent dref
pro0 :: E (M r)
pro0 = pro 0
-- ------------------------------------------------

-- Common Nouns
-- ------------------------------------------------
boy, girl, poem, thing :: ET (M r)
[boy, girl, poem, thing] = map kunit [_boy, _girl, _poem, _thing]

-- Abbreviations
tb,tg,sb,sg :: ET (M r)
tb = tall </> boy
tg = tall </> girl
sb = short </> boy
sg = short </> girl
-- ------------------------------------------------
 
-- Plurals
-- ------------------------------------------------
-- collective conjunction operator
oplus :: Ent -> Ent -> Ent
oplus x@(Atom _) y@(Atom _) = Plur [x,y]
oplus x@(Atom _) (Plur ys)  = Plur (x:ys)
oplus (Plur xs) y@(Atom _)  = Plur (xs++[y])
oplus (Plur xs) (Plur ys)   = Plur (xs++ys)

-- Abbreviations
_p123, _b123 :: Ent
-- p123 abbreviates the collective of poems +p1+p2+p3, b123 the collective of
-- boys +b1+b2+b3
_p123 = foldr1 oplus [_p1,_p2,_p3]
_b123 = foldr1 oplus [_b1,_b2,_b3]

p123, b123 :: E (M r)
[p123, b123] = map kunit [_p123, _b123]
-- ------------------------------------------------


-- DETERMINERS
-- ===========

-- Indefinites
-- ------------------------------------------------
_some :: (Ent -> M Bool) -> M Ent
_some p = do x <- lift . lift $ domAtoms
             p x --@ guard
             unit x

some :: K (M Ent) (M Bool) Ent
some = ixcont _some
-- ignoring type constructors:
--   = \k s -> concat [k x s' | x <- domAtoms, (b,s') <- p x s, b]
-- ------------------------------------------------

-- Definites
-- ------------------------------------------------
_the :: Int -> Post -> (Ent -> M Bool) -> M Ent
_the n h p = tell (h <> unique n) >> _some p

the :: Int -> Post -> K (M Ent) (M Bool) Ent
the n h = ixcont $ _the n h

-- shorthand for default 'the'
the' :: Int -> K (M Ent) (M Bool) Ent
the' n = the n mempty
-- ------------------------------------------------

-- POSTS
unique :: Int -> Post
unique n = Post $ \xs -> assert (1 == nSize xs) xs
  where nSize xs = length $ nub [s!!n | (_,s) <- xs]

tallest :: Int -> Post
tallest n = Post $ \xs -> foldr maxes (take 1 xs) (tail xs)
  where maxes x@(_,sx) ys@((_,sy):_) =
          case compare (sx!!n) (sy!!n) of
            GT -> [x]
            EQ -> x:ys
            LT -> ys



-- Universals
-- ------------------------------------------------
_every :: (Ent -> M Bool) -> E (M Bool)
_every p = ixcont $ \k -> _neg $ _some p --@ _neg . k

every :: K (E (M Bool)) (M Bool) Ent
every = ixcont _every
-- recursive tower!
-- ------------------------------------------------

-- Possessives
-- ------------------------------------------------
-- poss :: E r -> ET r -> K r (E r)
-- poss :: E r -> K (M Bool) o (Ent -> Bool) -> K r r (K (M Ent) o Bool)
poss :: E (M r) -> ET (M Bool) -> K (M r) (M r) (K (M Ent) (M Bool) Bool)
poss g p = kunit some <\\> ((kunit p <\\> kunit of_) <//> kkunit g)
-- ------------------------------------------------


-- RELATIVE CLAUSES
-- ================

_gap :: Int -> M Ent
_gap = _pro

gap :: Int -> E (M r)
gap = pro

_that :: Bool -> Bool -> Bool
_that = (&&)

that :: TTT (M r)
that = conj


{--

"The person who envies boy2 is short"
-- [good, because the only person who envies boy2 is boy1]
eval $ (res $ up (the' 0) <\> envies </> b2) <\> sb

"The person who envies boy3 is short"
-- [failure, because both boy2 and boy1 envy boy3]
eval $ (res $ up (the' 0) <\> envies </> b3) <\> sb

"The tallest person who envies b4 is short"
-- [good, boy3 is the (unique) tallest person who envies boy4, and he's short"
eval $ (res $ up (the 0 $ tallest 0) <\> envies </> b4) <\> sb

"The tallest person who likes b4 is tall"
-- [failure, because both boy4 and girl4 like boy4, and are equally tall]
eval $ (res $ up (the 0 $ tallest 0) <\> likes </> b4) <\> tb

eval $ (res $ up some <\> envies </> res (up some <\> sb)) <\> sb

--}


-- ==============
-- ** EXAMPLES **
-- ==============

{-

Basic Sentences
---------------
"Boy4 is tall"
eval $ up b4 ~\~ tb

"Boy1 is short and Boy5 is tall"
eval $ (up b1 ~\~ sb) ~\~ conj ~/~ up b5 ~\~ tb

"Some boy is tall"
eval $ (res $ up some ~\~ boy) ~\~ tb

"Some tall boy likes some tall girl"
eval $ (res $ up some ~\~ tb) ~\~ likes ~/~ (res $ up some ~\~ tg)


Basic Anaphora
--------------
"Boy 4 likes his poem"
eeval $ (kkunit $ up b4) ~\\~ kunit likes ~//~ (uup $ rres1 $ poss pro0 poem)

"Boy 1 is short and he is tall"
eval $ (res $ up b1 ~\~ sb) ~\~ conj ~/~ (res $ pro0 ~\~ tb)

"Some boy is short and he is tall"
eval $ (res $ (res $ up some ~\~ boy) ~\~ sb) ~\~ conj ~/~ (res $ pro0 ~\~ tb)

"Every boy is short and he is tall" [Binding failure]
eval $ (res $ (lower $ up every ~\~ boy) ~\~ sb) ~\~ conj ~/~ (res $ pro0 ~\~ tb)


Inverse Scope
-------------
"Some tall boy likes every tall girl" [surface scope]
eval $ (res $ up some ~\~ tb) ~\~ likes ~/~ (lower $ up every ~\~ tg)

"Some tall boy likes every tall girl" [inverse scope]
eeval $ (kunit $ res $ up some ~\~ tb) ~\\~ kunit likes ~//~ (kkunit $ lower $ up every ~\~ tg)


Complex DPs
-----------
"Every boy that Girl3 likes is short"
eval $ (lower $ (up every ~\~ boy) ~\~ that ~/~ (res $ up g3 ~\~ likes ~/~ gap 1) ) ~\~ sb

-}
