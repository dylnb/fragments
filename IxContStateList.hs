{-# LANGUAGE RebindableSyntax #-}

import IxPrelude
import Model
import Control.Monad.Indexed
import Control.Monad.Indexed.State
import Control.Monad.Indexed.Cont
import Control.Monad.Indexed.Trans
import Control.Exception (assert)
import Prelude hiding (Monad(..))

-- =================
-- ** TYPE SYSTEM ** 
-- =================

type Stack   = [Ent]
type D       = IxStateT [] Stack Stack -- D a := s -> [(a,s)]
type K       = IxCont -- K r o a := (a -> o) -> r

type E r     = K r r Ent
type T r     = K r r Bool
type ET r    = K r r (Ent -> Bool)
type EET r   = K r r (Ent -> Ent -> Bool)
type EEET r  = K r r (Ent -> Ent -> Ent -> Bool)
type TTT r   = K r r (Bool -> Bool -> Bool)


-- =======================
-- ** MONAD COMBINATORS **
-- =======================

-- Units and Binds
-- ------------------------------------------------
-- synonyms for the monad operators of IxStateT and Cont, to distinguish them
-- for clarity and ape the notation in Charlow 2014

unit :: a -> D a
unit = return
-- ignoring type constructors:
-- unit x = \s -> [(x,s)]

(--@) :: D a -> (a -> D b) -> D b
(--@) = (>>=)
-- ignoring type constructors:
-- m --@ f = \s -> concat [f x s' | (x,s') <- m s]
infixl 1 --@

-- 'lift' is semantically equivalent to (--@), but with type constructors that
-- enable lots of monadic sugar, including do-notation
lift :: D a -> K (D b) (D b) a
lift m = ixcont $ \k -> m --@ k

-- Scope Sequencing Combinator
(--*) :: K r o a -> (a -> K o r' b) -> K r r' b
(--*) = (>>=)
-- ignoring type constructors:
-- m --* f = \k -> m (\x -> f x k)
infixl 1 --*
-- ------------------------------------------------


-- Scope Shift
-- ------------------------------------------------
-- inject values into trivial (pure) computations

-- First-Order Scope ("Montague lift")
pure :: a -> K r r a 
pure = return
-- equivalent to:
-- pure = lift . unit
--   (where 'lift' is the transformer of the K type: \m k -> m --@ k)
-- ignoring type constructors:
--      = \x k -> k x
  
-- Second-Order Scope ("Internal lift")
ppure :: K r r a -> K r r (K r' r' a)
ppure = liftM pure
-- equivalent to:
-- ppure m = pure pure ~/~ m
--         = do x <- m
--              pure $ pure x
-- ignoring type constructors:
--         = \c -> m (\x -> c (pure x))
-- ------------------------------------------------


-- Left and Right Continuized Application
-- ------------------------------------------------
-- lift forward and backward function application through the monad(s)

-- First-Order Continuized Application

lap :: K r o a -> K o r' (a -> b) -> K r r' b
lap = liftM2 (flip ($))
-- equivalent to:
-- lap = \m h -> do x <- m
--                  f <- h
--                  pure (f x)
-- ignoring type constructors:
--     = \m h k -> m (\x -> h (\f -> k (f x)))

rap :: K r o (a -> b) -> K o r' a -> K r r' b
rap = liftM2 ($)
-- equivalent to:
-- rap = \h m -> do f <- h
--                  x <- m
--                  pure (f x)
-- ignoring type constructors:
--     = \h m k -> h (\f -> m (\x -> k (f x)))


-- Second-Order Continuized Application

llap :: K s t (K r o a) -> K t s' (K o r' (a -> b)) -> K s s' (K r r' b)
llap = liftM2 lap
-- equivalent to:
-- llap = \M H -> do m <- M
--                   h <- H
--                   pure (m `lap` h)
-- ignoring type constructors:
--      = \M H k -> M (\m -> H (\h -> k (m `lap` h)))

rrap :: K s t (K r o (a -> b)) -> K t s' (K o r' a) -> K s s' (K r r' b)
rrap = liftM2 rap
-- equivalent to:
-- rrap = \H M -> do h <- H
--                   m <- M
--                   pure (h `rap` m)
-- ignoring type constructors:
--      = \H M k -> H (\h -> M (\m -> k (h `rap` m)))


-- Infix combinators for left and right application

(~/~) :: K r o (a -> b) -> K o r' a -> K r r' b
(~/~) = rap
infixr 9 ~/~

(~//~) :: K s t (K r o (a -> b)) -> K t s' (K o r' a) -> K s s' (K r r' b)
(~//~) = rrap
infixr 9 ~//~

(~\~) :: K r o a -> K o r' (a -> b) -> K r r' b
(~\~) = lap
infixr 9 ~\~

(~\\~) :: K s t (K r o a) -> K t s' (K o r' (a -> b)) -> K s s' (K r r' b)
(~\\~) = llap
infixr 9 ~\\~
-- ------------------------------------------------


-- Program Evaluation
-- ------------------------------------------------
-- execute programmatic meanings with trivial continuations/states

-- First-Order Lower
lower :: K r (D a) a -> r
lower m = runIxCont m unit
-- ignoring type constructors:
-- lower = pure unit
--       = \m -> m unit

-- Second-Order (Total) Lower
llower :: K t r (K r (D a) a) -> t
llower mm = runIxCont mm lower
-- equivalent to:
-- llower = lower . join
--   (where 'join' is the join of the ContT monad: \M -> M --* id)
--        = \mm -> flip runIxContT unit $ do m <- mm; m
-- ignoring type constructors:
-- llower = pure lower
--        = \M -> M (\m -> m unit)

-- Evaluation in Default Context
run :: Stack -> D a -> [(a, Stack)]
run = flip runIxStateT

-- First-Order Default Evaluation
eval :: K (D b) (D a) a -> [(b, Stack)]
eval = run [] . lower

-- Second-Order Default Evaluation
eeval :: K (D b) r (K r (D a) a) -> [(b, Stack)]
eeval = run [] . llower
-- ------------------------------------------------


-- Scope Capture
-- ------------------------------------------------
-- force evaluation of quantificational constituents, delimiting their scope

-- First-Order Reset
res :: K (D r) (D a) a -> K (D r') (D r') r
res = lift . lower
-- equivalent to:
-- res m = ixcont $ \k -> do x <- lower m
--                           k x
-- ignoring type constructors:
--       = \k -> m unit --@ k
--       = \k s -> concat [k x s' | (x,s') <- m unit s]

-- Second-Order Total Reset
rres :: K (D b) r (K r (D a) a) -> K (D u) (D u) (K r' r' b)
rres = ppure . lift . llower
-- ignoring type constructors:
-- rres = \M c -> llower M --@ \a -> c (pure a)
--      = \M c s -> concat [c (pure m) s' | (m,s') <- llower M s]

-- Second-Order Inner Reset
rres1 :: K t s (K (D r) (D a) a) -> K t s (K (D r') (D r') r)
rres1 = liftM res
-- equivalent to:
-- rres1 = \mm -> $ do m <- mm
--                     pure (res m)
-- ignoring type constructors:
--       = \M c -> M (\m -> c (res m))

-- Second-Order Staged Reset (preserves scopal structure)
-- note that this won't type out for 3-level towers topped by universals;
-- they'll be forced to use the total reset
rres2 :: K (D u) (D (K (D r) (D r) r)) (K (D r) (D a) a) -> K (D r') (D r') u
rres2 = res . rres1
-- equivalent to:
-- rres2 = \mm -> res $ do m <- mm
--                         pure (res m)
-- ignoring type constructors:
--       = \M -> lift $ M (\m -> unit (res m))
--       = \M c s -> concat [c m s' | (m,s') <- M (unit . res) s]
-- ------------------------------------------------


-- Stack Update
-- ------------------------------------------------
-- extract drefs from continuized individuals and append them to the stack

_up :: D Ent -> D Ent
_up m = do x <- m
           imodify (++[x])
           unit x
-- ignoring type constructors:
--    = \s -> [(x, s'++[x]) | (x,s') <- m s]

-- First-Order Push
up :: K r (D o) Ent -> K r (D o) Ent
up m = do x <- m
          lift (imodify (++[x]))
          pure x
-- ignoring type constructors:
--   = \k -> m (\x s -> k x (s++[x]))

-- Second-Order Push
uup :: K t s (K r (D o) Ent) -> K t s (K r (D o) Ent)
uup = liftM up
-- equivalent to:
-- uup = ((unit up) ~/~)
--     = \mm -> do m <- mm
--                 pure (up m)
-- ignoring type constructors:
--     = \M k -> M (\m -> k (up m))



-- ==================
-- ** THE LANGUAGE **
-- ==================

-- PREDICATES
-- ===========

-- Transitive Verbs
-- ------------------------------------------------
likes, envies, pities, listensTo, overwhelm :: EET r
[likes, envies, pities, listensTo, overwhelm] =
  map pure [_likes, _envies, _pities, _listensTo, _overwhelm]
-- ------------------------------------------------

-- Ditransitive Verbs
-- ------------------------------------------------
gave :: EEET r
gave = pure _gave
-- ------------------------------------------------


-- CONNECTIVES
-- ===========

-- Boolean Operators
-- ------------------------------------------------
conj :: TTT r
conj = pure (&&)

disj :: IxMonadPlus m => m i j a -> m i j a -> m i j a
disj = implus

_neg :: D Bool -> D Bool
_neg m = IxStateT $ \s -> [(not $ any fst $ run s m, s)]

neg :: K r r (D Bool -> D Bool)
neg = pure _neg
-- ------------------------------------------------


-- ADJECTIVES
-- ==========

-- Intersective Adjectives
-- ------------------------------------------------
short, tall :: K r r ((Ent -> Bool) -> Ent -> Bool)
[short, tall] = map pure [_short, _tall]
-- ------------------------------------------------

-- Relational Adjectives
-- ------------------------------------------------
fav :: K r r ((Ent -> Bool) -> Ent -> Ent)
fav = pure _fav
-- ------------------------------------------------

-- Abbreviations
tb,tg,sb,sg :: ET r
tb = tall ~/~ boy
tg = tall ~/~ girl
sb = short ~/~ boy
sg = short ~/~ girl
-- ------------------------------------------------


-- PREPOSITIONS
-- ============

-- ------------------------------------------------
of_ :: K r r ((Ent -> Bool) -> Ent -> Ent -> Bool)
of_ = pure _of
-- ------------------------------------------------


-- NOMINALS
-- ========

-- Proper Names
-- ------------------------------------------------
b1, b2, b3, b4, b5, b6 :: E r
[b1, b2, b3, b4, b5, b6] = map pure boys

g1, g2, g3, g4, g5, g6 :: E r
[g1, g2, g3, g4, g5, g6] = map pure girls

p1, p2, p3, p4, p5, p6 :: E r
[p1, p2, p3, p4, p5, p6] = map pure poems
-- ------------------------------------------------

-- Pronouns
-- ------------------------------------------------
-- pronouns are indexed from the back of the stack;
-- out-of-bounds indices throw "Assertion failed" errors :)
_pro :: Int -> D Ent
_pro n = igets $ \s -> assert (length s >= n + 1) $ reverse s !! n

pro :: Int -> E (D r)
pro n = lift (_pro n)
-- equivalent to:
-- pro n = lift $ do s <- iget
--                   unit (reverse s !! n)
-- ignoring type constructors:
--       = \k -> \s -> k (reverse s !! n) s

-- convenience pronoun for grabbing the most recent dref
pro0 :: E (D r)
pro0 = pro 0
-- ------------------------------------------------

-- Common Nouns
-- ------------------------------------------------
boy, girl, poem, thing :: ET r
[boy, girl, poem, thing] = map pure [_boy, _girl, _poem, _thing]
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
p123, b123 :: Ent
-- p123 abbreviates the collective of poems +p1+p2+p3, b123 the collective of
-- boys +b1+b2+b3
p123 = foldr1 oplus [_p1,_p2,_p3]
b123 = foldr1 oplus [_b1,_b2,_b3]
-- ------------------------------------------------


-- DETERMINERS
-- ===========

-- Indefinites
-- ------------------------------------------------
_some :: (Ent -> D Bool) -> D Ent
_some p = do x <- ilift domAtoms
             p x --@ guard
             unit x

some :: K (D Ent) (D Bool) Ent
some = ixcont _some
-- ignoring type constructors:
--   = \k s -> concat [k x s' | x <- domAtoms, (b,s') <- p x s, b]
-- ------------------------------------------------

-- Universals
-- ------------------------------------------------
_every :: (Ent -> D Bool) -> E (D Bool)
_every p = ixcont $ \k -> _neg $ _some p --@ _neg . k

every :: K (E (D Bool)) (D Bool) Ent
every = ixcont _every
-- ------------------------------------------------

-- Possessives
-- ------------------------------------------------
-- poss :: E r -> ET r -> K r (E r)
-- poss :: E r -> K (D Bool) o (Ent -> Bool) -> K r r (K (D Ent) o Bool)
poss :: E r -> ET (D Bool) -> K r r (K (D Ent) (D Bool) Bool)
poss g p = pure some ~\\~ ((pure p ~\\~ pure of_) ~//~ ppure g)
-- ------------------------------------------------


-- RELATIVE CLAUSES
-- ================

_gap :: Int -> D Ent
_gap = _pro

gap :: Int -> E (D r)
gap = pro

_that :: Bool -> Bool -> Bool
_that = (&&)

that :: TTT r
that = conj



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
eeval $ (ppure $ up b4) ~\\~ pure likes ~//~ (uup $ liftM res $ poss (pro 0) poem)

"Boy 1 is short and he is tall"
eval $ (res $ up b1 ~\~ sb) ~\~ conj ~/~ (res $ pro 0 ~\~ tb)

"Some boy is short and he is tall"
eval $ (res $ (res $ up some ~\~ boy) ~\~ sb) ~\~ conj ~/~ (res $ pro 0 ~\~ tb)

"Every boy is short and he is tall" [Binding failure]
eval $ (res $ (lower $ up every ~\~ boy) ~\~ sb) ~\~ conj ~/~ (res $ pro 0 ~\~ tb)


Inverse Scope
-------------
"Some tall boy likes every tall girl" [surface scope]
eval $ (res $ up some ~\~ tb) ~\~ likes ~/~ (lower $ up every ~\~ tg)

"Some tall boy likes every tall girl" [inverse scope]
eeval $ (pure $ res $ up some ~\~ tb) ~\\~ pure likes ~//~ (ppure $ lower $ up every ~\~ tg)


Complex DPs
-----------
"Every boy that Girl3 likes is short"
eval $ (lower $ (up every ~\~ boy) ~\~ that ~/~ (res $ up g3 ~\~ likes ~/~ gap 1) ) ~\~ sb

-}
