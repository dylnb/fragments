module ExcScopeW where

-- A port of the monadic denotational semantics for a fragment of English, as
-- presented in Charlow 2014: "On the semantics of exceptional scope",
-- extended with intensional meanings

import Model.ModelW
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.List
import Control.Monad.Indexed
import Control.Monad.IxExtras
import Control.Monad.Indexed.Cont
import Control.Exception (assert)

-- =================
-- ** TYPE SYSTEM ** 
-- =================

type Stack   = [Ent]
type D       = StateT Stack (ListT ((->) World))
               -- DW a := s w -> [(a,s)]
type K r o a = IxCont r o a  
               -- K r o a := (a -> o) -> r

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
-- synonyms for the monad operators of StateT and IxCont, to distinguish them
-- for clarity and ape the notation in Charlow 2014

unit :: a -> D a
unit = return
-- ignoring type constructors:
-- unit x = \s _ -> [(x,s)]

(--@) :: D a -> (a -> D b) -> D b
(--@) = (>>=)
-- ignoring type constructors:
-- m --@ f = \s w -> concat [f x s' w | (x,s') <- m s w]
infixl 1 --@

-- 'ixlift' is semantically equivalent to (--@), but adds a type constructor
-- around the continuation
ixlift :: D a -> K (D b) (D b) a
ixlift m = ixcont $ \k -> m --@ k
-- ignoring type constructors:
-- ixlift m = \k s w -> concat [k x s' w | (x,s') <- m s w]

iixlift :: K r r (D a) -> K r r (K (D b) (D b) a)
iixlift = liftM ixlift

wlift :: (World -> a) -> K (D r) (D r) a
wlift = ixlift . lift . lift
-- ignoring type constructors:
-- wlift phi = \k s w -> k (phi w) s w

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
kunit :: a -> K (D r) (D r) a 
kunit = return
-- equivalent to:
-- kunit = lift . unit
--   (where 'lift' is the transformer of the K type: \m k -> m --@ k)
-- ignoring type constructors:
--       = \x k -> k x
  
-- Second-Order Scope ("Internal lift")
kkunit :: K r r a -> K r r (K (D r') (D r') a)
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
-- lower = kunit unit
--       = \m -> m unit

-- Second-Order (Total) Lower
llower :: K t r (K r (D a) a) -> t
llower mm = runIxCont mm lower
-- equivalent to:
-- llower = lower . join
--   (where 'join' is the join of the Cont monad: \M -> M --* id)
--        = \mm -> flip runIxCont unit $ do m <- mm; m
-- ignoring type constructors:
-- llower = kunit lower
--        = \M -> M (\m -> m unit)

llower1 :: K t r' (K r (D a) a) -> K t r' r
llower1 = ixliftM lower

-- Evaluation in Default Context
run :: Stack -> World -> D a -> [(a, Stack)]
run s w m = (runListT $ runStateT m s) w

-- First-Order Default Evaluation
eval :: K (D b) (D a) a -> [(b, Stack)]
eval = run [] W . lower

-- Second-Order Default Evaluation
eeval :: K (D b) r (K r (D a) a) -> [(b, Stack)]
eeval = run [] W . llower
-- ------------------------------------------------


-- Scope Capture
-- ------------------------------------------------
-- force evaluation of quantificational constituents, delimiting their scope

-- First-Order Reset
res :: K (D r) (D a) a -> K (D r') (D r') r
res = ixlift . lower
-- equivalent to:
-- res m = ixcont $ \k -> do x <- lower m
--                           k x
-- ignoring type constructors:
--       = \k -> m unit --@ k
--       = \k s -> concat [k x s' | (x,s') <- m unit s]

-- Second-Order Total Reset
rres :: K (D b) r (K r (D a) a) -> K (D u) (D u) (K (D r') (D r') b)
rres = kkunit . ixlift . llower
-- ignoring type constructors:
-- rres = \M c -> llower M --@ \a -> c (kunit a)
--      = \M c s -> concat [c (kunit m) s' | (m,s') <- llower M s]

-- Second-Order Inner Reset
rres1 :: K t s (K (D r) (D a) a) -> K t s (K (D r') (D r') r)
rres1 = ixliftM res
-- equivalent to:
-- rres1 = \mm -> $ do m <- mm
--                     kunit (res m)
-- ignoring type constructors:
--       = \M c -> M (\m -> c (res m))

-- Second-Order Staged Reset (preserves scopal structure)
-- note that this won't type out for 3-level towers topped by universals;
-- they'll be forced to use the total reset
rres2 :: K (D u) (D (K (D r) (D r) r)) (K (D r) (D a) a) -> K (D r') (D r') u
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

_up :: D Ent -> D Ent
_up m = do x <- m
           modify (++[x])
           unit x
-- ignoring type constructors:
--    = \s -> [(x, s'++[x]) | (x,s') <- m s]

-- First-Order Push
up :: K r (D o) Ent -> K r (D o) Ent
up m = m --* \x -> ixlift (modify (++[x])) --* \_ -> kunit x
-- equivalent to:
-- up m = do x <- m
--           ixlift (modify (++[x]))
--           kunit x
-- ignoring type constructors:
--     = \k -> m (\x s -> k x (s++[x]))

-- Second-Order Push
uup :: K t s (K r (D o) Ent) -> K t s (K r (D o) Ent)
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
likes, envies, pities, listensTo, overwhelm :: EET (D r)
[likes, envies, pities, listensTo, overwhelm] =
  map wlift [_likes, _envies, _pities, _listensTo, _overwhelm]
-- ------------------------------------------------

-- Ditransitive Verbs
-- ------------------------------------------------
gave :: EEET (D r)
gave = wlift _gave
-- ------------------------------------------------

-- Attitudes
-- ------------------------------------------------
_thinks :: D Bool -> D (Ent -> Bool)
_thinks m = do s <- get
               w <- ask
               unit $ \x -> all (\w' -> any fst $ run s w' m) (_bel x w)
  where _bel _ _ = domWorlds -- S5 modal frame
                             -- and since there's only the actual world,
                             -- everybody's omniscient

thinks :: K (D r) (D r) (D Bool -> D (Ent -> Bool))
thinks = kunit _thinks
-- ------------------------------------------------


-- CONNECTIVES
-- ===========

-- Boolean Operators
-- ------------------------------------------------
conj :: TTT (D r)
conj = kunit (&&)

disj :: IxMonadPlus m => m i j a -> m i j a -> m i j a
disj = implus

_neg :: D Bool -> D Bool
_neg m = do s <- get
            w <- ask
            unit $ not $ any fst $ run s w m

neg :: K (D r) (D r) (D Bool -> D Bool)
neg = kunit _neg
-- ------------------------------------------------


-- ADJECTIVES
-- ==========

-- Intersective Adjectives
-- ------------------------------------------------
short, tall :: K (D r) (D r) ((Ent -> Bool) -> Ent -> Bool)
[short, tall] = map wlift [_short, _tall]
-- ------------------------------------------------

-- Relational Adjectives
-- ------------------------------------------------
fav :: K (D r) (D r) ((Ent -> Bool) -> Ent -> Ent)
fav = wlift _fav
-- ------------------------------------------------


-- PREPOSITIONS
-- ============

-- ------------------------------------------------
of_ :: K (D r) (D r) ((Ent -> Bool) -> Ent -> Ent -> Bool)
of_ = wlift _of
-- ------------------------------------------------


-- NOMINALS
-- ========

-- Proper Names
-- ------------------------------------------------
-- all rigid designators
b1, b2, b3, b4, b5, b6 :: E (D r)
[b1, b2, b3, b4, b5, b6] = map (wlift . const) boys

g1, g2, g3, g4, g5, g6 :: E (D r)
[g1, g2, g3, g4, g5, g6] = map (wlift . const) girls

p1, p2, p3, p4, p5, p6 :: E (D r)
[p1, p2, p3, p4, p5, p6] = map (wlift . const) poems
-- ------------------------------------------------

-- Pronouns
-- ------------------------------------------------
-- pronouns are indexed from the back of the stack;
-- out-of-bounds indices throw "Assertion failed" errors :)
_pro :: Int -> D Ent
_pro n = gets $ \s -> assert (length s >= n + 1) $ reverse s !! n

pro :: Int -> E (D r)
pro n = ixlift (_pro n)
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
boy, girl, poem, thing :: ET (D r)
[boy, girl, poem, thing] = map wlift [_boy, _girl, _poem, _thing]

-- Abbreviations
tb,tg,sb,sg :: ET (D r)
tb = tall ~/~ boy
tg = tall ~/~ girl
sb = short ~/~ boy
sg = short ~/~ girl
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

p123, b123 :: E (D r)
[p123, b123] = map (wlift . const) [_p123, _b123]
-- ------------------------------------------------


-- DETERMINERS
-- ===========

-- Indefinites
-- ------------------------------------------------
_some :: (Ent -> D Bool) -> D Ent
_some p = do x <- lift $ ListT $ const domAtoms
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
poss :: E (D r) -> ET (D Bool) -> K (D r) (D r) (K (D Ent) (D Bool) Bool)
poss g p = kunit some ~\\~ ((kunit p ~\\~ kunit of_) ~//~ kkunit g)
-- ------------------------------------------------


-- RELATIVE CLAUSES
-- ================

_gap :: Int -> D Ent
_gap = _pro

gap :: Int -> E (D r)
gap = pro

_that :: Bool -> Bool -> Bool
_that = (&&)

that :: TTT (D r)
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
eval $ ( lower $ (up every ~\~ boy) ~\~ that ~/~ (res $ up g3 ~\~ likes ~/~ gap 1) ) ~\~ sb


Attitudes
---------
"Boy3 thinks Girl2 is short"
eval $ up b3 ~\~ (ixlift $ llower $ iixlift $ thinks ~/~ (kunit $ lower $ res $ up p2 ~\~ sg))

"Boy3 thinks some girl is short" [surface scope]
eval $ up b3 ~\~ (ixlift $ llower $ iixlift $ thinks ~/~ (kunit $ lower $ res $ (res $ up some ~\~ girl) ~\~ sg))

"Boy3 thinks some poem is short" [inverse scope]
eval $ up b3 ~\~ (ixlift $ llower $ iixlift $ thinks ~/~ (llower1 $ kkunit $ res $ (res $ up some ~\~ girl) ~\~ sg))


-}
