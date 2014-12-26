
module ContStateList where

import Model
import Control.Applicative hiding (some)
import Control.Monad.Cont
import Control.Monad.State
import Control.Exception (assert)

-- =================
-- ** TYPE SYSTEM ** 
-- =================

type Stack = [Ent]
type D     = StateT Stack []  -- D a := s -> [(a,s)]
type K r a = ContT r D a -- K r a := (a -> D r) -> D r
                         --       == (a -> s -> [(r,s)]) -> s -> [(r,s)]

type E r    = K r Ent
type T r    = K r Bool
type ET r   = K r (Ent -> Bool)
type EET r  = K r (Ent -> Ent -> Bool)
type EEET r = K r (Ent -> Ent -> Ent -> Bool)
type TTT r  = K r (Bool -> Bool -> Bool)

instance (Alternative m) => Alternative (ContT r m) where
  empty = ContT $ const empty
  m <|> n = ContT $ \c -> runContT m c <|> runContT n c

instance (MonadPlus m) => MonadPlus (ContT r m) where
  mzero = ContT $ const mzero
  m `mplus` n = ContT $ \c -> runContT m c `mplus` runContT n c


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

-- Scope Sequencing Combinator
(--*) :: K r a -> (a -> K r b) -> K r b
(--*) = (>>=)
-- ignoring type constructors:
-- -- m --* f = \k -> m (\x -> f x k)
infixl 1 --*
-- ------------------------------------------------


-- Scope Shift
-- ------------------------------------------------
-- inject values into trivial (pure) computations

-- First-Order Scope ("Montague lift")
kunit :: a -> K r a 
kunit = return
-- equivalent to:
-- kunit = lift . unit
--   (where 'lift' is the transformer of the K type: \m k -> m --@ k)
-- ignoring type constructors:
--       = \x k -> k x
  
-- Second-Order Scope ("Internal lift")
kkunit :: K r a -> K r (K r' a)
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

lap :: K r a -> K r (a -> b) -> K r b
lap = liftM2 (flip ($))
-- equivalent to:
-- lap = \m h -> do x <- m
--                  f <- h
--                  kunit (f x)
-- ignoring type constructors:
--     = \m h k -> m (\x -> h (\f -> k (f x)))

rap :: K r (a -> b) -> K r a -> K r b
rap = liftM2 ($)
-- equivalent to:
-- rap = \h m -> do f <- h
--                  x <- m
--                  kunit (f x)
-- ignoring type constructors:
--     = \h m k -> h (\f -> m (\x -> k (f x)))

-- Second-Order Continuized Application

llap :: K r' (K r a) -> K r' (K r (a -> b)) -> K r' (K r b)
llap = liftM2 lap
-- equivalent to:
-- llap = \M H -> do m <- M
--                   h <- H
--                   kunit (m `lap` h)
-- ignoring type constructors:
--      = \M H k -> M (\m -> H (\h -> k (m `lap` h)))

rrap :: K r' (K r (a -> b)) -> K r' (K r a) -> K r' (K r b)
rrap = liftM2 rap
-- equivalent to:
-- rrap = \H M -> do h <- H
--                   m <- M
--                   kunit (h `rap` m)
-- ignoring type constructors:
--      = \H M k -> H (\h -> M (\m -> k (h `rap` m)))

-- Infix combinators for left and right application

(~/~) :: K r (a -> b) -> K r a -> K r b
(~/~) = rap
infixr 9 ~/~

(~//~) :: K r' (K r (a -> b)) -> K r' (K r a) -> K r' (K r b)
(~//~) = rrap
infixr 9 ~//~

(~\~) :: K r a -> K r (a -> b) -> K r b
(~\~) = lap
infixr 9 ~\~

(~\\~) :: K r' (K r a) -> K r' (K r (a -> b)) -> K r' (K r b)
(~\\~) = llap
infixr 9 ~\\~
-- ------------------------------------------------


-- Program Evaluation
-- ------------------------------------------------
-- execute programmatic meanings with trivial continuations/states

-- First-Order Lower
lower :: K a a -> D a
lower m = runContT m unit
-- ignoring type constructors:
-- lower = kunit unit
--       = \m -> m unit

-- Second-Order (Total) Lower
llower :: K a (K a a) -> D a
llower mm = runContT mm lower
-- equivalent to:
-- llower = lower . join
--   (where 'join' is the join of the ContT monad: \M -> M --* id)
--        = \mm -> flip runContT unit $ do m <- mm; m
-- ignoring type constructors:
-- llower = kunit lower
--        = \M -> M (\m -> m unit)

-- Evaluation in Default Context
run :: Stack -> D a -> [(a,Stack)]
run = flip runStateT

-- First-Order Default Evaluation
eval :: K a a -> [(a,Stack)] 
eval = run [] . lower

-- Second-Order Default Evaluation
eeval :: K a (K a a) -> [(a, Stack)]
eeval = run [] . llower


-- Scope Capture
-- ------------------------------------------------
-- force evaluation of quantificational constituents, delimiting their scope

-- First-Order Reset
res :: K a a -> K r a
res = lift . lower
-- equivalent to:
-- res m = ContT $ \k -> do x <- lower m
--                          k x
-- ignoring type constructors:
--       = \k -> m unit --@ k
--       = \k s -> concat [k x s' | (x,s') <- m unit s]

-- Second-Order Total Reset
rres :: K a (K a a) -> K r' (K r a)
rres = kkunit . lift . llower
-- ignoring type constructors:
-- rres = \M c -> llower M --@ \a -> c (kunit a)
--      = \M c s -> concat [c (kunit m) s' | (m,s') <- llower M s]

-- Second-Order Inner Reset
rres1 :: K r (K a a) -> K r (K r' a)
rres1 = liftM res
-- equivalent to:
-- rres1 = \mm -> $ do m <- mm
--                     kunit (res m)
-- ignoring type constructors:
--       = \M c -> M (\m -> c (res m))

-- Second-Order Staged Reset (preserves scopal structure)
-- note that this won't type out for 3-level towers topped by universals;
-- they'll be forced to use the total reset
rres2 :: K (K r a) (K a a) -> K r' (K r a)
rres2 = res . liftM res
-- equivalent to:
-- rres2 = \mm -> reset $ do m <- mm
--                           kunit (reset m)
-- ignoring type constructors:
--       = \M -> lift $ M (\m -> unit (reset m))
--       = \M c s -> concat [c m s' | (m,s') <- M (unit . reset) s]


-- Stack Update
-- ------------------------------------------------
-- extract drefs from continuized individuals and append them to the stack

-- Push in the State Monad
_up :: D Ent -> D Ent
_up m = do x <- m
           modify (++[x])
           unit x
-- ignoring type constructors:
--    = \s -> [(x, s'++[x]) | (x,s') <- m s]

-- First-Order Push
up :: E r -> E r
up = withContT $ \k x -> k x `butWith` (++[x])
  where butWith = flip withStateT
-- equivalent to:
-- up m = do x <- m
--           lift (modify (++[x]))
--           kunit x
-- ignoring type constructors:
--      = \k -> m (\x s -> k x (s++[x]))

-- Second-Order Push
uup :: K r' (E r) -> K r' (E r)
uup = liftM up
-- equivalent to:
-- uup = ((unit up) ~/~)
--     = \mm -> do m <- mm
--                 kunit (up m)
-- ignoring type constructors:
--     = \M k -> M (\m -> k (up m))


-- =========================
-- ** AUXILIARY FUNCTIONS **
-- =========================

-- Backwards function application
(<$) :: a -> (a -> b) -> b
a <$ b = b a

-- Stack difference
-- (this really only makes sense if stacks are the same length) 
minus :: Stack -> Stack -> Stack
s1 `minus` s2 = take ((length s1) - (length s2)) s1


-- ==================
-- ** THE LANGUAGE **
-- ==================

-- PREDICATES
-- ===========

-- Transitive Verbs
-- ------------------------------------------------
likes, envies, pities, listensTo, overwhelm :: EET r
[likes, envies, pities, listensTo, overwhelm] =
  map kunit [_likes, _envies, _pities, _listensTo, _overwhelm]
-- ------------------------------------------------

-- Ditransitive Verbs
-- ------------------------------------------------
gave :: EEET r
gave = kunit _gave
-- ------------------------------------------------


-- CONNECTIVES
-- ===========

-- Boolean Operators
-- ------------------------------------------------
conj :: TTT r
conj = kunit (&&)

disj :: MonadPlus m => m a -> m a -> m a
disj = mplus

_neg :: D Bool -> D Bool
_neg m = StateT $ \s -> [(not $ any fst $ run s m, s)]

neg :: T Bool -> T Bool
neg m = lift $ _neg (lower m)
-- ------------------------------------------------


-- ADJECTIVES
-- ==========

-- Intersective Adjectives
-- ------------------------------------------------
short, tall :: K r ((Ent -> Bool) -> Ent -> Bool)
[short, tall] = map kunit [_short, _tall]
-- ------------------------------------------------

-- Relational Adjectives
-- ------------------------------------------------
fav :: K r ((Ent -> Bool) -> Ent -> Ent)
fav = kunit _fav
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
of_ :: K r ((Ent -> Bool) -> Ent -> Ent -> Bool)
of_ = kunit _of
-- ------------------------------------------------


-- NOMINALS
-- ========

-- Proper Names
-- ------------------------------------------------
b1, b2, b3, b4, b5, b6 :: E r
[b1, b2, b3, b4, b5, b6] = map kunit boys

g1, g2, g3, g4, g5, g6 :: E r
[g1, g2, g3, g4, g5, g6] = map kunit girls

p1, p2, p3, p4, p5, p6 :: E r
[p1, p2, p3, p4, p5, p6] = map kunit poems
-- ------------------------------------------------

-- Pronouns
-- ------------------------------------------------
-- pronouns are indexed from the back of the stack;
-- out-of-bounds indices throw "Assertion failed" errors :)
_pro :: Int -> D Ent
_pro n = gets $ \s -> assert (length s >= n + 1) $ reverse s !! n

pro :: Int -> E r
pro n = lift (_pro n)
-- equivalent to:
-- pro n = lift $ do s <- iget
--                   unit (reverse s !! n)
-- ignoring type constructors:
--       = \k -> \s -> k (reverse s !! n) s

-- convenience pronoun for grabbing the most recent dref
pro0 :: E r
pro0 = pro 0
-- ------------------------------------------------

-- Common Nouns
-- ------------------------------------------------
boy, girl, poem, thing :: ET r
[boy, girl, poem, thing] = map kunit [_boy, _girl, _poem, _thing]
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
-- can't tease the quantifiers into the ContT monad because their intermediate
-- and return types don't match! see IxContGrammar.hs
-- here, we just pass restrictors in directly, and ignore relative clauses

-- Indefinites
-- ------------------------------------------------
_some :: (Ent -> D Bool) -> D Ent
_some p = do x <- lift domAtoms
             p x --@ guard
             unit x

some :: ET r -> E r
some p = do x <- lift $ lift domAtoms
            (p ~/~ kunit x) --* guard
            kunit x
-- ------------------------------------------------
 
-- Universals
-- ------------------------------------------------
every :: ET Bool -> E Bool
every p = ContT $ \k -> lower $ neg $ some p --* neg . lift . k
-- ------------------------------------------------

-- Possessives
-- ------------------------------------------------
poss :: E r -> ET r' -> K r (E r')
poss g p = kunit some ~/~ ((kunit p ~\\~ kunit of_) ~//~ kkunit g)
-- ------------------------------------------------


-- ==============
-- ** EXAMPLES **
-- ==============

{-

Basic Sentences
---------------
"Boy4 is tall"
eval $ up b4 ~\~ tb

"Boy1 is short and Boy5 is tall"
eval $ (res $ up b1 ~\~ sb) ~\~ conj ~/~ (res $ up b5 ~\~ tb)

"Some boy is tall"
eval $ (up $ some boy) ~\~ tb

"Some tall boy likes some tall girl"
eval $ (up $ some tb) ~\~ likes ~/~ (up $ some tg)


Basic Anaphora
--------------
"Boy 4 likes his poem"
eeval $ (kkunit $ up b4) ~\\~ kunit likes ~//~ (uup $ poss pro0 poem)

"Boy 1 is short and he is tall"
eval $ (up b1 ~\~ sb) ~\~ conj ~/~ pro0 ~\~ tb

"Some boy is short and he is tall"
eval $ (res $ (up $ some boy) ~\~ sb) ~\~ conj ~/~ (res $ pro0 ~\~ tb)

"Every boy is short and he is tall" [Binding failure]
eval $ (res $ (up $ every boy) ~\~ sb) ~\~ conj ~/~ (res $ pro0 ~\~ tb)


Inverse Scope
-------------
"Some tall boy likes every tall girl" [surface scope]
eval $ (up $ some tb) ~\~ likes ~/~ (up $ every tg)

"Some tall boy likes every tall girl" [inverse scope]
eeval $ (kunit $ up $ some tb) ~\\~ kunit likes ~//~ (kkunit $ up $ every tg)

-}
