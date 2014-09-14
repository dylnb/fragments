{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances #-}

import IxPrelude
import Control.Monad.Indexed
import Control.Monad.Indexed.State
import Control.Monad.Indexed.Cont
import Control.Monad.Indexed.Trans
import Data.List (permutations, transpose)
import Control.Exception (assert)
import Prelude hiding (Monad(..))

-- =================
-- ** TYPE SYSTEM ** 
-- =================

data Ent = Atom (String,Int)
         | Plur {atoms :: [Ent]}

type Stack   = [Ent]
type D       = IxStateT [] Stack Stack -- D a := s -> [(a,s)]
type K       = IxCont

type E r     = K r r Ent
type T r     = K r r Bool
type ET r    = K r r (Ent -> Bool)
type EET r   = K r r (Ent -> Ent -> Bool)
type EEET r  = K r r (Ent -> Ent -> Ent -> Bool)
type ETE r   = K r r ((Ent -> Bool) -> Ent)
type ETET r  = K r r ((Ent -> Bool) -> Ent -> Bool)

instance Show Ent where
  show (Atom (x,y)) = x ++ show y
  show (Plur xs)    = foldl (\a b -> a ++ "+" ++ show b) "" xs

instance Eq Ent where
  (Atom x) == (Atom y)   = x == y
  (Plur xs) == (Plur ys) = xs == ys
  _ == _                 = False

instance Ord Ent where
  compare (Atom (_,tag)) (Atom (_,tag')) = compare tag tag'
  compare _ _                            = EQ


-- ========================
-- ** MONADIC OPERATIONS **
-- ========================

-- Synonyms for the monad operators of StateT, to distinguish them for clarity
-- from those of IxContT
unit :: a -> D a
unit = return
-- ignoring type constructors:
-- unit x = \s -> [(x,s)]

(--@) :: D a -> (a -> D b) -> D b
(--@) = (>>=)
-- ignoring type constructors:
-- m --@ f = \s -> concat [f x s' | (x,s') <- m s]
infixl 1 --@

-- 'lift' is semantically equivalent to (--@),
-- but with type constructors that will support various monad class functions
-- including do-notation
lift :: D a -> K (D b) (D b) a
lift m = ixcont $ \k -> m --@ k


-- SCOPE SHIFTERS
-- ==============

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

-- Scope Sequencing Combinator
(--*) :: K r o a -> (a -> K o r' b) -> K r r' b
(--*) = (>>=)
-- ignoring type constructors:
-- m --* f = \k -> m (\x -> f x k)
infixl 1 --*

-- LEFT AND RIGHT APPLICATION
-- ==========================

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

-- Infix operators for the application combinators
(~/~)  = rap
(~//~) = rrap
(~\~)  = lap
(~\\~) = llap

-- EVALUATION
-- ==========
-- execute programmatic meanings with trivial continuations/states

-- First-Order Lower
lower :: K r (D a) a -> r
lower = \m -> runIxCont m unit
-- ignoring type constructors:
-- lower = pure unit
--       = \m -> m unit

-- Second-Order (Total) Lower
llower :: K t r (K r (D a) a) -> t
llower = \mm -> runIxCont mm lower
-- equivalent to:
-- llower = lower . join
--   (where 'join' is the join of the ContT monad: \M -> M --* id)
--        = \mm -> flip runIxContT unit $ do m <- mm; m
-- ignoring type constructors:
-- llower = pure lower
--        = \M -> M (\m -> m unit)

{- do we need this?
-- Second-Order Internal Lower
llowerBelow :: K t s (K r (D a) a) -> K t s r
llowerBelow = liftM lower
-- equivalent to:
-- llowerBelow = \mm -> do m <- mm
--                         pure (lower m)
-- ignoring type constructors:
--             = (~/~ lower)
--             = \M k -> M (\m -> lower (\l -> k (m l))
--             = \M k -> M (\m -> k (m unit))
-}

-- Evaluation in Default Context
run :: Stack -> D a -> [(a, Stack)]
run = flip runIxStateT

-- First-Order Default Evaluation
-- eval :: K r a a -> [(r, Stack)] 
eval :: K (D b) (D a) a -> [(b, Stack)]
eval = run [] . lower

-- Second-Order Default Evaluation
-- eeval :: K s r (K r a a) -> [(s, Stack)]
eeval :: K (D b) r (K r (D a) a) -> [(b, Stack)]
eeval = run [] . llower


-- RESET
-- =====
-- forces evaluation of quantificational constituents, delimiting their scope

-- First-Order Reset
res :: K (D r) (D a) a -> K (D r') (D r') r
-- res :: K r a a -> K r' r' r
res = lift . lower
-- equivalent to:
-- res m = ixcont $ \k -> do x <- lower m
--                           k x
-- ignoring type constructors:
--         = \k -> m unit --@ k
--         = \k s -> concat [k x s' | (x,s') <- m unit s]

-- Second-Order Total Reset
rres :: K (D b) r (K r (D a) a) -> K (D u) (D u) (K r' r' b)
rres = ppure . lift . llower
-- ignoring type constructors:
-- rres = \M c -> llower M --@ \a -> c (pure a)
--      = \M c s -> concat [c (pure m) s' | (m,s') <- llower M s]

-- Second-Order Staged Reset (preserves scopal structure)
-- note that this won't type out for 3-level towers topped by universals;
-- they'll be forced to use the total reset
-- rres2 :: K t (K s s r) (K r a a) -> K r' r' t
rres2 :: K (D r) (D (K (D r'1) (D r'1) r1)) (K (D r1) (D a) a) -> K (D r') (D r') r
rres2 = res . liftM res
-- equivalent to:
-- rres2 = \mm -> res $ do m <- mm
--                         pure (res m)
-- ignoring type constructors:
--       = \M -> lift $ M (\m -> unit (res m))
--       = \M c s -> concat [c m s' | (m,s') <- M (unit . res) s]

-- STACK UPDATE
-- ============
-- extracts a dref from a continuized individual; appends it to the state

_up :: D Ent -> D Ent
_up m = do x <- m
           modify (++[x])
           unit x
-- ignoring type constructors:
--    = \s -> [(x, s'++[x]) | (x,s') <- m s]

-- First-Order Push
up :: K r (D o) Ent -> K r (D o) Ent
up m = do x <- m
          lift (modify (++[x]))
          pure x
-- ignoring type constructors:
--      = \k -> m (\x s -> k x (s++[x]))

-- Second-Order Push
uup :: K t s (K r (D o) Ent) -> K t s (K r (D o) Ent)
uup = liftM up
-- equivalent to:
-- uup = ((unit up) ~/~)
--     = \mm -> do m <- mm
--                 pure (up m)
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

-- connective for fusing multiple individuals into a plurality
oplus :: Ent -> Ent -> Ent
oplus x@(Atom _) y@(Atom _) = Plur [x,y]
oplus x@(Atom _) (Plur ys)  = Plur (x:ys)
oplus (Plur xs) y@(Atom _)  = Plur (xs++[y])
oplus (Plur xs) (Plur ys)   = Plur (xs++ys)


-- ===============
-- ** THE MODEL **
-- ===============

-- INDIVIDUALS
-- ===========

-- Atomic Individuals
boys, girls, poems :: [Ent]
boys     = map (\x -> Atom ("b",x)) [1..6]
girls    = map (\x -> Atom ("g",x)) [1..6]
poems    = map (\x -> Atom ("p",x)) [1..6]

-- Plural Individuals
shortboys, shortgirls, shortpoems :: Ent
shortboys  = Plur $ take 3 boys
shortgirls = Plur $ take 3 girls
shortpoems = Plur $ take 3 poems

-- The Domain
domAtoms, domPlurs, univ :: [Ent]
domAtoms = concat [boys, girls, poems]
domPlurs = [shortboys, shortgirls, shortpoems]
univ     = domAtoms ++ domPlurs

-- Some pre-fab D Bools with histories, for testing
dbooltest1 :: D Bool
dbooltest1 = IxStateT $ \s -> [(True, s++xs) | xs <- [perms!!0, perms!!3, perms!!4]]
  where perms = permutations $ take 3 girls
-- run [] dbooltest1 = [(True,[g1,g2,g3]), (True,[g2,g3,g1]), (True,[g3,g1,g2])]

dbooltest2 :: D Bool
dbooltest2 = do _ <- dbooltest1
                modify (\gs -> concat $ take (length gs) $ transpose [boys, gs])
                unit True
-- run [] dbooltest2 = [(True,[b1,g1,b2,g2,b3,g3]),
--                      (True,[b1,g2,b2,g3,b3,g1]),
--                      (True,[b1,g3,b2,g1,b3,g2])]


-- ==================
-- ** THE LANGUAGE **
-- ==================

-- NOMINALS
-- ========

-- Proper Names
-- ------------------------------------------------
_b1, _b2, _b3, _b4, _b5, _b6 :: Ent
[_b1, _b2, _b3, _b4, _b5, _b6] = boys

b1, b2, b3, b4, b5, b6 :: E r
[b1, b2, b3, b4, b5, b6] = map pure boys


_g1, _g2, _g3, _g4, _g5, _g6 :: Ent
[_g1, _g2, _g3, _g4, _g5, _g6] = girls

g1, g2, g3, g4, g5, g6 :: E r
[g1, g2, g3, g4, g5, g6] = map pure girls


_p1, _p2, _p3, _p4, _p5, _p6 :: Ent
[_p1, _p2, _p3, _p4, _p5, _p6] = poems

p1, p2, p3, p4, p5, p6 :: E r
[p1, p2, p3, p4, p5, p6] = map pure poems
-- ------------------------------------------------

-- Pronouns
-- ------------------------------------------------
-- pronouns are indexed from the back of the stack;
-- out-of-bounds indices throw "Assertion failed" errors :)
_he :: Int -> D Ent
_he n = gets $ \s -> assert (length s >= n + 1) $ reverse s !! n

he :: Int -> E (D r)
he n = lift (_he n)
-- equivalent to:
-- he n = lift $ do s <- get
--                  unit (reverse s !! n)
-- ignoring type constructors:
--      = \k -> \s -> k (reverse s !! n) s
-- ------------------------------------------------

-- Common Nouns
-- ------------------------------------------------
_boy, _girl, _poem, _thing :: Ent -> Bool

_boy (Atom ("b",_)) = True
_boy _              = False

_girl (Atom ("g",_)) = True
_girl _              = False

_poem (Atom ("p",_)) = True
_poem _              = False 

_thing = const True

boy, girl, poem, thing :: ET r
[boy, girl, poem, thing] = map pure [_boy, _girl, _poem, _thing]
-- ------------------------------------------------
 
-- Plurals
-- ------------------------------------------------
-- 'pl' below converts a property of individuals into a property of sums,
-- interpreted distributively
-- pl :: ET Bool -> ET r
-- pl p = let p' (Plur xs) = all (any fst . eval . check p) xs
--            p' _         = False in
--        pure p'
-- ------------------------------------------------

-- PREDICATES
-- ===========

-- Two-Place Predicates
-- ------------------------------------------------
_likes, _envies, _pities, _listensTo, _overwhelm :: Ent -> Ent -> Bool

-- people like other people when their indices match:
-- b1 likes g1, g3 likes b3, but g5 doesn't like b4 or g4
_likes (Atom (x,n)) (Atom (y,m)) = n == m && y /= "p" && x /= "p"
_likes _ _                       = False

-- people envy people of the same gender that they are less than:
-- b1 envies b3, but b3 does not envy b1 nor does he envy g6
_envies (Atom (x,n)) (Atom (y,m)) = x == y && n > m
_envies _ _                       = False

-- people pity people that envy them:
-- b3 pities b1, but not g1, nor does b1 pity him
_pities (Atom (x,n)) (Atom (y,m)) = x == y && n < m
_pities _ _                       = False

-- people listen to people of the opposite gender that they divide evenly:
-- b2 listens to g6, as does b3, but b4 doesn't, and neither does g2
_listensTo (Atom (x,n)) (Atom (y,m)) = n `mod` m == 0 &&
                                       (x == "g" && y == "b"  ||
                                        x == "b" && y == "g")
_listensTo _ _                       = False

-- +p1+p2+p3 overwhelm g6, and +b1+b2+b3 overwhelm each of b1,b2, and b3;
-- nothing else overwhelms anyone else
_overwhelm y xs = xs == shortpoems && y == girls!!5 ||
                  xs == shortboys  && y `elem` (take 3 boys)


likes, envies, pities, listensTo, overwhelm :: EET r
[likes, envies, pities, listensTo, overwhelm] =
  map pure [_likes, _envies, _pities, _listensTo, _overwhelm]
-- ------------------------------------------------

-- Three-Place Predicates
-- ------------------------------------------------
_gave :: Ent -> Ent -> Ent -> Bool
-- boys give girls poems in runs:
-- b1 gave g2 p3, and b4 gave g5 p6, but b1 didn't give g3 anything, and he
-- didn't give p4 to anybody
_gave (Atom (x,n)) (Atom (y,m)) (Atom (z,o)) = x == "g" && y == "p" &&
                                               z == "b" && n == o+1 && m == n+1
_gave _ _ _                                  = False

gave :: EEET r
gave = pure _gave
-- ------------------------------------------------


-- CONNECTIVES
-- ===========

conj ::  IxMonad m => m i j Bool -> m j k Bool -> m i k Bool
conj = liftM2 (&&)

disj ::  IxMonadPlus m => m i j a -> m i j a -> m i j a
disj = implus


-- ADJECTIVES
-- ==========

-- Intersective Adjectives
-- ------------------------------------------------
_short, _tall :: (Ent -> Bool) -> Ent -> Bool
_short p e@(Atom (_,n)) = p e && n <= 3
_short _ _              = False

_tall p e@(Atom (_,n)) = p e && n > 3
_tall _ _              = False

short, tall :: ETET r
[short, tall] = map pure [_short, _tall]
-- ------------------------------------------------

-- Abbreviations
tb,tg,sb,sg :: ET r
tb = tall ~/~ boy
tg = tall ~/~ girl
sb = short ~/~ boy
sg = short ~/~ girl


-- PREPOSITIONS
-- ============
_ownedBy :: (Ent -> Bool) -> Ent -> Ent -> Bool
-- 'ownedBy' approximates English 'of'. It takes two arguments, a noun
-- and an individual (the owner). So "poem `ownedby` b3" is the set of poems 
-- belonging to b3. As it happens, b1 doesn't have any poems.
_ownedBy p (Atom (_,n)) e@(Atom (y,m)) = p e && y == "p" && n == m && n /= 1
_ownedBy _ _ _                         = False

ownedBy :: K r r ((Ent -> Bool) -> Ent -> Ent -> Bool)
ownedBy = pure _ownedBy


-- QUANTIFIERS
-- ===========

-- Negation
-- ------------------------------------------------
_neg :: D Bool -> D Bool
_neg m = IxStateT $ \s -> [(any fst $ run s m, s)]

neg :: K r r (D Bool -> D Bool)
neg = pure _neg
-- ------------------------------------------------

-- Indefinites
-- ------------------------------------------------
_some :: (Ent -> D Bool) -> D Ent
_some p = do x <- ilift domAtoms
             p x --@ guard
             unit x

some :: K (D Ent) (D Bool) Ent
some = ixcont _some
-- ignoring type constructors:
--        = \k s -> concat [k x s' | x <- domAtoms, (b,s') <- p x s, b]
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
poss g p = pure some ~\\~ ((pure p ~\\~ pure ownedBy) ~//~ ppure g)
-- ------------------------------------------------

-- poss (lower $ every ~\~ boy) poem :: K (D Bool) (D Bool) (K (D Ent) (D Bool) Bool)
-- ppure $ lower $ every ~\~ boy :: K (D Bool) (D Bool) (E r)
-- ppure $ res $ some ~\~ boy :: K (D u) (D u) (E r)
-- llower :: K t r (K r (D a) a) -> t
-- (liftM res) $ poss (lower $ every ~\~ boy) poem :: K (D Bool) (D Bool) (E (D r))
--

-- ==============
-- ** EXAMPLES **
-- ==============

{-

BASIC SENTENCES
===============

"Boy4 is a tall boy"
eval $ up b4 ~\~ tb

"Some tall boy likes some tall girl"
eval $ (up $ res $ some ~\~ tb) ~\~ (likes ~/~ (up $ res $ some ~\~ tg))

-}
