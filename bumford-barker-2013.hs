{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Debug.Trace
import Data.List (nub, subsequences, intersperse, (\\))
import Data.Maybe
import Control.Applicative
import Data.Traversable (sequenceA)


-- =================
-- ** TYPE SYSTEM ** 
-- =================

data Ent = Atom Char
         | Plur [Ent] deriving Eq
type Stack = [Ent]
type Stackset = [Stack]
type Continuation = Stackset -> Bool
type Prop = Stackset -> Continuation -> Bool
type GQ = (Int -> Prop) -> Prop


-- =========================
-- ** AUXILIARY FUNCTIONS ** 
-- =========================

-- Functions for handling continuations
-- ==================================== 

-- the trivial continuation; forces evaluation
trivial :: Continuation
trivial i = True

-- evaluates a sentence at the empty discourse context
eval :: Prop -> Bool
eval s = s [[]] trivial

-- Functions for handling stacks
-- ==================================== 

-- insert x at position n of stack i
ins :: Int -> Ent -> Stack -> Stack
ins 0 x i = x:i
ins n x (a:i) = a:(ins (n - 1) x i)

-- retrieve the atoms in an entity
-- (at least, when that entity is not "nested", like a+b+(b+d),
--  but such cases won't arise here)
getAtoms :: Ent -> [Ent]
getAtoms s@(Atom _) = [s]
getAtoms   (Plur y) = y

-- Functions for handling sums
-- ==================================== 

-- turn a sum into a column vector
open_up :: Ent -> Stackset
open_up (x@(Atom _)) = [[x]]
open_up (   Plur y ) = sequenceA [y]

-- fuse a set of entities into one sum entity
-- (if the set is a singleton, returns its element as an atom)
fuse :: [Ent] -> Ent
fuse is | length ls > 1   = Plur ls
        | otherwise       = head ls
  where simpleAdd []              = []
        simpleAdd (x@(Atom _):is) = x:(simpleAdd is)
        simpleAdd (  (Plur i):is) = i ++ (simpleAdd is)
        ls                        = (nub . simpleAdd) is

-- least upper bound of a set of entities 
top :: (Int -> Prop) -> Ent
top = fuse . cset

-- Link's "asterisk"; closes a property under sum-formation
-- (inclusive plural)
ast :: (Int -> Prop) -> Int -> Prop
ast p n (i1:i2:is) k = fn && (ast p n (i2:is) k)
  where fn | i1!!n `elem` atoms  = p n [i1] k
           | otherwise           = p 0 (open_up (i1!!n)) k
ast p n (i1:is) k = fn
  where fn | i1!!n `elem` atoms = p n [i1] k
           | otherwise          = p 0 (open_up (i1!!n)) k

-- closes a property under sum-formation, then excludes the atoms
-- (exclusive plural)
pl :: (Int -> Prop) -> Int -> Prop
pl p n is k | not $ any (\i -> i!!n `elem` atoms) is  = ast p n is k
            | otherwise                               = False


-- Functions for displaying individuals, properties, and GQs
-- ==================================== 

-- characteristic set of a property
cset :: (Int -> Prop) -> [Ent]
cset p = [x | (x,n) <- zip domain [0..], p n [domain] trivial]

-- the sets inside a GQ
csets :: GQ -> [[Ent]]
csets g = map cset cfuncs
  where cfn xs = \n is _ -> (is!!0!!n) `elem` getAtoms xs
        cfuncs = filter (eval . g . ast) $ map cfn domain

-- how to display entities and functions
instance Show Ent where
  show y = intersperse '+' $ getAtoms y >>= (\(Atom x) -> [x])
instance Show (Int -> Prop) where
  show = show . cset
instance Show ((Int -> Prop) -> Prop) where
  show = show . csets


-- ===============
-- ** THE MODEL **
-- ===============

-- INDIVIDUALS
-- ===========
[a,b,c,d,e,f] = map Atom "abcdef"
atoms = [a,b,c,d,e,f]

plurs = map Plur [xs | xs <- subsequences atoms, length xs > 1]

domain = atoms ++ plurs


-- ==================
-- ** THE LANGUAGE **
-- ==================

-- Proper Names, Pronouns
-- ------------------------------------------------
john :: (Int -> Prop) -> Prop
john p is k = p 0 (map (a:) is) k

he :: Int -> (Int -> Prop) -> Prop
he = flip id
-- more verbosely: he n p is k = p n is k


-- One-Place Predicates
-- ------------------------------------------------
boy, girl, entered, poem, sat :: Int -> Prop
-- a and b are boys
boy     n is k = all ((`elem` [a,b]) . (!!n)) is  &&  k is
-- e and f are girls
girl    n is k = all ((`elem` [e,f]) . (!!n)) is  &&  k is
-- a and b entered
entered n is k = all ((`elem` [a,b]) . (!!n)) is  &&  k is
-- c and d are poems
poem    n is k = all ((`elem` [c,d]) . (!!n)) is  &&  k is
-- only a sat
sat     n is k = all ((`elem` [a]  ) . (!!n)) is  &&  k is


-- Two-Place Predicates
-- ------------------------------------------------
recite, enjoy :: Int -> Int -> Prop
-- a recited c; b recited d
recite n m is k = all (\i -> ((i!!n), (i!!m)) `elem` [(c,a), (d,b)]) is  &&  k is
-- a enjoyed c; b enjoyed c
enjoy  n m is k = all (\i -> ((i!!n), (i!!m)) `elem` [(c,a), (c,b)]) is  &&  k is


-- Three-Place Predicates
-- ------------------------------------------------
give, give', give'' :: Int -> Int -> Int -> Prop
-- a and b both gave f to c and e to d; b gave e to d and 
give n m l is k = all (\i -> ((i!!n), (i!!m), (i!!l)) `elem`
                             [(f,c,a), (e,d,a), (f,c,b), (e,d,b)]) is  &&  k is
-- a gave' f to c and e to d; b gave f to d and e to c
give' n m l is k = all (\i -> ((i!!n), (i!!m), (i!!l)) `elem`
                              [(f,c,a), (e,d,a), (f,d,b), (e,c,b)]) is  &&  k is
-- a gave'' both f and e to c; b gave both f and e to d 
give'' n m l is k = all (\i -> ((i!!n), (i!!m), (i!!l)) `elem`
                               [(f,c,a), (e,c,a), (f,d,b), (e,d,b)]) is  &&  k is

-- Determiners
-- ------------------------------------------------
every, indef :: Int -> (Int -> Prop) -> GQ
every n res scope is k =
  and [conj (res n) (scope n) (fn x y) trivial |
       x <- domain, y <- domain \\ [x], res n (fn x y) trivial]  &&  k is
  where fn x y = is >>= (\i -> [ins n x i, ins n y i])

every' n res scope is k =
  and [conj (res n) (scope n) (fn x y) trivial |
       x <- domain, y <- domain \\ [x], res n (fn x y) trivial]  &&  k is
  where fn x y = is >>= (\i -> [ins n x i, ins n y i])

-- given stackset [i1, i2, ..., im], test whether there exist x1, x2, ..., xm
--   such that [i1^{x1/n}, i2^{x2/n}, ..., in^{xm/m}] satisfies res n; scope n
indef n res scope is k =
  or [conj (res n) (scope n) is' k 
       | is' <- foldr (\i jss -> [(ins n x i):js | x <- domain, js <- jss]) [[]] is]


-- Connectives
-- ------------------------------------------------
conj :: Prop -> Prop -> Prop
conj left right is k = left is (`right` k)


-- Adjectives
-- ------------------------------------------------
-- the index on "different" should be 2^n, where n is the number of intervening 
-- distributors between "different" and its distributor it wants to associate with
different :: Int -> (Int -> Prop) -> Int -> Prop
different index nom m =
  conj (nom m) (\is -> \k -> ((is!!0)!!m) /= ((is!!index)!!m) && (k is))

-- "diff" is another implementation option for different. the index on "diff" is
--   just the index of its associated distributor. it guarantees that if rows 
--   i and j agree on everything except possibly column n, then they differ on column n
diff :: Int -> (Int -> Prop) -> Int -> Prop
diff ind nom m =
  conj (nom m) $
    \is k -> and [(i!!m) /= (j!!m) | i <- is, j <- is, i /= j, butfor [ind,m] i j]
             && (k is)
  where butfor ns i j = and [(i!!x) == (j!!x) | x <- [0..length i - 1] \\ ns]
-- butfor is like the g[x]h operation in DPL and CDRT; it checks that stacks
--   i and j agree on every column except possibly the ones in ns

same :: Int -> (Int -> Prop) -> Int -> Prop
same index nom m =
  conj (nom m) (\is -> \k -> ((is!!0)!!m) == ((is!!index)!!m) && (k is))


-- ==============
-- ** EXAMPLES **
-- ==============

-- eval (john entered) == True
-- he 0 sat [[a,b]] trivial == True
-- he 1 sat [[a,d],[d,b]] trivial == False
-- eval ((john entered) `conj` (he 0 sat)) == True
-- eval (indef 0 boy sat) == True
-- eval(every 0 boy entered) == True
-- eval(every 0 boy sat) == False

-- Every boy read a (different) poem:
-- eval((every 0 boy) (\x -> (indef 1 poem) (\y -> recite y x))) == True
-- eval((every 0 boy) (\x -> (indef 1 (different 1 poem)) (\y -> recite y x))) == True

-- Every boy enjoyed a (different) poem:
-- eval((every 0 boy) (\x -> (indef 1 poem) (\y -> enjoy y x))) == True
-- eval((every 0 boy) (\x -> (indef 1 (different 1 poem)) (\y -> enjoy y x))) == False

-- Throws a runtime error, since "different" requires more than one stack on the stackset:
-- eval(john (\x -> (indef 1 (different 1 poem)) (\y -> enjoy y x)))


-- Ambiguous: Every boy gave/showed every girl a different poem
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 poem) (\m -> give n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 2 poem)) (\m -> give n m l)))) == False
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 poem) (\m -> give' n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give' n m l)))) == False
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 2 poem)) (\m -> give' n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give'' n m l)))) == False

-- Every boy recited a same poem:
-- eval((every 0 boy) (\x -> (indef 1 (same 1 poem)) (\y -> recite y x))) == False

-- Every boy enjoyed a same poem:
-- eval((every 0 boy) (\x -> (indef 1 (same 1 poem)) (\y -> enjoy y x))) == True


