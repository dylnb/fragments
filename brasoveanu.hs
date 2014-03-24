{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- mashup of Brasoveanu 2011 with de Groote 2007

import Debug.Trace
import Data.List (nub, subsequences, intersperse)
import Data.Maybe
import Control.Applicative
import Data.Traversable (sequenceA)

data Ent = Atom Char
         | Plur [Ent] deriving Eq

type Stack = [Ent]
type Stackset = [Stack]
type Continuation = Stackset -> Bool
type Prop = Stackset -> Continuation -> Bool
type GQ = (Int -> Prop) -> Prop


-- Print functions, Convenienve definitions
-- =====================================

getEnts :: Ent -> [Ent]
getEnts s@(Atom _) = [s]
getEnts   (Plur y) = y

trivial :: Continuation
trivial i = True

eval :: Prop -> Bool
eval s = s [[]] trivial

instance Show Ent where
  show y = intersperse '+' $ getEnts y >>= (\(Atom x) -> [x])

characteristic_set :: (Int -> Prop) -> [Ent]
characteristic_set p = [x | (x,n) <- zip atoms [0..], p n [atoms] trivial]

instance Show (Int -> Prop) where
  show p = show $ characteristic_set p 

characteristic_sets :: GQ -> [[Ent]]
characteristic_sets g =
  map (\h -> characteristic_set h) funcs
    where fn y  = \n is k -> (is!!0!!n) `elem` getEnts y
          funcs = filter (eval . g . ast) (map fn domain)

instance Show ((Int -> Prop) -> Prop) where
  show g = show $ characteristic_sets g


-- Populate the domain
-- ===================================
[a,b,c,d,e,f] = map Atom "abcdef"
atoms = [a,b,c,d,e,f]

plurs = map Plur [xs | xs <- subsequences atoms, length xs > 1]

domain = atoms ++ plurs


-- Basic operations on individuals
-- ==================================== 

-- turn a sum into a column vector
open_up :: Ent -> Stackset
open_up (x@(Atom _)) = [[x]]
open_up (   Plur y ) = sequenceA [y]

-- fuse a list of individuals into one (possibly) sum individual
join :: [Ent] -> Ent
join is | length ls > 1   = Plur ls
        | otherwise       = head ls
  where simpleAdd []              = []
        simpleAdd (x@(Atom _):is) = x:(simpleAdd is)
        simpleAdd (  (Plur i):is) = i ++ (simpleAdd is)
        ls = (nub . simpleAdd) is 

-- Link's maximal individual
top :: (Int -> Prop) -> Ent
top p = join (characteristic_set p)

-- "asterisk", Link's all-inclusive pluralizer
ast :: (Int -> Prop) -> Int -> Prop
ast p n (i1:i2:is) k = fn && (ast p n (i2:is) k)
  where fn | i1!!n `elem` atoms  = p n [i1] k
           | otherwise           = p 0 (open_up (i1!!n)) k
ast p n (i1:is) k = fn
  where fn | i1!!n `elem` atoms = p n [i1] k
           | otherwise          = p 0 (open_up (i1!!n)) k

-- plurals only
pl :: (Int -> Prop) -> Int -> Prop
pl p n is k | not $ any (\i -> i!!n `elem` atoms) is  = ast p n is k
            | otherwise                               = False


-- Basic operations on stacks
-- ===============================

ins :: Int -> Ent -> Stack -> Stack
ins 0 x i = x:i
ins n x (a:i) = a:(ins (n - 1) x i)



-- Interpretations
-- =================================


john :: (Int -> Prop) -> Prop
john p is k = p 0 (map (a:) is) k

he :: Int -> (Int -> Prop) -> Prop
he n p is k = p n is k

--boy, entered, poem, sat :: Int -> Prop
boy     n is k = (and (map (\i -> elem (i!!n) [a,b]) is)) && (k is)
entered n is k = (and (map (\i -> elem (i!!n) [a,b]) is)) && (k is)
poem    n is k = (and (map (\i -> elem (i!!n) [c,d]) is)) && (k is)
sat     n is k = (and (map (\i -> elem (i!!n) [a]) is)) && (k is)

recite, enjoy :: Int -> Int -> Prop
recite n m is k = (and (map (\i -> elem ((i!!n), (i!!m)) [(c,a),(d,b)]) is)) && (k is)
enjoy  n m is k = (and (map (\i -> elem ((i!!n), (i!!m)) [(c,a),(c,b)]) is)) && (k is)

conj :: Prop -> Prop -> Prop  -- after de Groote p. 3, (3) 
conj left right is k = left is (\is' -> right is' k)

every n res scope is k = 
  let fn x y = concat (map (\i -> [ins n x i, ins n y i]) is) in
    and [conj (res n) (scope n) (fn x y) trivial
           | x <- domain, y <- domain, x /= y, res n (fn x y) trivial]
    && (k is)

-- given stackset [i1, i2, ..., im], test whether there exist x1, x2, ..., xm
--   such that [i1^{x1/n}, i2^{x2/n}, ..., in^{xm/m}] satisfies res n; scope n
indef n res scope is k =
  or [conj (res n) (scope n) is' k 
       | is' <- foldr (\i -> \jss -> [(ins n x i):js | x <- domain, js <- jss]) [[]] is]

-- the index on "different" should be 2^n, where n is the number of intervening 
-- distributors between "different" and its distributor it wants to associate with
different :: Int -> (Int -> Prop) -> Int -> Prop
different index nom m = conj (nom m) (\is -> \k -> ((is!!0)!!m) /= ((is!!index)!!m) && (k is))

-- butfor is like the g[x]h operation in DPL and CDRT; it checks that stacks
--   i and j agree on every column except possibly the ones in ns
butfor :: [Int] -> Stack -> Stack -> Bool
butfor ns i j = 
  and [(i!!x) == (j!!x) | x <- filter (\y -> notElem y ns) [0..length i - 1]]

-- "diff" is another implementation option for different. the index on "diff" is
--   just the index of its associated distributor. it guarantees that if rows 
--   i and j agree on everything except possibly column n, then they differ on column n
diff :: Int -> (Int -> Prop) -> Int -> Prop
diff ind nom m =
  conj (nom m) (\is -> \k -> and [(i!!m) /= (j!!m)
        | i <- is, j <- is, i /= j, (butfor [ind,m] i j)] && (k is))

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

girl n is k = (and (map (\i -> elem (i!!n) [e,f]) is)) && (k is)
give n m l is k = (and (map (\i -> elem ((i!!n), (i!!m), (i!!l))
                                        [(f,c,a),(e,d,b),(f,c,b),(e,d,a)])
                            is)) && (k is)
give' n m l is k = (and (map (\i -> elem ((i!!n), (i!!m), (i!!l))
                                        [(f,c,a),(e,c,b),(f,d,b),(e,d,a)])
                            is)) && (k is)
give'' n m l is k = (and (map (\i -> elem ((i!!n), (i!!m), (i!!l))
                                        [(f,c,a),(e,c,a),(f,d,b),(e,d,b)])
                            is)) && (k is)

-- Ambiguous: Every boy gave/showed every girl a different poem
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 poem) (\m -> give n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 2 poem)) (\m -> give n m l)))) == False
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 poem) (\m -> give' n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give' n m l)))) == False
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 2 poem)) (\m -> give' n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give'' n m l)))) == False

same :: Int -> (Int -> Prop) -> Int -> Prop
same index nom m = conj (nom m) (\is -> \k -> ((is!!0)!!m) == ((is!!index)!!m) && (k is))

-- Every boy recited a same poem:
-- eval((every 0 boy) (\x -> (indef 1 (same 1 poem)) (\y -> recite y x))) == False

-- Every boy enjoyed a same poem:
-- eval((every 0 boy) (\x -> (indef 1 (same 1 poem)) (\y -> enjoy y x))) == True


