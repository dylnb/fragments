{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- parasitic, anaphoric "same" with de Groote continuations

import Debug.Trace
import Data.List
import Data.Maybe

data Ent = Atom Char
         | Plur [Ent] deriving (Eq,Show)

type Stack = [Ent]
type Continuation = Stack -> Bool
type Prop = Stack -> Continuation -> Bool
type GQ = (Ent -> Prop) -> Prop
type Adj = (Ent -> Prop) -> Ent -> Prop


-- Print functions and convenience definitions
-- ======================================== 

trivial :: Continuation
trivial i = True

eval :: Prop -> Bool
eval s = s [] trivial

characteristic_set :: (Ent -> Prop) -> [Ent]
characteristic_set p = filter (eval . p) domain

instance Show (Ent -> Prop) where
  show p = show $ characteristic_set p

characteristic_sets :: GQ -> [[Ent]]
characteristic_sets g =
  map (\h -> characteristic_set h) funcs
    where fn s@(Atom y) = (\x i k -> x == s)
          fn   (Plur y) = (\x i k -> elem x y)
          funcs = filter (eval . g . ast) (map fn domain)

instance Show ((Ent -> Prop) -> Prop) where
  show g = show $ characteristic_sets g

-- Populate the domain
-- ======================================== 

[a,b,c,d,e,f,g,h] = map Atom "abcdefgh"
atoms = [a,b,c,d,e,f,g,h]

plurs = map Plur (filter (\x -> length x > 1) (subsequences atoms))
 
domain = atoms ++ plurs


-- Basic operations on individuals
-- ======================================== 

-- fuse a list of individuals into one (possibly) plural individual
join :: [Ent] -> Ent
join is | length ls > 1   = Plur ls
        | otherwise       = head ls
  where simpleAdd []              = []
        simpleAdd (x@(Atom i):is) = x:(simpleAdd is)
        simpleAdd (x@(Plur i):is) = i ++ (simpleAdd is)
        ls = (nub . simpleAdd) is 

-- Link's maximal individual
top :: (Ent -> Prop) -> Ent
top p = join (filter (eval . p) domain)

-- "asterisk", Link's all-inclusive pluralizer
ast :: (Ent -> Prop) -> Ent -> Prop
ast p s@(Atom y) i k = p s i k
ast p   (Plur y) i k = and (map (eval . p) y) && (k i)

-- plurals only
pl :: (Ent -> Prop) -> Ent -> Prop
pl p   (Atom y) i k = False
pl p s@(Plur y) i k = ast p s i k


-- Basic operations on stacks
-- ======================================== 

-- insert an indvidual to a position in a stack
ins :: Int -> Ent -> Stack -> Stack
ins 0 x i = x:i
ins n x (a:i) = a:(ins (n - 1) x i)

-- find the first plural on a stack (if there is one)
first_pl :: Stack -> Maybe [Ent]
first_pl []            = Nothing
first_pl ((Plur i):is) = Just i
first_pl ((Atom i):is) = first_pl is

-- return the first plural on a stack; if there isn't one, then return the
--   first two atoms as if they were a plural
get_pl :: Stack -> [Ent]
get_pl is | isNothing (first_pl is)     = [is!!0, is!!1]
          | otherwise                   = fromJust (first_pl is)


-- Type shenanigans and dynamics
-- ======================================== 

-- Argument Raising operator: arg_raise
type family Lift (a :: *)
type instance Lift (a -> b) = Lift a -> b
type instance Lift Ent      = GQ

class Lifts a where
  arg_raise :: a -> Lift a

instance Lifts Ent where
  arg_raise x = \p i k -> p x (x:i) k
instance Lifts (Ent -> Prop) where
  arg_raise p = \g i k -> g p i k
instance Lifts (Ent -> Ent -> Prop) where
  arg_raise r = \g y i k -> g (\x -> r x y) i k

-- continuizing operator: dynam
type family Dynamic (a :: *)
type instance Dynamic (a -> b) = Dynamic a -> Dynamic b
type instance Dynamic Ent      = Ent
type instance Dynamic Bool     = Stack -> (Stack -> Bool) -> Bool

class Dynamics a where
  dynam :: (Stack -> a) -> Dynamic a

instance Dynamics Bool where
  dynam f = \i k -> f i && k i
instance (Dynamics a) => Dynamics (Ent -> a) where
  dynam f = \x -> dynam (\e -> (f e) x)


-- Interpretating English
-- ======================================== 

-- Connectives
-- ---------------------------------------- 

-- dynamic conjunction (sentential "and")
conj :: Prop -> Prop -> Prop --after de Groote p. 3, (3) 
conj left right i k = left i (\i' -> right i' k)

-- sum-forming "and", as in "John and Bill went home"
oplus :: [Ent] -> GQ
oplus xs = arg_raise (join xs)

-- static VP negation
un :: Prop -> Prop 
un s i k = not (s i k) && (k i)

-- partitive "of"; returns the set of individuals at the bottom of the GQ
--   lattice (returns the empty set if the GQ is not an ultrafilter)
of_p :: GQ -> Ent -> Prop
of_p g = dynam $ \_ y -> y `elem` foldr intersect atoms (characteristic_sets g)


-- Nouns
-- ---------------------------------------- 

-- names
alex', bill', chris', dubliners' :: Ent
[alex', bill', chris', dubliners'] = [a, b, c, d]

--continuized names, pronouns
alex, bill, chris :: GQ
[alex, bill, chris] = map arg_raise [alex', bill', chris']

dubliners :: Ent
dubliners = dubliners'

he, they :: Int -> GQ
he n p i k = p (i!!n) i k
they n p i k = p (i!!n) i k

-- basic nominals
student', book' :: Ent -> Bool
student' y = elem y [a,b,c]
book' y    = elem y [d,e,f]

-- continuized nominals
student, book :: Ent -> Prop
[student, book] = map (dynam . (\x -> \_ -> x)) [student', book']

-- Verbs
-- ---------------------------------------- 

-- basic intransitives
laugh', smoke' :: Ent -> Bool
laugh' y   = elem y [a,b,c]
smoke' y   = elem y [a]

-- continuized, asterisk-ized intransitives
laugh, smoke :: Ent -> Prop
[laugh, smoke] = map (ast . dynam . (\x -> \_ -> x)) [laugh', smoke']

-- basic transitives
want', want2', receive' :: Ent -> Ent -> Bool

want' x s@(Atom y) = elem (x,s) [(d,a), (d,b), (d,c)]
want' x   (Plur y) = and (map (\z -> elem (x,z) [(d,a), (d,b), (d,c)]) y)

want2' x s@(Atom y) = elem (x,s) [(d,a), (d,b), (d,c), (e,a), (e,b), (e,c)]
want2' x   (Plur y) = and (map (\z -> elem (x,z) [(d,a), (d,b), (d,c), (e,a),
  (e,b), (e,c)]) y)

receive' x s@(Atom y) = elem (x,s) [(d,a), (e,b), (f,c)]
receive' x   (Plur y) = and (map (\z -> elem (x,z) [(d,a), (e,b), (f,c)]) y)

-- continuized transitives
want, want2, receive :: Ent -> Ent -> Prop
[want, want2, receive] = map (dynam . (\x -> \_ -> x)) [want', want2', receive']

-- Determiners
-- ---------------------------------------- 

every :: (Ent -> Prop) -> GQ
every res scope i k = 
  and [not (res x i (\i' -> not (scope x (x:(top res):i') trivial)))
        | x <- domain] && (k i)

some :: (Ent -> Prop) -> GQ
some res scope i k =
  or [res x i (\i' -> scope x (x:i') k) | x <- domain]

no :: (Ent -> Prop) -> GQ
no res scope i k =
  and [not (res x i (\i' -> scope x (x:i') trivial)) | x <- domain] && (k i)

-- "the" is like "every" except that it doesn't throw anything other than what
--   it is quantifying over onto the stack; uniqueness presuppositions absent
--   here
the :: (Ent -> Prop) -> GQ
the res = arg_raise (top res)

-- Adjectives
-- ---------------------------------------- 

same, different :: (Adj -> GQ) -> (Ent -> Ent -> Prop) -> Ent -> Prop
same dp verb x i k =
  let fn s@(Atom x) = elem s
      fn   (Plur x) = (\w -> all (\r -> elem r w) x) in
  and [eval (dp (\g -> \y -> conj (verb y u) (g y)) (\z -> verb z v))
        | u <- atoms, v <- (delete u domain),
          elem u (get_pl i), fn v (get_pl i)] && (k i)

different dp verb x i k =
  let fn s@(Atom x) = elem s
      fn   (Plur x) = (\w -> all (\r -> elem r w) x) in
  and [eval (dp (\g -> \y -> conj (verb y u) (g y)) (\z -> un (verb z v)))
        | u <- atoms, v <- (filter (\(Plur x) -> notElem u x) plurs) ++ (delete u atoms),
          elem u (get_pl i), fn v (get_pl i)] && (k i)

