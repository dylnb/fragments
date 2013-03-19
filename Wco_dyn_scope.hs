-- Haskell port of Charlow's wco_dyn.ml using StateT transformer
-- with Lists to model nondeterminism within state

module Wco_dyn_scope where

import Control.Monad.State
import Data.List.Split


type Stack = [Int]
type DState a = StateT Stack [] a
type E = DState Int
  -- Stack -> [(Int, Stack)]
type T = DState Bool
  -- Stack -> [(Bool, Stack)]
type GQ = (E -> T) -> T


{- Auxiliary functions (not used)

clean_up :: [(Bool,Stack)] -> [(Bool,Stack)]
clean_up xs = filter fst xs

pop :: Int -> Stack -> Stack
pop x []   = [x]
pop x (i:is) | x == i     = is++[x]
             | otherwise  = i:(pop x is)

firstToLast :: Stack -> Stack
firstToLast []     = []
firstToLast (x:xs) = xs++[x]

-}


-- Auxiliary functions (used)

-- backwards function application
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- returns characteristic function of a set
charF :: [Int] -> E -> T
charF xs = liftM (`elem` xs)

-- a sort of existential closure of stacks
truthy :: [(Bool, a)] -> Bool
truthy = (or . map fst)

-- "natural" function for negation
compress :: [(Bool, Stack)] -> Stack
compress []     = []
compress (x:xs) = [ i | i <- foldr hashOut s ss, i /= -1 ]
  where (s:ss) = map snd (x:xs)

-- just guessing here about how to handle stacks of different sizes,
-- which apparently comes up for inverse-linking out of DP
hashOut :: Stack -> Stack -> Stack
hashOut [] []     = []
hashOut _ [] = [-1]
hashOut [] _ = [-1]
hashOut (x:xs) (y:ys) | x == y    = x : (hashOut xs ys)
                      | otherwise = -1 : (hashOut xs ys)

-- order-sensitive stack differential: (except for empty lists)
-- s2 - s1 returns s2 unless s1 is a proper final sublist
-- of s2, in which case it returns the non-s1 initial subpart of s2
minus :: Stack -> Stack -> Stack
s2 `minus` s1
    | s1 == []   = s2
    | s2 == []   = []
    | s1 == s2   = []
    | otherwise  = (xs!!0)
  where xs = split (startsWith s1) s2

-- runs a proposition against an empty state
eval :: DState a -> [(a,Stack)]
eval m = runStateT m []

-- generalized return function, which adds s' to the state
unit' :: Stack -> a -> DState a
unit' s' x = StateT $ \s -> [(x, s'++s)]

-- "unit" is the special case of "unit' []"
unit :: a -> DState a
unit = return

-- "lift" is a predefined function in MonadTrans class that 
-- converts the value(s) inside a monad (in this case a list)
-- to default transformers (in this case nondeterministic 
-- stateful computations: Stack -> [(a, Stack)]). To avoid
-- confusion with later type-shifting rules, I'm renaming
-- it "mapunit".
mapunit :: [a] -> DState a
mapunit = lift
-- mapunit' is just like "lift", except that it returns  
-- computations in which x has been added to the resulting
-- state
mapunit' :: Stack -> E
mapunit' c = StateT $ \s -> c >>= (\x -> return (x, x:s))



-- The model and the language


-- domain

univ :: [Int]
univ = [1..11]


-- predicates

thing :: E -> T
thing = liftM (`elem` [1..10])

evenNum :: E -> T
evenNum = liftM even

over :: Int -> E -> T
over n = liftM (> n)

under :: Int -> E -> T
under n = liftM (< n)

next :: E -> E
next m = do
  x <- m
  unit' [x+1] (x + 1)


-- in the monadic DState environement, it takes 
-- work to keep things static from left to right;
-- compare static "equals" to dynamic "equals" below

{- dynamic "equals"
equals :: E -> E -> T
equals r l = do
  x <- l
  y <- r
  unit (x == y)
-}

-- in fact, dynamic "equals" is ALMOST as simple as
-- equals r l = liftM2 (==),
-- except that the side-effects here would track 
-- argument structure instead of linear order

equals, gthan, lthan, divides :: E -> E -> T
equals r l = StateT $ \s ->
  let [(x,s1)] = runStateT l s
      [(y,s2)] = runStateT r s in
  [(x==y, (s2 `minus` s) ++ (s1 `minus` s) ++ s)] 

{- still static, but using the monad
equals r l = do
  s <- get
  x <- l
  s' <- get
  put s
  y <- r
  s'' <- get
  put s
  unit' ((s'' `minus` s) ++ (s' `minus` s)) (x==y)
-}

gthan r l = StateT $ \s ->
  let [(x,s1)] = runStateT l s
      [(y,s2)] = runStateT r s in
  [(x > y, (s2 `minus` s) ++ (s1 `minus` s) ++ s)] 

lthan r l = StateT $ \s ->
  let [(x,s1)] = runStateT l s
      [(y,s2)] = runStateT r s in
  [(x < y, (s2 `minus` s) ++ (s1 `minus` s) ++ s)] 

divides r l = StateT $ \s ->
  let [(x,s1)] = runStateT l s
      [(y,s2)] = runStateT r s in
  [(x < y && y `mod` x == 0, (s2 `minus` s) ++ (s1 `minus` s) ++ s)] 


-- names update the stack, pronouns don't

john, bill, johnORbill:: E
john = unit' [1] 1

bill = unit' [9] 9
  
-- DState monad allows for indeterminacy at 
-- the individual level to percolate up to 
-- indeterminacy at the sentence level (bumford)
johnORbill = mapunit' [1,9]

he, he1, he2, he3 :: E
he = do
  s <- get
  unit (head s)

he1 = do
  s <- get
  unit (s!!1)

he2 = do
  s <- get
  unit (s!!2)

he3 = do
  s <- get
  unit (s!!3)


-- connectives


-- dynamic conjunction; so easy with monads
-- again, probably usually OK to use "liftM2 (&&)",
-- but just in case...
dyn_conj :: T -> T -> T
l `dyn_conj` r = do
  p <- l
  q <- r
  unit ((p && q) || (q && p))

-- static conjunction; painful
-- have to double the conjunction to avoid short-circuiting
-- before exceptions get thrown!!!
conj :: T -> T -> T
l `conj` r = StateT $ \s ->
  let ps = runStateT l s
      qs = runStateT r s in
  [ ((p && q) || (q && p), (s2 `minus` s) ++ (s1 `minus` s) ++ s)
    | (p,s1) <- ps, (q,s2) <- qs ]
 
{- static in the monad
conj :: T -> T -> T
l `conj` r = do
  s <- get
  p <- l
  s' <- get
  put s
  q <- r
  s'' <- get
  put s
  unit' ((s'' `minus` s) ++ (s' `minus` s)) ((p && q) || (q && p))
-}

disj :: T -> T -> T
l `disj` r = StateT $ \s -> runStateT l s ++ runStateT r s

dyn_disj :: T -> T -> T
l `dyn_disj` r = do
  p <- l
  q <- r
  unit ((p || q) && (q || p))

neg :: T -> T
neg p = StateT $ \s -> 
  let xs = runStateT p s in
  [(not $ truthy xs, compress xs)]



-- determiners

-- option to return information about every member 
-- of the restrictor, or just the members of the 
-- restrictor that also satisfy the scope
some, every :: (E -> T) -> (E -> T) -> T
some n c = do
  s  <- get
  x  <- mapunit [1..10]
  p  <- n (unit x)
  s' <- get
  q  <- c (unit' (x : (s' `minus` s)) x)
  if p then unit q else mapunit []
  --if (p && q) then unit True else mapunit []

every p c = neg (some p (\x -> neg (c x)))


-- generalized quantifiers

eo, so, he' :: (E -> T) -> T
eo = every thing

so = some thing

he' = lift1 he


-- gaps, prepositions, wh-words

gap :: (E -> T) -> E -> T
gap = \c l -> c l

divisor_of :: E -> (E -> T) -> E -> T
divisor_of y q x = (q x) `conj` (divides y x)

who_rc :: (E -> T) -> (E -> T) -> E -> T
who_rc p q x = (q x) `conj` (p x)

which :: (E -> T) -> (E -> T) -> ((E -> T) -> E) -> T
which p q f = q (f p)


-- conditionals

impl :: ((T -> T) -> T) -> ((T -> T) -> T) -> T
impl g c = neg (g (\p -> p `conj` neg (c id)))



-- scope

lift1 x = \c -> c x

lift2 f c = f (\x -> c (\k -> k x))

bind1 g c = do
  s <- get
  g (\l -> do
    x  <- l
    s' <- get
    c (unit' (s' `minus` s) x))

{- equivalent, verbose definition on "bind1"
bind1 g = \c -> StateT $ \s ->
  runStateT (g (\l -> l >>= (\x -> StateT $ \s' ->
    runStateT (c (StateT $ \s'' -> [(x, (s' `minus` s) ++ s'')])) s'))) s
-}

-- "lower1" lowers T-type things
lower1 g = do
  s <- get
  g (\x -> do { put s; x })

--"lower1'" lowers E->T-type things
lower1' g y = do
  s <- get
  g (\x -> do { put s; x }) y

lower2 g c = g (\h -> c (lower1 h))

lower3 g c = do
  s <- get
  g (\h -> do { put s; h c} )

slash left right c   = left (\l -> right (\r -> c (l r)))

bslash left right c  = left (\l -> right (\r -> c (r l)))

slash2 left right c  = left (\l -> right (\r -> c (\k -> slash l r k)))

bslash2 left right c = left (\l -> right (\r -> c (\k -> bslash l r k)))


-- some examples

-- inverse scope
-- eval $ lower1 $ lower2 $ bslash2 (lift1 so) $ slash2 (lift1 $ lift1 equals) (lift2 eo)

-- basic binding
-- eval $ lower1 $ bslash (bind1 so) $ slash (lift1 lthan) $ bslash (bind1 $ lift1 he) (lift1 next)

-- crossover
-- eval $ lower1 $ lower2 $ bslash2 (lift1 $ bind1 $ lift1 he) $ slash2 (lift1 $ lift1 equals) (lift2 $ bind1 eo)

-- basic RC
-- eval $ lower1 $ bslash (some $ evenNum |> who_rc $ lower1' $ bslash (lift1 $ unit 3) $ slash (lift1 $ lthan) gap) (lift1 $ over 8)

-- binding out of RC
-- eval $ lower1 $ bslash (bind1 $ every $ thing |> who_rc $ lower1' $ bslash gap $ slash (lift1 divides) $ some evenNum) $ slash (lift1 lthan) (bind1 $ lift1 he1)

-- binding out of antecedents
-- eval $ lower1 $ slash (impl $ bind1 $ lift1 $ lower1 $ bslash so (lift1 $ over 8)) (bind1 $ lift1 $ over 5 he)

--binding failure out of antecedents
-- eval $ lower1 $ slash (impl $ bind1 $ lift1 $ lower1 $ bslash eo (lift1 $ over 8)) (bind1 $ lift1 $ over 5 he)

-- binding across sentences
-- eval $ lower1 $ bslash (bind1 $ lift1 $ lower1 $ bslash so (lift1 $ over 5)) $ slash (lift1 conj) (bind1 $ lift1 $ over 8 he)

-- binding failure across sentences
-- eval $ lower1 $ bslash (bind1 $ lift1 $ lower1 $ bslash eo (lift1 $ over 5)) $ slash (lift1 conj) (bind1 $ lift1 $ over 8 he)

-- binding out of DP (inverse linking)
-- eval $ lower1 $ bslash (bind1 $ lower3 $ slash (lift1 some) $ bslash (lift1 thing) $ slash (lift1 divisor_of) (every $ over 5)) $ slash (lift1 lthan) (bind1 $ lift1 he1)
