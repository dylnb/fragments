{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- STACK TYPE MUST BE GENERALIZED TO HANDLE FUNCTIONAL DREFS!!!
-- need a union type for Ent (Atom Int | Func Stack), but this requires
-- pattern matching in all of the definitions below :(

import Control.Monad.State
import Control.Monad.Cont
import Control.Applicative
import Data.List
import Data.List.Split (chunksOf, splitPlaces)
import Data.Ord
--import Data.Maybe
--import Debug.Hood.Observe
--import Debug.Trace

type Stack = [Int]
type Dstate r = StateT Stack [] r
type Dcont a = Cont (Dstate Bool) a

type E = Dcont Int
type T = Dcont Bool
type ET = Dcont (Int -> Bool)
type EET = Dcont (Int -> Int -> Bool)
type EEET = Dcont (Int -> Int -> Int -> Bool)
type ETE = Dcont ((Int -> Bool) -> Int)
type ETET = Dcont ((Int -> Bool) -> Int -> Bool)



-- AUXILIARY FUNCTIONS
-- ===================

-- Characteristic set of a property
characteristic :: (Int -> Bool) -> Stack
characteristic p = filter p univ

-- Stack difference
minus :: Stack -> Stack -> Stack
s1 `minus` s2 = take ((length s1) - (length s2)) s1

-- Normal pop operation for stacks
pop :: Dstate Int
pop = state $ \s -> let (x:xs) = reverse s in (x, reverse xs)
--pop = state $ \(x:xs) -> (x, xs)

-- Dynamically-charged State.List unit function
unit' :: Stack -> a -> Dstate a
unit' s' x = state $ \s -> (x, s++s')
--unit' s' x = state $ \s -> (x, s'++s)

-- Runs a State.List value against the empty state
eval :: Dstate a -> [(a,Stack)]
eval = (`runStateT` [])


-- MONADIC OPERATIONS
-- ==================

-- First-Order Continuized Application

ret :: a -> Dcont a
ret = return

lap :: Dcont a -> Dcont (a -> b) -> Dcont b
-- lap = flip ap (watch out: side effects still flow from function to arg)
lap m h = do
  x <- m
  f <- h
  return $ f x

-- First-Order Unit Function
rap :: Dcont (a -> b) -> Dcont a -> Dcont b
rap = ap 

-- First-Order Lower Function
-- (overloaded for continuized individuals to make printing easier)
class Lowerable a where
  lower :: Dcont a -> Dstate a
instance Lowerable Bool where
  lower m = runCont m return
instance Lowerable Int where
  lower m = runCont m (\x -> unit' [x] True) >>= (\_ -> pop)


-- Second-Order Continuized Application
llap :: Dcont (Dcont a) -> Dcont (Dcont (a -> b)) -> Dcont (Dcont b)
llap m h = do
 x <- m
 f <- h
 return $ lap x f

rrap :: Dcont (Dcont (a -> b)) -> Dcont (Dcont a) -> Dcont (Dcont b)
rrap h m = do
  f <- h
  x <- m
  return $ rap f x

-- Second-Order Unit Function
rreturn :: Dcont a -> Dcont (Dcont a)
rreturn f = lap f (return return)

-- Second-Order Lower Function
lower2 :: Dcont (Dcont a) -> Dcont a
lower2 outer = cont $ \k -> StateT $ \s -> 
  runStateT
    ( (runCont outer)
      (\m -> StateT $ \s' ->
        runStateT
          (runCont m
                   (\a -> StateT $ \s'' ->
                     runStateT (k a) (s'' ++ (s' `minus` s))
                   )
          ) s
      )
    ) s


-- SIMPLE BINDING
-- ==============

up :: E -> E
up m = cont $ \k ->
  runCont m (\x -> StateT $ \s -> runStateT (k x) (s++[x]))
  --runCont m (\x -> StateT $ \s -> runStateT (k x) (x:s))


-- THE MODEL AND THE LANGUAGE
-- ==========================
   
univ :: Stack
univ = [1..10]

-- Proper Names
one, two, three, four, five, six, seven, eight, nine, ten :: E
[one, two, three, four, five, six, seven, eight, nine, ten] = map return univ

-- Pronouns
he :: Int -> E
he n = cont $ \k -> do
  s <- get
  k (s!!n)

-- One-Place Predicates
leq3, bt46, bt24, geq8, triv :: ET
[leq3, bt46, bt24, geq8] =
  map return [(<= 3), (`elem` [4,5,6]), (`elem` [2,3,4]), (>= 8)]
triv = return (const True)

-- Two-Place Predicates
eq, lt, gt :: EET
[eq, lt, gt] = map return [(==), (>), (<)]

-- Three-Place Predicates
gcd' :: EEET
gcd' = return (\n m g -> gcd n m == g)

-- CHOICE FUNCTIONS (broken)
-- ===============================

cf :: Int -> (Int -> Bool) -> Int
cf n p
    | n < length plist = plist!!n
    | otherwise        = -1
  where plist = characteristic p

restrict :: (((Int -> Bool) -> Int) -> Dstate Bool) -> [(Int -> Bool) -> Int]
restrict k =
  filter (\f -> last (head (execStateT (k f) [])) > 0) cfs
  where cfs = map (cf . subtract 1) univ

choicesome :: ETE
choicesome = cont $ \k -> do
  f <- lift (restrict k)
  k f

safecf :: Int -> (Int -> Bool) -> Int
safecf n p
    | n < length plist = plist!!n
    | otherwise        = maximum plist
  where plist = characteristic p

safesome :: ETE
safesome = cont $ \k -> do
  f <- lift $ map (safecf . subtract 1) univ
  k f

-- there are quirks with multiple quantifiers that are very likely due to "restrict";
-- there is an index error if nothing in the "nuclear scope" is upped;
-- and the stack explodes if the "every" DP is not itself upped;
-- and forget about donkey binding.
choiceeveryD :: ETE
choiceeveryD = cont $ \k -> do 
  let ps = [k f | f <- restrict k]
  --foldl1 (liftM2 (&&)) (trace ("everyD: " ++ show (length ps)) ps)
  foldl1 (liftM2 (&&)) ps

choiceeveryS :: ETE
choiceeveryS = cont $ \k -> StateT $ \s ->
  let ls = runStateT (runCont choiceeveryD k) s in
  [(any fst ls, compress ls)]

safechoiceeveryD :: ETE
safechoiceeveryD = cont $ \k -> do
  let ps = [k f | f <- map (safecf . subtract 1) univ]
  foldl1 (liftM2 (&&)) ps

safechoiceeveryS :: ETE
safechoiceeveryS = cont $ \k -> StateT $ \s ->
  let ls = runStateT (runCont safechoiceeveryD k) s in
  [(any fst ls, compress ls)]

-- ==========================


-- ET -> E Quantifiers
-- ==========================

-- auxiliary functions for working with restrictors
check :: ET -> Int -> Dstate Bool
check p = lower . rap p . return

someD :: ET -> E
someD p  = cont $ \k -> do
  x <- lift univ
  b <- check p x 
  if b then k x else mzero

altsomeD :: ET -> E
altsomeD p = cont $ \k -> do
  let xs = map ((>>) <$> mfilter id . check p <*> return) univ
  (foldl1 mplus xs) >>= k
  
-- almost right, but doesn't pass referents from restr to scope 
simpleeveryD :: ET -> E
simpleeveryD p = cont $ \k -> do
  let xs = filter (any fst . eval . check p) univ
  let ps = map k xs
  foldl1 (liftM2 (&&)) ps

-- internally dynamic universal
everyD :: ET -> E
everyD p = cont $ \k -> do
  let xs = filter (not . null . eval) $
           map (bottle <*> check p) univ
           --map ((>>) <$> mfilter id . check p <*> return) univ
  let ps = map (>>= k) xs
  foldl1 (liftM2 (&&)) ps
  where bottle x t = mfilter id t >> return x
-- xs here is interesting. it's a sort of
-- stateful characteristic set of p. we could go a step farther, and reduce p
-- to a single Dstate Int, by mapping a state over the list and concatenating
-- the results:
--   p' = foldl1 mplus xs
-- This could then be directly injected into the continuation (p' >>= k), but
-- there would be no way to tell where the contributions of one individual, so
-- it would only be useful for "some"
-- ended and another began 
--
--
-- "bottle" takes an int x and a bool-state t, and replaces the (True, s') pairs
-- in t with (x, s') pairs, and discards the rest; intuitively, it filters t, 
-- and then "bottles" x up with the various result states:
--   bottle 3 (\s -> [(T,7:s), (F,8:s), (T,9:s)]) == \s -> [(3,7:s), (3,9:s)]
-- the only problem is that if x completely fails p, "bottle" returns the
-- empty individual (\s -> []), which has to swept out later. the
-- commented-out line is equivalent



-- ADJECTIVES SENSITIVE TO ACCUMULATION
-- ===================================
different :: ETET
different = cont $ \k -> do {s <- get; k (\p x -> p x && x `notElem` s)}

longer :: ETET
longer = cont $ \k -> do {s <- get; k (\p x -> p x && x > maximum s)}



-- TEST ZONE AND TEST TERMS
-- ========================

-- these entries are not internally dynamic; every iteration of the loop is
-- evaluated at the matrix state
trialsome :: ET -> E
trialsome p = cont $ \k -> StateT $ \s ->
  let xs = filter (any fst . eval . check p) univ in
  let ps = map (\x -> runStateT (k x) s) xs in
  concat ps

trialeveryD :: ET -> E
trialeveryD p = cont $ \k -> StateT $ \s ->
  let xs = filter (not . null . eval) $
           map ((>>) <$> mfilter id . check p <*> return) univ in
  let ps = map (\x -> runStateT (x >>= k) s) xs in
  foldl1 dynand ps
  where dynand l l' = [(x && x', t ++ t') | (x,t) <- l, (x',t') <- l']


--pushS :: Int -> Dstate Int
--pushS n = withStateT (n:)
--
--pushC :: Int -> Dcont Int
--pushC n = cont $ \k -> pushS n

up2 :: E -> E
up2 m = m >>= (\x -> cont $ \k -> do {modify (x:); k x})

--up3 :: E -> E
--up3 m = do {x <- m; pushC x}

w, w',w'' :: Dstate Int
w   = StateT $ \s -> [(3,7:s),(3,8:s),(3,9:s)]
w'  = StateT $ \s -> [(4,9:s),(4,8:s),(4,7:s)]
w'' = StateT $ \s -> [(1,s),(2,s),(3,s)]

trivstate, emptystate :: Dstate Bool
trivstate  = StateT $ \s -> [(True,s)]
emptystate = StateT $ \s -> []

c :: Int -> Dstate Bool
c x = lower $ lap (up $ someD leq3) (rap eq (up $ return x))

j :: Dstate (Dstate Int) -> Dstate Int
j = join

-- Machinery for making functional witnesses. Unfortunately, it can't be
-- rolled into the rest of the semantics until the Stack and Ent types are
-- genrealized

diffs :: Stack -> Stack
diffs s = [(s!!n) - (s!!(n-1)) | n <- [1..length s - 1]]

findAnchors :: [(Bool,Stack)] -> Stack
findAnchors alts = map fst $ foldl1 intersect enumStacks
  where enumStacks = [(zip [0..] . snd) alt | alt <- alts]

compress :: [(Bool,Stack)] -> Stack
compress alts = map snd $ foldl1 intersect enumStacks
  where enumStacks = [(zip [0..] . snd) alt | alt <- alts]

makeFuncs :: [Int] -> Stack -> [(Int,Stack)]
makeFuncs indices hist =
  foldl (\funcs is -> (last is, (reverse . init) is) : funcs) [] splits
  where splits = splitPlaces (head indices + 1 : diffs indices) hist

functionalize :: [(Bool,Stack)] -> [(Bool,[(Int,Stack)])]
functionalize alts = map (\(b,hist) -> (b, makeFuncs inds hist)) alts
  where inds = findAnchors alts

-- generalizes "findAnchors" to patterns generated by multiple universals
-- (probably unnecessary if universals automatically functionalize as soon as
-- they take scope)
findAnchs :: Stack -> [Stack]
findAnchs indices = (maximumBy (comparing length) parts)
  where divisors x = [y | y <- [2..(x `div` 2)], x `mod` y ==0] ++ [x]
        chunks     = [chunksOf n indices | n <- divisors (length indices)]
        parts      = filter ((== 1) . length . nub . map diffs) chunks
    


-- EXAMPLES
-- ========

-- eval $ lower $ rap geq8 nine
