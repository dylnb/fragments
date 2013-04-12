{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.Monad.State
import Control.Monad.Cont
import Control.Applicative
import Data.List
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
type ETE = Dcont ((Int -> Bool) -> Int)
type ETET = Dcont ((Int -> Bool) -> Int -> Bool)

class Lowerable a where
  lower :: Dcont a -> Dstate a
instance Lowerable Bool where
  lower m = runCont m return
instance Lowerable Int where
  lower m = runCont m (\x -> unit' [x] True) >>= (\_ -> pop)

characteristic :: (Int -> Bool) -> Stack
characteristic p = filter p univ

pop :: Dstate Int
--pop = state $ \s -> let (x:xs) = reverse s in (x, reverse xs)
pop = state $ \(x:xs) -> (x, xs)

unit' :: Stack -> a -> Dstate a
--unit' s' x = state $ \s -> (x, s++s')
unit' s' x = state $ \s -> (x, s'++s)

ret :: a -> Dcont a
ret = return

lap :: Dcont a -> Dcont (a -> b) -> Dcont b
-- lap = flip ap (watch out: side effects still flow from function to arg)
lap m h = do
  x <- m
  f <- h
  return $ f x

llap :: Dcont (Dcont a) -> Dcont (Dcont (a -> b)) -> Dcont (Dcont b)
llap m h = do
 x <- m
 f <- h
 return $ lap x f

rap :: Dcont (a -> b) -> Dcont a -> Dcont b
rap = ap 

rrap :: Dcont (Dcont (a -> b)) -> Dcont (Dcont a) -> Dcont (Dcont b)
rrap h m = do
  f <- h
  x <- m
  return $ rap f x

rreturn :: Dcont a -> Dcont (Dcont a)
rreturn f = lap f (return return)

eval :: Dstate a -> [(a,Stack)]
eval = (`runStateT` [])

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

minus :: Stack -> Stack -> Stack
s1 `minus` s2 = take ((length s1) - (length s2)) s1

up :: E -> E
up m = cont $ \k ->
  --runCont m (\x -> StateT $ \s -> runStateT (k x) (s++[x]))
  runCont m (\x -> StateT $ \s -> runStateT (k x) (x:s))

   
univ :: Stack
univ = [1..10]

one, two, three, four, five, six, seven, eight, nine, ten :: E
[one, two, three, four, five, six, seven, eight, nine, ten] = map return univ

he :: Int -> E
he n = cont $ \k -> do
  s <- get
  --k (trace ("he-stack: " ++ show (length s)) s!!n)
  k (s!!n)

leq3, leq5, geq8, triv :: ET
[leq3, leq5, geq8] = map return [(<= 3), (<= 5), (>= 8)]
triv = return (const True)

eq, lt, gt :: EET
[eq, lt, gt] = map return [(==), (>), (<)]


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

compress :: [(Bool,Stack)] -> Stack
compress [] = []
compress ls = map snd $ foldl1 intersect enum_stacks
  where enum_stacks = [(zip [(0::Int)..] . snd) l | l <- ls]

someD :: ET -> E
someD p  = cont $ \k -> do
  x <- lift univ
  b <- check p x 
  if b then k x else mzero

trialsome :: ET -> E
trialsome p = cont $ \k -> StateT $ \s ->
  let xs = filter (any fst . eval . check p) univ in
  let ps = map (\x -> runStateT (k x) s) xs in
  concat ps

-- almost right, but doesn't pass referents from restr to scope 
simpleeveryD :: ET -> E
simpleeveryD p = cont $ \k -> do
  let xs = filter (any fst . eval . check p) univ
  let ps = map k xs
  foldl1 (liftM2 (&&)) ps


-- xs here is interesting. it's a sort of
-- stateful characterisitc set of p. we could go a step farther, and reduce p
-- to a single Dstate Int, by mapping a state over the list and concatenating
-- the results:
--   p' = foldl1 (mplus) xs
-- This could then be directly injected into the continuation (p' >>= k), but
-- there would be no way to tell where the contributions of one individual
-- ended and another began 
everyD :: ET -> E
everyD p = cont $ \k -> do
  let xs = filter (not . null . eval) $
           map (bottle <*> check p) univ
           --map ((>>) <$> mfilter id . check p <*> return) univ
  let ps = map (>>= k) xs
  foldl1 (liftM2 (&&)) ps
  where bottle x t = mfilter id t >> return x
-- "bottle" takes an int x and a bool-state t, and replaces the (True, s') pairs
-- in t with (x, s') pairs, and discards the rest; intuitively, it filters t, 
-- and then "bottles" x up with the various result states:
--   bottle 3 (\s -> [(T,7:s), (F,8:s), (T,9:s)]) == \s -> [(3,7:s), (3,9:s)]
-- the only problem is that if x completely fails p, "bottle" returns the
-- empty individual (\s -> []), which has to swept out later. the
-- commented-out line is equivalent

trialeveryD :: ET -> E
trialeveryD p = cont $ \k -> StateT $ \s ->
  let xs = filter (not . null . eval) $
           map ((>>) <$> mfilter id . check p <*> return) univ in
  let ps = map (\x -> runStateT (x >>= k) s) xs in
  foldl1 dynand ps
  where dynand l l' = [(x && x', t ++ t') | (x,t) <- l, (x',t') <- l']
-- matches the simple formal definition given in the paper, but doesn't work
-- for 'different', because all the states are evaluated before being crossed
-- and conjoined

different :: ETET
different = cont $ \k -> do {s <- get; k (\p x -> p x && x `notElem` s)}

-- ==============================


-- TEST ZONE
-- ==============================

--pushS :: Int -> Dstate Int
--pushS n = withStateT (n:)
--
--pushC :: Int -> Dcont Int
--pushC n = cont $ \k -> pushS n

up2 :: E -> E
up2 m = m >>= (\x -> cont $ \k -> do {modify (x:); k x})

--up3 :: E -> E
--up3 m = do {x <- m; pushC x}

longest :: ETET
longest = cont $ \k -> do {s <- get; k (\p x -> p x && x > maximum s)}

w, w',w'' :: Dstate Int
w   = StateT $ \s -> [(3,7:s),(3,8:s),(3,9:s)]
w'  = StateT $ \s -> [(4,9:s),(4,8:s),(4,7:s)]
w'' = StateT $ \s -> [(1,s),(2,s),(3,s)]


c :: Int -> Dstate Bool
c x = lower $ lap (up $ someD leq3) (rap eq (up $ return x))
