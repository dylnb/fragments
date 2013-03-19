{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.Monad.State
import Control.Monad.Cont
import Data.List
--import Debug.Hood.Observe
import Debug.Trace

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

lap :: Dcont a -> Dcont (a -> b) -> Dcont b
-- lap = flip ap (watch out: side effects still flow from function to arg)
lap m h = do
  x <- m
  f <- h
  return $ f x

rap :: Dcont (a -> b) -> Dcont a -> Dcont b
rap = ap 

eval :: Dstate a -> [(a,Stack)]
eval = (`runStateT` [])

up :: E -> E
up m = cont $ \k ->
  --runCont m (\x -> StateT $ \s -> runStateT (k x) (s++[x]))
  runCont m (\x -> StateT $ \s -> runStateT (k x) (x:s))

up2 :: E -> E
up2 m = m >>= (\x -> cont $ \k -> do {modify (x:); k x})
   
univ :: Stack
univ = [1..10]

one, two, three, four, five, six, seven, eight, nine, ten :: E
[one, two, three, four, five, six, seven, eight, nine, ten] = map return univ

he :: Int -> E
he n = cont $ \k -> do
  s <- get
  k (trace ("he-stack: " ++ show (length s)) s!!n)

leq3, leq5, geq8, triv :: ET
[leq3, leq5, geq8] = map return [(<= 3), (<= 5), (>= 8)]
triv = return (const True)

eq, lt, gt :: EET
[eq, lt, gt] = map return [(==), (>), (<)]


cf :: Int -> (Int -> Bool) -> Int
cf n p
    | n < length plist = plist!!n
    | otherwise        = -1
  where plist = characteristic p

restrict :: (((Int -> Bool) -> Int) -> Dstate Bool) -> [(Int -> Bool) -> Int]
restrict k =
  filter (\f -> last (head (execStateT (k f) [])) > 0) cfs
  where cfs = map (cf . subtract 1) univ

some :: ETE
some = cont $ \k -> do
  f <- lift (restrict k)
  k f

compress :: [(Bool,Stack)] -> Stack
compress [] = []
compress ls = map snd $ foldl1 intersect enum_stacks
  where enum_stacks = [(zip [0..] . snd) l | l <- ls]

-- there are quirks with multiple quantifiers that are very likely due to "restrict";
-- there is an index error if nothing in the "nuclear scope" is upped;
-- and the stack explodes if the "every" DP is not itself upped;
-- and forget about donkey binding.
everyD :: ETE
everyD = cont $ \k -> do 
  let ps = [k f | f <- restrict k]
  foldl1 (liftM2 (&&)) (trace ("everyD: " ++ show (length ps)) ps)

everyS :: ETE
everyS = cont $ \k -> StateT $ \s ->
  let ls = runStateT (runCont everyD k) s in
  [(any fst ls, compress ls)]
  

--different :: ETET
--different = cont $ \k -> do

