{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.Monad.State
import Control.Monad.Cont
import Data.Monoid
import Control.Applicative
import Data.List
import Data.List.Split (chunksOf)
import qualified Data.Map as M
import Data.Ord
--import Data.Maybe
--import Debug.Hood.Observe
--import Debug.Trace
import Control.Exception (assert)

data Ref = Ent (String,Int) | Func {unfunc :: M.Map Ref Stack} --deriving (Eq,Show)
type Stack = [Ref]
type Dstate r = StateT Stack [] r
type Dcont a = Cont (Dstate Bool) a

type E = Dcont Ref
type T = Dcont Bool
type ET = Dcont (Ref -> Bool)
type EET = Dcont (Ref -> Ref -> Bool)
type EEET = Dcont (Ref -> Ref -> Ref -> Bool)
type ETE = Dcont ((Ref -> Bool) -> Ref)
type ETET = Dcont ((Ref -> Bool) -> Ref -> Bool)


instance Show Ref where
  show (Ent (x,y)) = x ++ show y
  --show (Func _ _) = show "func"
  show _           = show "func"

instance Eq Ref where
  (Ent x) == (Ent y) = x == y
  _ == _ = False

instance Ord Ref where
  compare (Ent (name,tag)) (Ent (name',tag')) = compare tag tag'
  compare _ _ = EQ


-- AUXILIARY FUNCTIONS
-- ===================

-- Characteristic set of a property
characteristic :: (Ref -> Bool) -> Stack
characteristic p = filter p univ

-- Stack difference
-- (this only makes sense if stacks are guaranteed not to diverge)
minus :: Stack -> Stack -> Stack
s1 `minus` s2 = take ((length s1) - (length s2)) s1

-- Normal pop operation for stacks
pop :: Dstate Ref
pop = state $ \s -> let (x:xs) = reverse s in (x, reverse xs)
--pop = state $ \(x:xs) -> (x, xs)

-- Dynamically-charged State.List unit function
unit' :: Stack -> a -> Dstate a
unit' s' x = state $ \s -> (x, s++s')
--unit' s' x = state $ \s -> (x, s'++s)

lift' ::  Monad m => m a -> StateT [a] m a
lift' c = StateT $ \s -> c >>= (\x -> return (x, x:s))

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
instance Lowerable Ref where
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
   
boys, girls, poems, univ :: Stack
boys  = map (\x -> Ent ("b",x)) [1..6]
girls = map (\x -> Ent ("g",x)) [1..6]
poems = map (\x -> Ent ("p",x)) [1..6]
univ = concat [boys, girls, poems]

-- Proper Names
-- one, two, three, four, five, six, seven, eight, nine, ten :: E
-- [one, two, three, four, five, six, seven, eight, nine, ten] = map return univ
boy1, boy2, boy3, boy4, boy5, boy6 :: E
[boy1, boy2, boy3, boy4, boy5, boy6] = map return boys

girl1, girl2, girl3, girl4, girl5, girl6 :: E
[girl1, girl2, girl3, girl4, girl5, girl6] = map return girls

poem1, poem2, poem3, poem4, poem5, poem6 :: E
[poem1, poem2, poem3, poem4, poem5, poem6] = map return poems

-- Pronouns
he :: Int -> E
he n = cont $ \k -> do
  s <- get
  k (s!!n)


-- One-Place Predicates
boy, girl, poem, triv :: ET
boy = let boy' (Ent ("b",_)) = True
          boy' _             = False in
      return boy'

girl = let girl' (Ent ("g",_)) = True
           girl' _             = False in
       return girl'

poem = let poem' (Ent ("p",_)) = True
           poem' _             = False in
       return poem'
 
triv = return (const True)


-- Two-Place Predicates
matches, envies, listensTo :: EET
--[eq, lt, gt] = map return [(==), (>), (<)]

-- people match anyone that their "tags" are equal to:
-- b1 matches g1, g3 matches g3, but g5 doesn't match b4 or g4
matches = let matches' (Ent (_,n)) (Ent (_,m)) = n == m
              matches' _ _                     = False in
          return matches'

-- people envy people of the same gender that they are less than:
-- b1 envies b3, but b3 does not envy b1 nor does he envy g6
envies = let envies' (Ent (x,n)) (Ent (y,m)) = x == y &&
                                               n > m
             envies' _ _                     = False in
          return envies'

-- people listen to people of the opposite gender that they divide evenly:
-- b2 listens to g6, as does b3, but b4 doesn't, and neither does g2
listensTo = let lt' (Ent (x,n)) (Ent (y,m)) = x /= y &&
                                              n `mod` m == 0
                lt' _ _                     = False in
          return lt'

-- Three-Place Predicates
gave :: EEET

-- boys give girls poems in runs:
-- b1 gave g2 p3, and b4 gave g5 p6, but b1 didn't give g3 anything, and he
-- didn't give p4 to anybody
gave = let gave' (Ent (x,n)) (Ent (y,m)) (Ent (z,o)) =
             x == "g" && y == "p" && z == "b" &&
             n == o+1 && m == n+1
           gave' _ _ _                               = False in
       return gave'


-- ET -> ET Adjectives
-- ==========================

short, tall :: ETET
short = let short' p e@(Ent (_,n)) = p e && n <= 3
            short' _ _             = False in
        return short'

tall = let tall' p e@(Ent (_,n)) = p e && n > 3
           tall' _ _             = False in
       return tall'


-- ET -> E Quantifiers
-- ==========================

-- auxiliary functions for working with restrictors
check :: ET -> Ref -> Dstate Bool
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

-- Machinery for making functional witnesses. Unfortunately, it can't be
-- rolled into the rest of the semantics until the Stack and Ent types are
-- genrealized

skipdist :: [Int] -> Int
skipdist s =
  let dl = [(s!!n) - (s!!(n-1)) | n <- [1..length s - 1]] in
  assert ((length . nub) dl == 1) (head dl)

findAnchors :: [(Bool,Stack)] -> [Int]
findAnchors alts = map fst $ foldl1 intersect enumStacks
  where enumStacks = [(zip [0..] . snd) alt | alt <- alts]

compress :: [(Bool,Stack)] -> Stack
compress alts = map snd $ foldl1 intersect enumStacks
  where enumStacks = [(zip [0..] . snd) alt | alt <- alts]

makeFunc :: [Int] -> Stack -> Ref
makeFunc anchs hist = Func $ M.fromList splits
  where splits = map (\(i:is) -> (i,is)) $ chunksOf (skipdist anchs) hist'
        hist'  = drop (head anchs) hist

functionalize :: Dstate Bool -> Dstate Bool
functionalize m = StateT $ \s ->
  let alts  = runStateT m s in
  let anchs = findAnchors alts in
  map (\(b,hist) -> (b, [makeFunc anchs hist])) alts

everyD' :: ET -> E
everyD' = mapCont functionalize . everyD

-- some pre-fab Dstate Bools with histories, for testing
randogirls :: Dstate Bool
randogirls = msum $ map ((>> return True) . put) $
  map ($ permutations $ take 3 girls) [(!!0), (!!3), (!!4)]

stream2 :: Dstate Bool
stream2 = randogirls >> modify (concatMap (\(a,b) -> [a,b]) . zip boys) >> return True


{-
-- generalizes "findAnchors" to patterns generated by multiple universals
-- (probably unnecessary if universals automatically functionalize as soon as
-- they take scope)
findAnchs :: Stack -> [Stack]
findAnchs indices = (maximumBy (comparing length) parts)
  where divisors x = [y | y <- [2..(x `div` 2)], x `mod` y ==0] ++ [x]
        chunks     = [chunksOf n indices | n <- divisors (length indices)]
        parts      = filter ((== 1) . length . nub . map diffs) chunks

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


trivstate, emptystate :: Dstate Bool
trivstate  = StateT $ \s -> [(True,s)]
emptystate = StateT $ \s -> []

c :: Int -> Dstate Bool
c x = lower $ lap (up $ someD leq3) (rap eq (up $ return x))

    


-- EXAMPLES
-- ========

-- eval $ lower $ rap geq8 nine
-- let x = eval $ lower $ lap (up $ everyD' (rap tall boy)) (rap matches (up $ someD (rap tall girl)))
-- M.toList $ (unfunc . head . snd) x

-}
