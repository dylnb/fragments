{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.Monad.Cont
import Control.Monad.State
import Data.List
import Control.Applicative ((<*>), (<$>))
import Data.List.Split (chunksOf)
--import Data.Monoid
--import Data.Ord
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
--import Debug.Hood.Observe
--import Debug.Trace
import Control.Exception (assert)

data Ref = Ent (String,Int)
           | Func {unfunc :: M.Map Ref Stack} --deriving (Eq,Show)
           | Plur {atoms :: [Ref]}
type Stack = [Ref]
type Dstate r = StateT Stack [] r
type Dcont a = Cont (Dstate Bool) a
type K a t = Cont (Dstate t) a

type E = Dcont Ref
type T = Dcont Bool
type ET = Dcont (Ref -> Bool)
type EET = Dcont (Ref -> Ref -> Bool)
type EEET = Dcont (Ref -> Ref -> Ref -> Bool)
type ETE = Dcont ((Ref -> Bool) -> Ref)
type ETET = Dcont ((Ref -> Bool) -> Ref -> Bool)

type E' t = K Ref t
type T' t = Dcont Bool
type ET' t = K (Ref -> Bool) t
type EET' t = K (Ref -> Ref -> Bool) t
type EEET' t = K (Ref -> Ref -> Ref -> Bool) t
type ETE' t = K ((Ref -> Bool) -> Ref) t
type ETET' t = K ((Ref -> Bool) -> Ref -> Bool) t


instance Show Ref where
  show (Ent (x,y)) = x ++ show y
  show (Plur xs)   = foldl (\a b -> a ++ "+" ++ show b) "" xs
  show _           = show "func"

instance Eq Ref where
  (Ent x) == (Ent y)     = x == y
  (Plur xs) == (Plur ys) = xs == ys
  _ == _                 = False

instance Ord Ref where
  compare (Ent (name,tag)) (Ent (name',tag')) = compare tag tag'
  compare _ _                                 = EQ


-- AUXILIARY FUNCTIONS
-- ===================

-- Backwards function application
(<|) :: a -> (a -> b) -> b
a <| b = b a

-- Characteristic set of a property
characteristic :: (Ref -> Bool) -> Stack
characteristic p = filter p univ

-- Stack difference
-- (this only makes sense if stacks are guaranteed not to diverge)
minus :: Stack -> Stack -> Stack
s1 `minus` s2 = take (length s1 - length s2) s1

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
--lap :: Dcont a -> Dcont (a -> b) -> Dcont b
lap :: K a t -> K (a -> b) t -> K b t
-- lap = flip ap (watch out: side effects still flow from function to arg)
lap m h = do
  x <- m
  f <- h
  return $ f x

--rap :: Dcont (a -> b) -> Dcont a -> Dcont b
rap :: K (a -> b) t -> K a t -> K b t
rap = ap 

-- First-Order Unit Function
-- ("lift")
--ret :: a -> Dcont a
ret :: a -> K a t
ret = return

-- First-Order Lower Function
-- (overloaded for continuized individuals to make printing easier)
-- class Lowerable a where
--   --lower :: Dcont a -> Dstate a
--   lower :: K a a -> Dstate a
-- instance Lowerable Bool where
--   lower m = runCont m return
-- instance Lowerable Ref where
--   --lower m = runCont m (\x -> unit' [x] True) >>= (\_ -> pop)
--   lower m = runCont m return

lower :: K a a -> Dstate a
lower m = runCont m return

-- Second-Order Continuized Application
--llap :: Dcont (Dcont a) -> Dcont (Dcont (a -> b)) -> Dcont (Dcont b)
llap :: K (K a t) t' -> K (K (a -> b) t) t' -> K (K b t) t'
llap m h = do
 x <- m
 f <- h
 return $ lap x f

--rrap :: Dcont (Dcont (a -> b)) -> Dcont (Dcont a) -> Dcont (Dcont b)
rrap :: K (K (a -> b) t) t' -> K (K a t) t' -> K (K b t) t'
rrap = liftM2 ap
-- rrap h m = do
--   f <- h
--   x <- m
--   return $ rap f x

-- Second-Order Unit Function
-- ("internal lift")
--rret :: Dcont a -> Dcont (Dcont a)
rret :: K a t -> K (K a t') t
rret f = lap f (return return)

-- Second-Order Lower Function
--llower :: Dcont (Dcont a) -> Dcont a
llower :: K (K a t) t -> K a t
llower outer = cont $ \k -> StateT $ \s -> 
  runStateT
    ( runCont outer
      (\m -> StateT $ \s' ->
        runStateT
          (runCont m
                   (\a -> StateT $ \s'' ->
                     runStateT (k a) (s'' ++ (s' `minus` s))
                   )
          ) s
      )
    ) s

llorret :: K (K a t) t -> K (K a t) t'
llorret = ret . llower


-- SIMPLE BINDING
-- ==============

-- First-Order Push
--up :: E -> E
up :: E' t -> E' t
up m = cont $ \k ->
  runCont m (\x -> StateT $ \s -> runStateT (k x) (s++[x]))
  --runCont m (\x -> StateT $ \s -> runStateT (k x) (x:s))

-- Second-Order Push
--uup :: Dcont E -> Dcont E
uup :: K (E' t) t' -> K (E' t) t'
uup mm = do
  m <- mm
  ret (up m)


-- RESET
-- =====

-- First-Order Reset
reset :: K a a -> K a t
reset m = cont $ \k -> do
  x <- lower m
  k x

-- Second-Order Reset
rreset :: K (K a a) (K a t) -> K (K a t) t'
rreset mm = cont $ \k -> do
  x <- runCont mm (return . reset)
  k x

-- THE MODEL AND THE LANGUAGE
-- ==========================
   
boys, girls, poems, univ :: Stack
boys  = map (\x -> Ent ("b",x)) [1..6]
girls = map (\x -> Ent ("g",x)) [1..6]
poems = map (\x -> Ent ("p",x)) [1..6]
univ  = concat [boys, girls, poems]

-- Proper Names
--boy1, boy2, boy3, boy4, boy5, boy6 :: E
boy1, boy2, boy3, boy4, boy5, boy6 :: E' t
[boy1, boy2, boy3, boy4, boy5, boy6] = map return boys

--girl1, girl2, girl3, girl4, girl5, girl6 :: E
girl1, girl2, girl3, girl4, girl5, girl6 :: E' t
[girl1, girl2, girl3, girl4, girl5, girl6] = map return girls

--poem1, poem2, poem3, poem4, poem5, poem6 :: E
poem1, poem2, poem3, poem4, poem5, poem6 :: E' t
[poem1, poem2, poem3, poem4, poem5, poem6] = map return poems

-- Pronouns
--he :: Int -> E
he :: Int -> E' t
he n = cont $ \k -> do
  s <- get
  let ind = length s - n - 1
  assert (ind >= 0) $ k (s !! ind)
-- pronouns count backward


-- One-Place Predicates
--boy, girl, poem, triv :: ET
boy, girl, poem, triv :: ET' t
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
--likes, envies, pities, listensTo :: EET
likes, envies, pities, listensTo :: EET' t
--[eq, lt, gt] = map return [(==), (>), (<)]

-- people like anything that their "tags" are equal to:
-- b1 likes g1, g3 likes p3, but g5 doesn't like b4 or g4
likes = let likes' (Ent (_,n)) (Ent (_,m)) = n == m
            likes' _ _                     = False in
          return likes'

-- people envy people of the same gender that they are less than:
-- b1 envies b3, but b3 does not envy b1 nor does he envy g6
envies = let envies' (Ent (x,n)) (Ent (y,m)) = x == y &&
                                               n > m
             envies' _ _                     = False in
          return envies'

pities = let pities' (Ent (x,n)) (Ent (y,m)) = x == y &&
                                               n < m
             pities' _ _                     = False in
          return pities'

-- people listen to people of the opposite gender that they divide evenly:
-- b2 listens to g6, as does b3, but b4 doesn't, and neither does g2
listensTo = let lt' (Ent (x,n)) (Ent (y,m)) =
                   n `mod` m == 0 && (x == "g" && y == "b"  ||
                                      x == "b" && y == "g")
                lt' _ _                     = False in
          return lt'


-- Three-Place Predicates
--gave :: EEET
gave :: EEET' t

-- boys give girls poems in runs:
-- b1 gave g2 p3, and b4 gave g5 p6, but b1 didn't give g3 anything, and he
-- didn't give p4 to anybody
gave = let gave' (Ent (x,n)) (Ent (y,m)) (Ent (z,o)) =
             x == "g" && y == "p" && z == "b" &&
             n == o+1 && m == n+1
           gave' _ _ _                               = False in
       return gave'


-- et -> et Adjectives
-- ==========================

--short, tall :: ETET
short, tall :: ETET' t
short = let short' p e@(Ent (_,n)) = p e && n <= 3
            short' _ _             = False in
        return short'

tall = let tall' p e@(Ent (_,n)) = p e && n > 3
           tall' _ _             = False in
       return tall'

-- Abbreviations
--tb,tg,sb,sg :: ET
tb,tg,sb,sg :: ET' t
tb = rap tall boy
tg = rap tall girl
sb = rap short boy
sg = rap short girl

-- 'ownedBy' approximates English 'of'. It takes two arguments, a nominal
-- and an individual (the owner). So "book ownedby Boy3" is the set of books
-- that Boy3 owns. As it happens, Boy1 doesn't own any poems.
--ownedBy :: Dcont ((Ref -> Bool) -> Ref -> Ref -> Bool)
ownedBy :: K ((Ref -> Bool) -> Ref -> Ref -> Bool) t
ownedBy = let ownedBy' p (Ent (x,n)) e@(Ent (y,m)) =
                p e && y == "p" && n == m && n /= 1
              ownedBy' _ _ _                       = False in
          return ownedBy'

-- ET -> E Quantifiers
-- ==========================

-- auxiliary functions for working with restrictors
--check :: ET -> Ref -> Dstate Bool
check :: ET' Bool -> Ref -> Dstate Bool
check p = lower . rap p . return

-- "bottle" takes an ref x and a stateful bool t, and replaces the (True, s') pairs
-- in t with (x, s') pairs, and discards the rest; intuitively, it filters t, 
-- and then "bottles" x up with the various result states:
--   bottle 3 (\s -> [(T,7:s), (F,8:s), (T,9:s)]) == \s -> [(3,7:s), (3,9:s)]
-- the only problem is that if x completely fails p, "bottle" returns the
-- empty individual (\s -> []), which has to swept out later.
bottle :: Ref -> Dstate Bool -> Dstate Ref
bottle x t = mfilter id t >> return x

--someD :: ET -> E
someD :: ET' Bool -> E' t
someD p  = cont $ \k -> do
  x <- lift univ
  b <- check p x 
  if b then k x else mzero

-- equivalent to someD
--altsomeD :: ET -> E
altsomeD :: ET' Bool -> E' t
altsomeD p = cont $ \k -> do
  let xs = map ((>>) <$> mfilter id . check p <*> return) univ
  foldl1 mplus xs >>= k
  
-- almost right, but doesn't pass referents from restr to scope 
--simpleeveryD :: ET -> E
simpleeveryD :: ET' Bool -> E' Bool
simpleeveryD p = cont $ \k -> do
  let xs = filter (any fst . eval . check p) univ
  let ps = map k xs
  foldl1 (liftM2 (&&)) ps

-- internally dynamic universal
--everyD :: ET -> E
everyD :: Fusable t => ET' Bool -> E' t
everyD p = cont $ \k -> do
  let xs = filter (not . null . eval) $
           map (bottle <*> check p) univ
  let ps = filter (not . null . eval) $
           -- the line above protects the computation against scope failure,
           -- as in "Every short boy likes someone he pities", which will
           -- otherwise fail on Boy1 who doesn't pity anyone. Switch this line
           -- off to get a more presupposition-failure like semantics
           map (>>= k) xs
  foldl1 (liftM2 fuse) ps

class Fusable a where
  fuse :: a -> a -> a
instance Fusable Bool where
  fuse p q = p && q
instance Fusable Ref where
  fuse x y = x `oplus` y

-- Simon's universal; not clear whether the written fragment corresponds to
-- version 1 (scopeignore) or version 2 (scopeattend)
--everyS :: ET -> E
everyS :: ET' Bool -> E' Bool
everyS p = cont $ \k -> StateT $ \s -> 
  let xs = concatMap (($ s) . runStateT . (bottle <*> check p)) univ in

  -- This ignores any restrictor elements that come up empty on the nuclear
  -- scope; it's as if they never mattered; mirrors the behavior of someD
  let ps = mapMaybe (scopeignore . uncurry (runStateT . k)) xs in
  concat ps -- helpful to see the results when exploring
  --[(all (any fst) ps, s)] -- provides the real deterministic answer
  --

  {- This attends to restrictor elements that come up empty, and considers
  -- them equivalent to falsity
  let ps = map (scopeattend . uncurry (runStateT . k)) xs in
  concat ps -- helpful to see the results when exploring
            -- But watch out: this ignores restrictor failure
  --[(all (any fst) ps, s)] -- provides the real deterministic answer
  -}
  where scopeignore bs
          | null bs   = Nothing
          | otherwise = Just bs
        scopeattend bs
          | null bs   = [(False, [])] -- this is just to make things clear;
                                      -- the computation would return False anyway
                                      -- because "any fst []" == False
          | otherwise = bs

-- POSSESSIVES
-- ===========
--poss :: E -> ET -> Dcont E
poss :: E' t -> ET' Bool -> K (E' t) t
poss g p = rap (ret someD) (rrap (llap (ret p) (ret ownedBy)) (rret g))


-- ADJECTIVES SENSITIVE TO ACCUMULATION
-- ===================================
--different :: ETET
different :: ETET' t
different = cont $ \k -> do {s <- get; k (\p x -> p x && x `notElem` s)}

--longer :: ETET
longer :: ETET' t
longer = cont $ \k -> do
  s <- get
  k (\p x ->  p x && (null s || x > maximum s))



-- TEST ZONE AND TEST TERMS
-- ========================

-- Machinery for making functional witnesses 
skipdist :: [Int] -> Int
skipdist s =
  let dl = [(s!!n) - (s!!(n-1)) | n <- [1..length s - 1]] in
  -- assert ((length . nub) dl == 1) (head dl)
  head dl

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

--everyD' :: ET -> E
everyD' :: ET' Bool -> E' Bool
everyD' = mapCont functionalize . everyD

-- some pre-fab Dstate Bools with histories, for testing
randogirls :: Dstate Bool
randogirls = msum $
  map ((>> return True) . put . ($ permutations $ take 3 girls)) choices
  where choices = [(!! 0), (!! 3), (!! 4)]

stream2 :: Dstate Bool
stream2 = randogirls >> modify (concatMap (\(a,b) -> [a,b]) . zip boys)
                     >> return True

oplus :: Ref -> Ref -> Ref
oplus x@(Ent _)  (Plur ys) = Plur (x:ys)
oplus (Plur xs)  y@(Ent _) = Plur (xs++[y])
oplus (Plur xs) (Plur ys)  = Plur (xs++ys)
oplus x y                  = Plur [x,y]

shortboys :: Ref
shortboys = foldl1 oplus $ take 3 boys

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

up' :: E -> E
up' m = m >>= (\x -> cont $ \k -> do {modify (x:); k x})

up'' :: E -> E
up'' m = m >>= (\x -> cont $ \k -> StateT $ \s -> k x (x:s))

--up3 :: E -> E
--up3 m = do {x <- m; pushC x}


trivstate, emptystate :: Dstate Bool
trivstate  = StateT $ \s -> [(True,s)]
emptystate = StateT $ \s -> []

c :: Int -> Dstate Bool
c x = lower $ lap (up $ someD leq3) (rap eq (up $ return x))

-}


-- EXAMPLES
-- ========

{-

"Boy4 is a tall boy"
eval $ lower $ rap tb (up boy4)

"Some tall boy likes some tall girl"
eval $ lower $ lap (up $ someD tb) (rap likes (up $ someD tg))

"Every tall boy likes some tall girl"
eval $ lower $ lap (up $ everyD tb) (rap likes (up $ someD tg))

"Some tall girl likes every tall boy" (inverse scope)
eval $ lower $ llower $ llap (ret (up $ someD tg)) (rrap (ret likes) (rret (up $ everyD tb)))

"Some short girl likes herself"
eval $ lower $ lap (up $ someD sg) (rap likes (up $ he 0))

"Someone liking Boy2 listens to Girl6"
eval $ lower $ lap (up $ someD (rap likes boy2)) (rap listensTo girl6)

"Someone envying every tall boy listens to Girl4" (surface scope)
eval $ lower $ lap (up $ someD (rap envies (up $ everyD tb))) (rap listensTo girl4)

eval $ lower $ lap (up $ someD (rap envies (up $ everyS tb))) (rap listensTo girl4)

"Someone liking every short boy listens to Girl6" (inverse scope)
eval $ lower $ llower $ llap (uup (rap (ret someD) (rrap (ret likes) (rret (up $ everyD sb))))) (rrap (ret listensTo) (ret girl6))

========================================
* RESET *
=========
eval $ lower $ llower $ llap (rreset $ llower $ uup $ rap (return someD) (rrap (ret likes) (rret (up $ everyD sb)))) (rrap (ret listensTo) (ret girl6))
=========================================


"Some short boy pities someone who envies him" (Boy1 drops out)
eval $ lower $ lap (up $ someD sb) (rap pities (up $ someD (rap envies $ he 0)))

"Every short boy pities someone who envies him" (Boy1 drops out, or presup failure)
eval $ lower $ lap (up $ everyD sb) (rap pities (up $ someD (rap envies $ he 0)))

"Boy2's poem is short"
eval $ lower $ llower $ llap (uup $ (up boy2) <| poss $ poem) (rrap (ret short) (ret poem))

"Boy2's poem is owned by him"
eval $ lower $ llower $ llap ((up boy2) <| poss $ poem) (rrap (llap (ret poem) (ret ownedBy)) (rret $ he 0))

"Every short boy's poem is short" (Boy1 drops out: narrowing)
eval $ lower $ llower $ llap (uup $ (up $ everyD sb) <| poss $ poem) (rrap (ret short) (ret poem))

"Every short boy envies a different tall boy"
eval $ lower $ lap (up $ everyD sb) (rap envies (up $ someD (rap different tb)))

"Every short boy envies a longer tall girl"
eval $ lower $ lap (up $ everyD sb) (rap envies (up $ someD (rap longer tg)))

"Every tall boy likes some tall girl" (functionalized)
let x = eval $ lower $ lap (up $ everyD' (rap tall boy)) (rap likes (up $ someD (rap tall girl))) in M.toList $ (unfunc . head . snd) (x!!5)

-}
