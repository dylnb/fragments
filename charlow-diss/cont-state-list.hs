{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances #-}
{-# LANGUAGE TupleSections #-}

import Control.Monad.Cont
import Control.Monad.Trans.State
import Data.List
import qualified Data.Set as S (fromList)
import Control.Applicative ((<*>), (<$>), (<**>))
import Data.List.Split (chunksOf)
import Data.Function (on)
--import Data.Monoid
--import Data.Ord
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
--import Debug.Hood.Observe
--import Debug.Trace
import Control.Exception (assert)

-- =================
-- ** TYPE SYSTEM ** 
-- =================

data Ent = Atom (String,Int)
         | Plur {atoms :: [Ent]}
         | Func {unfunc :: M.Map Ent Stack}
type Stack     = [Ent]
type Dstate    = StateT Stack []
type Kappa a r = ContT r Dstate a

type E r    = Kappa Ent r
type T r    = Kappa Bool r
type ET r   = Kappa (Ent -> Bool) r
type EET r  = Kappa (Ent -> Ent -> Bool) r
type EEET r = Kappa (Ent -> Ent -> Ent -> Bool) r
type ETE r  = Kappa ((Ent -> Bool) -> Ent) r
type ETET r = Kappa ((Ent -> Bool) -> Ent -> Bool) r

instance Show Ent where
  show (Atom (x,y)) = x ++ show y
  show (Plur xs)    = foldl (\a b -> a ++ "+" ++ show b) "" xs
  show _            = show "func"

instance Eq Ent where
  (Atom x)  == (Atom y)  = x == y
  (Plur xs) == (Plur ys) = S.fromList xs == S.fromList ys
  _ == _                 = False

instance Ord Ent where
  compare (Atom (name,tag)) (Atom (name',tag')) = compare tag tag'
  compare _ _                                   = EQ

instance Eq a => Eq (Dstate a) where
  (==)  = (==) `on` run


-- ========================
-- ** MONADIC OPERATIONS **
-- ========================

-- TESTING
-- =======

nlift :: Dstate a -> ContT r Dstate a
nlift = lift

-- klift :: ContT r Dstate a -> ContT r' (ContT r Dstate) a
klift :: Monad m => ContT r m a -> ContT r' (ContT r m) a
klift = lift
-- klift m = ContT $ \g -> m >>= (\x -> g x)
-- klift m = ContT $ \g -> ContT $ \k -> runContT m (\x -> runContT (g x) k)

klower ::  Monad m => ContT r m r -> m r
klower = (`runContT` return)

kreset ::  ContT a (ContT r Dstate) a -> ContT r' (ContT r Dstate) a
kreset = klift . klower


-- UNIT (GENERALIZED "LIFT")
-- ========================

-- First-Order Unit Function
-- (linguist's "lift")
unit :: a -> Kappa a r
unit = return

-- Second-Order Unit Function
-- ("internal lift")
uunit :: Kappa a r -> Kappa (Kappa a r') r
uunit = liftM unit
-- equivalent to:
-- uunit m = do
--   x <- m
--   unit $ unit x
-- equivalent to:
-- uunit m = m `lap` (unit unit)

-- Shift!
-- (not used here, but worth thinking about)
shift :: ((a -> Kappa p o) -> Kappa p p) -> Kappa a p
shift h = ContT $ \k -> lower $ h (lift . k)

-- APPLICATION
-- ===========
 
(~/~) = rap
(~//~) = rrap
(~\~) = lap
(~\\~) = llap

-- First-Order Continuized Application
lap :: Kappa a r -> Kappa (a -> b) r -> Kappa b r
lap = (<**>)
-- equivalent to:
-- lap = liftM2 (flip ($))
-- equivalent to:
-- lap m h = do
--   x <- m
--   f <- h
--   unit (x <$ f)

rap :: Kappa (a -> b) r -> Kappa a r -> Kappa b r
rap = (<*>)
-- equivalent to:
-- rap = liftM2 ($)
-- equivalent to:
-- rap h m = do
--   f <- h
--   x <- m
--   unit (f $ x)

-- Second-Order Continuized Application
llap :: Kappa (Kappa a r) r' -> Kappa (Kappa (a -> b) r) r' -> Kappa (Kappa b r) r'
llap = liftM2 lap
-- equivalent to:
-- llap m h = do
--   x <- m
--   f <- h
--   unit (x `lap` f)

rrap :: Kappa (Kappa (a -> b) r) r' -> Kappa (Kappa a r) r' -> Kappa (Kappa b r) r'
rrap = liftM2 rap
-- equivalent to:
-- rrap h m = do
--   f <- h
--   x <- m
--   unit (f `rap` x)

-- LOWER
-- =====

-- First-Order Lower Function
lower :: Kappa a a -> Dstate a
lower = (`runContT` return)

-- Second-Order Lower Function
llower :: Kappa (Kappa a r) r -> Kappa a r
llower = join
-- llower outer = ContT $ \k -> StateT $ \s -> 
--   runStateT
--     ( (runContT outer)
--       (\m -> StateT $ \s' ->
--         runStateT
--           (runContT m
--                    (\a -> StateT $ \s'' ->
--                      runStateT (k a) (s'' ++ (s' `minus` s))
--                    )
--           ) s
--       )
--     ) s


-- SIMPLE BINDING
-- ==============

-- First-Order Push
up :: E r -> E r
up = withContT (\f x -> modify (++[x]) >> f x)
-- equivalent to:
-- up m = ContT $ \k ->
--   runContT m (\x -> StateT $ \s -> runStateT (k x) (s++[x]))

-- Second-Order Push
uup :: Kappa (E r) r' -> Kappa (E r) r'
uup = liftM up
-- equivalent to:
-- uup m = m `lap` (unit up)
-- equivalent to:
-- uup m = do
--   x <- m
--   unit $ up x


-- RESET
-- =====

-- First-Order Reset
reset :: Kappa a a -> Kappa a r
reset = lift . lower
-- equivalent to:
-- reset m = ContT $ \k -> do
--   x <- lower m
--   k x

-- Second-Order Reset
-- there are options here. we can simply apply "reset" to a two-level tower,
-- which only resets the outermost layer. or we can apply "liftM reset" (i.e.
-- "rreset1"), which only resets the innermost layer. or we can apply
-- "rreset2", which resets them both
rreset1 :: Kappa (Kappa a a) r' -> Kappa (Kappa a r) r'
rreset1 = liftM reset
-- equivalent to:
-- rreset1 mm = ContT $ \k -> do
--   m <- mm
--   unit $ reset m

rreset2 :: Kappa (Kappa a a) (Kappa a r) -> Kappa (Kappa a r) r'
rreset2 = reset . liftM reset
-- equivalent to:
-- rreset2 mm = ContT $ \k -> do
--   m <- runContT mm (return . reset)
--   k m

-- ===============
-- ** THE MODEL **
-- ===============

-- INDIVIDUALS
-- ===========

-- Atomic Individuals
boys, girls, poems :: Stack
[boys,girls,poems] =
  chunksOf 6 [Atom ([x],y) | x <- "bgp", y <- [1..6]]

-- Plural Individuals
shortboys, shortgirls, longpoems :: Ent
[shortboys,shortgirls,longpoems] =
  [Plur $ take 3 xs | xs <- [boys,girls,(reverse poems)]]

-- The Domain
domAtoms, domPlurs, univ :: Stack
domAtoms = concat [boys, girls, poems]
domPlurs = [shortboys, shortgirls, longpoems]
univ     = domAtoms ++ domPlurs

-- Link's join/sum connective
oplus :: Ent -> Ent -> Ent
oplus x@(Atom _)  (Plur ys) = Plur (x:ys)
oplus (Plur xs)  y@(Atom _) = Plur (xs++[y])
oplus (Plur xs) (Plur ys)   = Plur (xs++ys)
oplus x y                   = Plur [x,y]

-- Link's exclusive pluralizer
pl :: ET Bool -> ET r
pl p = let p' (Plur xs) = all (any fst . run . check p) xs
           p' _         = False in
       unit p'

-- Some pre-fab Dstate Bools with histories, for testing
randogirls :: Dstate Bool
randogirls = msum $ map ((>> return True) . modify . flip (++)) $
             map ($ permutations $ take 3 girls) [(!!0), (!!3), (!!4)]

boygirls :: Dstate Bool
boygirls = randogirls >> modify (concatMap (\(a,b) -> [a,b]) . zip boys)
                      >> return True

-- ==================
-- ** THE LANGUAGE **
-- ==================

-- NOMINALS
-- ========

-- Proper Names
-- ------------------------------------------------
boy1, boy2, boy3, boy4, boy5, boy6 :: E r
[boy1, boy2, boy3, boy4, boy5, boy6] = map unit boys

girl1, girl2, girl3, girl4, girl5, girl6 :: E r
[girl1, girl2, girl3, girl4, girl5, girl6] = map unit girls

poem1, poem2, poem3, poem4, poem5, poem6 :: E r
[poem1, poem2, poem3, poem4, poem5, poem6] = map unit poems
-- ------------------------------------------------

-- Pronouns
-- ------------------------------------------------
he :: Int -> E r
he n = lift $ do {s <- get; assert (length s > 0) $ return (reverse s !! n)}
                                                  -- pronouns count backward
-- equivalent to:
-- he n = lift $ gets ((!!n) . reverse) 
-- ------------------------------------------------


-- PREDICATES
-- ===========

-- One-Place Predicates
-- ------------------------------------------------
boy, girl, poem, triv :: ET r
boy = let boy' (Atom ("b",_)) = True
          boy' _              = False in
      unit boy'

girl = let girl' (Atom ("g",_)) = True
           girl' _              = False in
       unit girl'

poem = let poem' (Atom ("p",_)) = True
           poem' _              = False in
       unit poem'
 
triv = unit (const True)
-- ------------------------------------------------

-- Two-Place Predicates
-- ------------------------------------------------
likes, envies, pities, listensTo, overwhelm :: EET r

-- people like the people they are coindexed with :)
-- b1 likes g1, g3 likes b3, but g5 doesn't like b4 or g4
likes = let likes' (Atom (x,n)) (Atom (y,m)) = n == m &&
                                               y /= "p"
            likes' _ _                       = False in
        unit likes'

-- people envy people of the same gender that they are less than:
-- b1 envies b3, but b3 does not envy b1 nor does he envy g6
envies = let envies' (Atom (x,n)) (Atom (y,m)) = x == y &&
                                                 n > m
             envies' _ _                       = False in
         unit envies'

-- people pity people that envy them:
-- b3 pities b1, but not g1, nor does b1 pity him
pities = let pities' (Atom (x,n)) (Atom (y,m)) = x == y &&
                                                 n < m
             pities' _ _                       = False in
         unit pities'

-- people listen to people of the opposite gender that they divide evenly:
-- b2 listens to g6, as does b3, but b4 doesn't, and neither does g2
listensTo = let lt' (Atom (x,n)) (Atom (y,m)) =
                   n `mod` m == 0 && (x == "g" && y == "b"  ||
                                      x == "b" && y == "g")
                lt' _ _                       = False in
            unit lt'

-- +p4+p5+p6 overwhelm g1, and +b1+b2+b3 overwhelm each of b1,b2, and b3;
-- nothing else overwhelms anyone else
overwhelm = let ow' y xs =
                  xs == longpoems && y == girls!!0 ||
                  xs == shortboys  && y `elem` (take 3 boys) in
            unit ow'
-- ------------------------------------------------

-- Three-Place Predicates
-- ------------------------------------------------
gave :: EEET r

-- boys give girls poems in runs:
-- b1 gave g2 p3, and b4 gave g5 p6, but b1 didn't give g3 anything, and he
-- didn't give p4 to anybody
gave = let gave' (Atom (x,n)) (Atom (y,m)) (Atom (z,o)) =
             x == "g" && y == "p" && z == "b" &&
             n == o+1 && m == n+1
           gave' _ _ _i                                 = False in
       unit gave'
-- ------------------------------------------------


-- ADJECTIVES
-- ==========
short, tall, long :: ETET r
short = let short' p e@(Atom (_,n)) = p e && n <= 3
            short' _ _              = False in
        unit short'

tall = let tall' p e@(Atom (_,n)) = p e && n > 3
           tall' _ _              = False in
       unit tall'

long = let long' p e@(Atom (x,n)) = p e && n > 3 && x == "p"
           long' _ _              = False in
       unit long'


-- Accumulating Adjectives
-- ------------------------------------------------
different, longer, same :: ETET r
different = ContT $ \k -> do {s <- get; k (\p x -> p x && x `notElem` s)}

same = ContT $ \k -> do {s <- get; k (\p x -> p x && (x `elem` s || s == []))}

longer = ContT $ \k -> do
  s <- get
  k (\p x ->  p x && (null s || x > maximum s))
-- ------------------------------------------------

-- Abbreviations
tb,tg,sb,sg :: ET r
tb = rap tall boy
tg = rap tall girl
sb = rap short boy
sg = rap short girl


-- PREPOSITIONS
-- ============

-- Boys wrote the poems they match,
-- except for poem1, which was written by girl1
by :: Kappa (Ent -> (Ent -> Bool) -> Ent -> Bool) r
by = let by' (Atom (x,n)) p e@(Atom (y,m)) =
                p e && y == "p" && n == m &&
                ((x == "b") `xor` (x /= "p" && n == 1))
         by' _ _ _                         = False in
     unit by'
-- the following people wrote the following poems:
--   Girl1 -- Poem1
--   Boy4  -- Poem2, Poem3, Poem4
--   Boy5  -- Poem5
--   Boy6  -- Poem6
-- by = let by' (Atom (x,n)) p e@(Atom (y,m)) =
--                 p e && y == "p" &&
--                 case (x,n) of
--                   ("g",1) -> m == 1
--                   ("b",4) -> m `elem` [2,3,4]
--                   ("b",5) -> m == 5
--                   ("b",6) -> m == 6
--                   (_,_)   -> False
--          by' _ _ _                         = False in
--      unit by'

-- 'ownedBy' approximates English 'of'.
-- people own the poems they wrote
ownedBy :: Kappa (Ent -> (Ent -> Bool) -> Ent -> Bool) r
ownedBy = by

-- CONNECTIVES
-- ===========

class MonadTimes a where
  mtimes :: a -> a -> a
instance MonadTimes Bool where
  mtimes = (&&)
instance MonadTimes Ent where
  mtimes = oplus
instance (Monad m, MonadTimes a) => MonadTimes (m a) where
  mtimes = liftM2 mtimes

conj :: MonadTimes m => m -> m -> m
conj = mtimes

disj :: MonadPlus m => m a -> m a -> m a
disj = mplus

mproduct :: (Monad m, MonadTimes a) => [m a] -> m a
mproduct = foldl1 conj

-- DETERMINERS
-- ===========

-- Auxiliary functions for working with restrictors
-- ------------------------------------------------
check :: ET Bool -> Ent -> Dstate Bool
check p = lower . rap p . unit

-- "bottle" takes a ref x and a stateful bool t, and replaces the (True, s')
-- pairs in t with (x, s') pairs, and discards the rest;
-- intuitively, it filters t, and then "bottles" x up with the various
-- result states:
--   bottle 3 (\s -> [(T,7:s), (F,8:s), (T,9:s)]) == \s -> [(3,7:s), (3,9:s)]
bottle :: Ent -> Dstate Bool -> Dstate Ent
bottle x t = mfilter id t >> return x

-- if x completely fails p, "bottle" returns the empty individual:
--   (\s -> [])
-- we can try and flush this out, but it might blow up in our faces if p
-- contains a pronoun; better just to leave the empty individual, which 
-- eventually dissipates in the concatenation of `someD' anyway
charact ::  ET Bool -> [Dstate Ent]
charact p = map (bottle <*> check p) domAtoms
            -- equivalent to:
            -- map ((>>) <$> mfilter id . check p <*> return) domAtoms
-- ------------------------------------------------

-- Indefinites
-- ------------------------------------------------
someD :: ET Bool -> E r
someD = lift . msum . charact
-- equivalent to:
-- someD p  = ContT $ \k -> do
--   x <- lift domAtoms
--   b <- check p x 
--   if b then k x else mzero
-- equivalent to:
-- someD p = ContT $ \k -> do
--   let xs = charact p
--   let ps = map (k =<<) xs
--   foldl1 mplus ps
--   -- equivalent to:
--   -- (msum xs) >>= k

twoD :: ET Bool -> E r
twoD p = lift $ msum $
  nub [x `conj` y | x <- charact p, y <- charact p, ((/=) `on` run) x y]
-- ------------------------------------------------

-- Universals
-- ------------------------------------------------
everyD :: MonadTimes r => ET Bool -> E r
everyD p = ContT $ \k -> do
  let xs = filter (not . null . run) $
           -- flushes out individuals that completely fail the restrictor, 
           -- but explodes if the restrictor contains pronouns :(
           charact p
  let ps = -- filter (not . null . run) $
           -- the line above protects the computation against scope failure, 
           -- as in "Every short boy likes someone he pities", which will
           -- otherwise fail on Boy1 who doesn't pity anyone. Comment this
           -- line out off to get a more presupposition-failure like semantics
           map (k =<<) xs
  foldl1 conj ps
-- essentially equivalent to:
--   everyD = lift . mproduct . charact
-- but with handlers for empty individuals

test = liftCatch

-- a towerish version of everyD
-- shows slightly different behavior when "different" is in a restrictor
alteveryD :: MonadTimes r => ET Bool -> E r
alteveryD p = ContT $ \k -> StateT $ \s ->
  let witnesses x = filter fst $ runStateT (check p x) s in
  let ps = filter (not . null . (`runStateT` s)) $
           map (\x -> StateT $ \s' -> concat $ [runStateT (k x) (s'++(s'' `minus` s))
                                                 | (_,s'') <- witnesses x]) domAtoms in
  runStateT (foldl1 conj ps) s

-- externally static (possibly deterministic) version of everyD
everyS' :: MonadTimes r => ET Bool -> E r
-- everyS' :: ET Bool -> E Bool
everyS' = mapContT (\m -> do {s <- get; mapStateT ((,s) . fst <$>) m}) . everyD
-- everyS' = mapContT (\m -> do {s <- get; mapStateT (\ts -> [(any fst ts, s)]) m}) . everyD
-- equivalent to:
-- everyS' p = ContT $ \k -> StateT $ \s -> [(or $ evalStateT (runContT (everyD p) k) s, s)]

-- Simon's universal; not clear whether the written fragment corresponds to
-- version 1 (scopeignore) or version 2 (scopeattend)
--everyS :: ET -> E
everyS :: ET Bool -> E Bool
everyS p = ContT $ \k -> StateT $ \s -> 
  let xs = domAtoms >>= ((`runStateT` s) . (bottle <*> check p)) in

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
          | bs == []  = Nothing
          | otherwise = Just bs
        scopeattend bs
          | bs == []  = [(False, [])] -- this is just to make things clear; the
                                      -- computation would return False anyway
                                      -- because "any fst []" == False
          | otherwise = bs
-- ------------------------------------------------

-- Possessives
-- ------------------------------------------------
poss :: E r -> ET Bool -> Kappa (E r) r
poss g p = rap (unit someD) (llap (unit p) (rrap (unit ownedBy) (uunit g)))
-- ------------------------------------------------


-- ==========================
-- ** FUNCTIONAL WITNESSES **
-- ==========================

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

makeFunc :: [Int] -> Stack -> Ent
makeFunc anchs hist = Func $ M.fromList splits
  where splits = map (\(i:is) -> (i,is)) $ chunksOf (skipdist anchs) hist'
        hist'  = drop (head anchs) hist

functionalize :: Dstate Bool -> Dstate Bool
functionalize m = StateT $ \s ->
  let alts  = runStateT m s in
  let anchs = findAnchors alts in
  map (\(b,hist) -> (b, [makeFunc anchs hist])) alts

-- Functionalizing universal
--everyF :: ET -> E
everyF :: ET Bool -> E Bool
everyF = mapContT functionalize . everyD


{-
-- generalizes "findAnchors" to patterns generated by multiple universals
-- (probably unnecessary if universals automatically functionalize as soon as
-- they take scope)
findAnchs :: Stack -> [Stack]
findAnchs indices = (maximumBy (comparing length) parts)
  where divisors x = [y | y <- [2..(x `div` 2)], x `mod` y ==0] ++ [x]
        chunks     = [chunksOf n indices | n <- divisors (length indices)]
        parts      = filter ((== 1) . length . nub . map diffs) chunks
-}

-- =========================
-- ** AUXILIARY FUNCTIONS **
-- =========================

-- Backwards function application
(<$) :: a -> (a -> b) -> b
a <$ b = b a

-- Exclusive disjunction
xor :: Bool -> Bool -> Bool
x `xor` y = (x || y) && (not (x && y))

-- Stack difference
-- (this only makes sense if stacks are guaranteed not to diverge in the
-- course of a computation)
minus :: Stack -> Stack -> Stack
s1 `minus` s2 = take ((length s1) - (length s2)) s1

-- Evaluation functions
run :: Dstate a -> [(a,Stack)]
run = (`runStateT` [])

eval :: Kappa a a -> [(a,Stack)]
eval = run . lower

eeval :: Kappa (Kappa a a) a -> [(a,Stack)]
eeval = run . lower . llower


-- ==============
-- ** EXAMPLES **
-- ==============

{-

BASIC SENTENCES
===============

"Boy4 is a tall boy"
eval $ lap (up boy4) tb

"Some tall boy likes some tall girl"
eval $ lap (up $ someD tb) (likes </> (up $ someD tg))

"Every tall boy likes some tall girl"
eval $ lap (up $ everyD tb) (rap likes (up $ someD tg))

"Some tall girl likes every tall boy" (inverse scope)
eeval $ llap (uup $ unit $ someD tg) (rrap (unit likes) (uup $ uunit $ everyD tb))

"Some short girl likes herself"
eval $ lap (up $ someD sg) (rap likes (up $ he 0))

"Someone liking Boy2 listens to Girl6"
eval $ lap (up $ someD (rap likes boy2)) (rap listensTo girl6)

"Someone envying every tall boy listens to Girl4" (surface scope)
eval $ lap (up $ someD (rap envies (up $ everyD tb))) (rap listensTo girl4)

"Someone liking every short girl listens to Girl6" (inverse scope)
eeval $ llap (uup (rap (unit someD) (rrap (unit likes) (uup $ uunit $ everyD sg)))) (rrap (unit listensTo) (unit girl6))

"Some short boy pities someone who envies him" (Boy1 drops out)
eval $ lap (up $ someD sb) (rap pities (up $ someD (rap envies $ he 0)))

"Every short boy pities someone who envies him" (Boy1 drops out, or failure)
eval $ lap (up $ everyD sb) (rap pities (up $ someD (rap envies $ he 0)))

"Boy5's poem is long"
eeval $ llap (uup $ (up boy5) <$ poss $ poem) (rrap (unit long) (unit poem))

"Boy5's poem is owned by him"
eeval $ llap ((up boy5) <$ poss $ poem) (llap (unit poem) (rrap (unit ownedBy) (uunit $ he 0)))

"Every short boy's poem is short" (Boy1 drops out: narrowing)
eeval $ llap (uup $ (up $ everyD sb) <$ poss $ poem) (rrap (unit short) (unit poem))

"Every short boy envies a different tall boy"
eval $ lap (up $ everyD sb) (rap envies (up $ someD (rap different tb)))

"Every short boy envies a longer tall girl"
eval $ lap (up $ everyD sb) (rap envies (up $ someD (rap longer tg)))

"Every tall boy likes some tall girl" (functionalized)
let x = eval $ lap (up $ everyD' (rap tall boy)) (rap likes (up $ someD (rap tall girl))) in M.toList $ (unfunc . head . snd) (x!!5)


-- CROSSOVER
-- =========

-- moral of the story:
-- the simple algebraic llower (= join) still derives crossover facts, as long
-- as binding happens after lifting: "uup $ uunit", rather than "uunit $ up"
-- (see also the reset examples with binding)

"Herself likes some short girl" (presup failure w/ both llowers!)
eeval $ llap (uup $ unit $ he 0) (rrap (unit likes) (uup $ uunit $ someD sg))

"Herself likes some short girl" (presup failure only w/ complicated llower)
eeval $ llap (unit $ up $ he 0) (rrap (unit likes) (uunit $ up $ someD sg))

"A different tall boy pities every short boy" (inv scope)
-- with complicated llower, 'different' doesn't do anything in any of these sentences :(
-- but with simple llower, they all come out fine
eeval $ llap (uup $ unit $ someD (rap different tb)) (rrap (unit pities) (uup $ uunit $ everyD sb))
eeval $ llap (unit $ up $ someD (rap different tb)) (rrap (unit pities) (uup $ uunit $ everyD sb))
eeval $ llap (uup $ unit $ someD (rap different tb)) (rrap (unit pities) (uunit $ up $ everyD sb))
eeval $ llap (unit $ up $ someD (rap different tb)) (rrap (unit pities) (uunit $ up $ everyD sb))


-- This has nothing to do with crossover, but it might provide a clue:
--
-- with complicated llower, the first two sentences here end up with normal
-- funtional stacklists:
--   e.g. (True, [b3,g3,b2,g2,b1,g1])
-- but the latter two sentences end up with hourglass stacklists:
--   e.g. (True, [b3,b2,b1,g1,g2,g3])
eeval $ llap (unit $ up $ someD sb) (rrap (unit likes) (uup $ uunit $ everyD sg))
eeval $ llap (uup $ unit $ someD sb) (rrap (unit likes) (uup $ uunit $ everyD sg))
eeval $ llap (unit $ up $ someD sb) (rrap (unit likes) (uunit $ up $ everyD sg))
eeval $ llap (uup $ unit $ someD sb) (rrap (unit likes) (uunit $ up $ everyD sg))
-- with simple llower, all of the sentences are yield functional stacklists,
-- but the order of the pairs depends on the order of binding and lifting
--   e.g. (True, [b1,g1,b2,g2,b3,g3])
--   e.g. (True, [g1,b1,g2,b2,g3,b3])


-- RESET
-- =====

-- Type T sentences
-- ------------------------------------------------
-- returns False (equal to "Every short boy is a boy and pities b2")
eval $ conj (lap (up $ everyS' sb) boy) (lap (he 0) (rap pities boy2))
-- presupposition failure (equal to "Every short boy is a boy. He pities b2")
eeval $ conj (uunit $ reset $ lap (up $ everyS' sb) boy)  (llap (uunit $ he 0) (rrap (unit pities) (unit boy2)))
eeval $ conj (rreset2 $  llap (uup $ uunit $ everyS' sb) (unit boy))  (llap (uunit $ he 0) (rrap (unit pities) (unit boy2)))

-- returns False for b1 and b2, but True for b3
eval $ conj (lap (up $ someD sb) boy)  (lap (he 0) (rap pities boy2))
-- reset makes no difference; still False for b1 and b2, True for b3
eval $ conj (reset $ lap (up $ someD sb) boy)  (lap (he 0) (rap pities boy2))
-- ------------------------------------------------

-- Type E universal descriptions
-- ------------------------------------------------
-- reset universal E-type DPs results in sum individuals
eval $ up $ reset $ everyD sb
-- ------------------------------------------------

-- Type E universal > indefinite descriptions
-- ------------------------------------------------
-- when the indefinite controls the referent, then the indefinite variables
-- get summed, in this case the likers
eeval $ uup $ reset $ rap (unit someD) (rrap (unit likes) (uup (uunit $ everyD sb)))
eeval $ uup $ rreset2 $ rap (unit someD) (rrap (unit likes) (uup (uunit $ everyD sb)))

-- for some reason, resets don't effectively kill off "everyS'"'s binding
-- potential in these inverse linking cases, unless either
--   (i) "everyS'" is bound below its "uunit" (which is generally bad)
--   (ii) the whole host DP is lowered first
eeval $ uup $ rreset2 $ rap (unit someD) (rrap (unit likes) (uup $ uunit $ everyS' sb))
eeval $ uup $ rreset2 $ unit $ llower $ rap (unit someD) (rrap (unit likes) (uup $ uunit $ everyS' sb))
-- -------------------------------------------------

-- Whole sentences with reset universal DPs
-- -------------------------------------------------
-- a plain universal DP, when reset, can satisfy a collective predicate
eval $ lap (up $ reset $ everyD (rap long poem)) (rap overwhelm girl1)
-- if not reset, it can't
eval $ lap (up $ everyD (rap long poem)) (rap overwhelm girl6)

-- when a universal is boxed without scope, there are options.
-- regular "reset" leaves the universal distributive
eeval $ llap (reset $ unit $ llower $ unit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))
-- the recursive rresets collectivize it
eeval $ llap (rreset $ unit $ llower $ unit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))
eeval $ llap (altrreset $ unit $ llower $ unit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))
eeval $ llap ((liftM reset) $ unit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))

-- same options available to a universal with boxed with scope, except for
-- "liftM reset", which now leaves things distributive, like regular "reset",
-- if it isn't first llowered and boxed, like the others
eeval $ llap (reset $ unit $ llower $ uunit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))
eeval $ llap ((liftM reset) $ uunit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))
-- the other recursive rresets still collectivize
eeval $ llap ((liftM reset) $ unit $ llower $ uunit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))
eeval $ llap (rreset $ unit $ llower $ uunit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))
eeval $ llap (altrreset $ unit $ llower $ uunit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))

eeval $ llap (rr $ unit $ llower $ uunit $ everyD (rap long poem)) (rrap (unit overwhelm) (unit girl1))

-- -------------------------------------------------

-- Whole sentences with reset [universal > indefinite] DPs
-- -------------------------------------------------
-- w/o reset, "Someone liking every short boy listens to Girl6" (inversely
-- linked) returns True when the boys are assigned to themselves
eeval $ llap (uup $ rap (unit someD) (rrap (unit likes) (uup (uunit $ everyD sb)))) (rrap (unit listensTo) (unit girl6))
-- but when the subject is reset, it returns False for the same assignment,
-- because the likers have been summed!
eeval $ llap (uup $ rreset $ unit $ llower $ rap (unit someD) (rrap (unit likes) (uup (uunit $ everyD sb)))) (rrap (unit listensTo) (unit girl6))

-- other ways of resetting produce the same contrast as above.
-- regular "reset" and immediate "liftM reset" leave things distributive:
-- returns True for the identity assignment
eeval $ llap (uup $ reset $ unit $ llower $ rap (unit someD) (rrap (unit likes) (uup (uunit $ everyD sb)))) (rrap (unit listensTo) (unit girl6))
eeval $ llap (uup $ (liftM reset) $ rap (unit someD) (rrap (unit likes) (uup (uunit $ everyD sb)))) (rrap (unit listensTo) (unit girl6))
-- recursive resets collectivize:
-- returns False for the identity assignment
eeval $ llap (uup $ rreset $ unit $ llower $ rap (unit someD) (rrap (unit likes) (uup (uunit $ everyD sb)))) (rrap (unit listensTo) (unit girl6))
eeval $ llap (uup $ altrreset $ unit $ llower $ rap (unit someD) (rrap (unit likes) (uup (uunit $ everyD sb)))) (rrap (unit listensTo) (unit girl6))
eeval $ llap (uup $ (liftM reset) $ unit $ llower $ rap (unit someD) (rrap (unit likes) (uup (uunit $ everyD sb)))) (rrap (unit listensTo) (unit girl6))

-- obversely, "Someone liking every short boy overwhelm Girl6" (inversely
-- linked) returns False for all assignments, because overwhelm here is
-- collective in its subject
eeval $ llap (uup $ reset $ unit $ llower $ rap (unit someD) (llap (unit poem) (rrap (unit ownedBy) (uup (uunit $ everyD tb))))) (rrap (unit overwhelm) (unit girl1))
-- returns True when the boys are assigned to poems, because together +p4+p5+p6
-- overwhelm Girl1
eeval $ llap (uup $ reset $ rap (unit someD) (llap (unit poem) (rrap (unit ownedBy) (uup (uunit $ everyD tb))))) (rrap (unit overwhelm) (unit girl1))
-- ------------------------------------------------

-- Resets and binding
-- ------------------------------------------------
-- whether the atoms or the sum ends up on the stack depends on whether the
-- reset outscopes the push. the first DP here yeilds atom-stacks (which is
-- bad news, since "every" can't bind atoms out from under an aggregation).
-- the second DP yeilds sum-stacks, as it should
eval $ reset $ up $ everyD sb
eval $ up $ reset $ everyD sb
-- again, it looks like binding should follow all other operations on DPs
-- ------------------------------------------------

-}
