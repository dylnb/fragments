{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances #-}

import Control.Monad.Cont
import Control.Monad.State
import Data.List
import Control.Applicative ((<*>), (<$>), (<**>))
import Data.List.Split (chunksOf)
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
           | Func {unfunc :: M.Map Ent Stack} --deriving (Eq,Show)
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
  show (Plur xs)   = foldl (\a b -> a ++ "+" ++ show b) "" xs
  show _           = show "func"

instance Eq Ent where
  (Atom x) == (Atom y)     = x == y
  (Plur xs) == (Plur ys) = xs == ys
  _ == _                 = False

instance Ord Ent where
  compare (Atom (name,tag)) (Atom (name',tag')) = compare tag tag'
  compare _ _                                 = EQ



-- ========================
-- ** MONADIC OPERATIONS **
-- ========================

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

(</>)  = rap
(<//>) = rrap
(<\>)  = lap
(<\\>) = llap

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
rreset :: Kappa (Kappa a a) (Kappa a r) -> Kappa (Kappa a r) r'
rreset = lift . (`runContT` (return . reset))
-- equivalent to:
-- rreset mm = ContT $ \k -> do
--   x <- runContT mm (\m -> return (reset m))
--   k x

-- equivalent to first-order reset, but with an obligatorily higher type
rreset' :: Kappa (Kappa a r) (Kappa a r) -> Kappa (Kappa a r) r'
rreset' = reset

altrreset :: Kappa (Kappa a a) (Kappa a r) -> Kappa (Kappa a r) (Kappa a r)
altrreset = liftM reset
-- equivalent to:
-- altrreset m = do
--   x <- m
--   unit $ reset x

-- ===============
-- ** THE MODEL **
-- ===============

-- INDIVIDUALS
-- ===========

-- Atomic Individuals
boys, girls, poems :: Stack
boys     = map (\x -> Atom ("b",x)) [1..6]
girls    = map (\x -> Atom ("g",x)) [1..6]
poems    = map (\x -> Atom ("p",x)) [1..6]

-- Plural Individuals
shortboys, shortgirls, shortpoems :: Ent
shortboys  = Plur $ take 3 boys
shortgirls = Plur $ take 3 girls
shortpoems = Plur $ take 3 poems

-- The Domain
domAtoms, domPlurs, univ :: Stack
domAtoms = concat [boys, girls, poems]
domPlurs = [shortboys, shortgirls, shortpoems]
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
randogirls = msum $ map ((>> return True) . put) $
             map ($ permutations $ take 3 girls) [(!!0), (!!3), (!!4)]

stream2 :: Dstate Bool
stream2 = randogirls >> modify (concatMap (\(a,b) -> [a,b]) . zip boys)
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

-- people like other people when their indices match:
-- b1 likes g1, g3 likes b3, but g5 doesn't like b4 or g4
likes = let likes' (Atom (x,n)) (Atom (y,m)) = n == m
                                               && y /= "p" && x /= "p"
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

-- +p1+p2+p3 overwhelm g6, and +b1+b2+b3 overwhelm each of b1,b2, and b3;
-- nothing else overwhelms anyone else
overwhelm = let ow' y xs =
                  xs == shortpoems && y == girls!!5 ||
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
short, tall :: ETET r
short = let short' p e@(Atom (_,n)) = p e && n <= 3
            short' _ _              = False in
        unit short'

tall = let tall' p e@(Atom (_,n)) = p e && n > 3
           tall' _ _              = False in
       unit tall'

-- Accumulating Adjectives
-- ------------------------------------------------
different, longer :: ETET r
different = ContT $ \k -> do {s <- get; k (\p x -> p x && x `notElem` s)}

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
-- 'ownedBy' approximates English 'of'. It takes two arguments, a nominal
-- and an individual (the owner). So "book ownedby Boy3" is the set of books
-- that Boy3 owns. As it happens, Boy1 doesn't own any poems.
ownedBy :: Kappa ((Ent -> Bool) -> Ent -> Ent -> Bool) r
ownedBy = let ownedBy' p (Atom (x,n)) e@(Atom (y,m)) =
                p e && y == "p" && n == m && n /= 1
              ownedBy' _ _ _i                        = False in
          unit ownedBy'


-- CONNECTIVES
-- ===========

class Fusable a where
  fuse :: a -> a -> a
instance Fusable Bool where
  fuse = (&&)
instance Fusable Ent where
  fuse = oplus

conj :: (Monad m, Fusable r) => m r -> m r -> m r
conj = liftM2 fuse


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
--   let xs =  charact p
--   let ps = map (k =<<) xs
--   foldl1 mplus ps
--   -- equivalent to:
--   -- (msum xs) >>= k
-- ------------------------------------------------
 
-- Universals
-- ------------------------------------------------
everyD :: Fusable r => ET Bool -> E r
everyD p = ContT $ \k -> do
  let xs = filter (not . null . run) $
           -- flushes out individuals that completely fail the restrictor, 
           -- but explodes if the restrictor contains pronouns :(
           charact p
  let ps = filter (not . null . run) $
           -- the line above protects the computation against scope failure, 
           -- as in "Every short boy likes someone he pities", which will
           -- otherwise fail on Boy1 who doesn't pity anyone. Comment this
           -- line out off to get a more presupposition-failure like semantics
           map (k =<<) xs
  foldl1 conj ps

-- a towerish version of everyD
-- shows slightly different behavior when "different" is in a restrictor
alteveryD :: ET Bool -> E Bool
alteveryD p = ContT $ \k -> StateT $ \s ->
  let witnesses x = filter fst $ runStateT (check p x) s in
  let ps = filter (not . null . (`runStateT` s)) $
           map (\x -> StateT $ \s' -> concat $ [runStateT (k x) (s'++(s'' `minus` s))
                                                 | (_,s'') <- witnesses x]) domAtoms in
  runStateT (foldl1 conj ps) s

-- externally static version of everyD
everyS' :: ET Bool -> E Bool
everyS' = mapContT (\m -> do {s <- get; mapStateT (\ts -> [(any fst ts, s)]) m}) . everyD
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
poss g p = rap (unit someD) (rrap (llap (unit p) (unit ownedBy)) (uunit g))
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
eval $ (up boy4) <\> tb

"Some tall boy likes some tall girl"
eval $ (up $ someD tb) <\> (likes </> (up $ someD tg))

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

"Every short boy pities someone who envies him" (Boy1 drops out, or presup failure)
eval $ lap (up $ everyD sb) (rap pities (up $ someD (rap envies $ he 0)))

"Boy2's poem is short"
eeval $ llap (uup $ (up boy2) <$ poss $ poem) (rrap (unit short) (unit poem))

"Boy2's poem is owned by him"
eeval $ llap ((up boy2) <$ poss $ poem) (rrap (llap (unit poem) (unit ownedBy)) (uunit $ he 0))

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
eeval $ llap (uup $ unit $ someD (rap different tb)) (rrap (unit pities) (uup $ uunit $ everyD sb))
eeval $ llap (unit $ up $ someD (rap different tb)) (rrap (unit pities) (uup $ uunit $ everyD sb))
eeval $ llap (uup $ unit $ someD (rap different tb)) (rrap (unit envies) (uunit $ up $ everyD sb))
eeval $ llap (unit $ up $ someD (rap different tb)) (rrap (unit envies) (uunit $ up $ everyD sb))
-- but with simple llower, the first two sentences work perfectly :)
-- again, "uup $ uunit" is better than "uunit $ up"


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
eval $ conj (lap (up $ everyS' sb) boy)  (lap (he 0) (rap pities boy2))
-- presupposition failure (equal to "Every short boy is a boy. He pities b2")
eval $ conj (reset $ lap (up $ everyS' sb) boy)  (lap (he 0) (rap pities boy2))

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
eval $ reset $ llower $ uup $ rap (unit someD) (rrap (unit likes) (uunit (up $ everyD sb)))
-- "rreset" can only apply to a universalish DP if it is first lowered
-- and relifted
eeval $ rreset $ unit $ llower $ uup $ rap (unit someD) (rrap (unit likes) (uunit (up $ everyD sb)))
-- -------------------------------------------------

-- Whole sentences with reset universal DPs
-- -------------------------------------------------
-- a plain universal DP, when reset, can satisfy a collective predicate
eval $ lap (reset $ up $ everyD (rap short poem)) (rap overwhelm girl6)
-- if not reset, it can't
eval $ lap (up $ everyD (rap short poem)) (rap overwhelm girl6)
-- even when double-lifted, resetting the universal DP glues it together
eeval $ llap (rreset $ unit $ llower $ unit $ everyD (rap short poem)) (rrap (unit overwhelm) (unit girl6))
-- no matter how it's reset
eval $ lap (reset $ llower $ unit $ everyD (rap short poem)) (rap overwhelm girl6)
-- or how it scopes
eval $ lap (reset $ llower $ uunit $ everyD (rap short poem)) (rap overwhelm girl6)
-- -------------------------------------------------

-- Whole sentences with reset [universal > indefinite] DPs
-- -------------------------------------------------
-- w/o reset, "Someone liking every short boy listens to Girl6" (inversely
-- linked) returns True when the boys are assigned to themselves
eeval $ llap (unit $ llower $ uup $ rap (unit someD) (rrap (unit likes) (uunit (up $ everyD sb)))) (rrap (unit listensTo) (unit girl6))
-- but when the subject is reset, it returns False for the same assignment,
-- because the likers have been summed!
eeval $ llap (rreset $ unit $ llower $ uup $ rap (unit someD) (rrap (unit likes) (uunit (up $ everyD sb)))) (rrap (unit listensTo) (unit girl6))

-- lowering before resetting produces the same contrast
-- returns True for the identity assignment
eval $ lap (llower $ uup $ rap (unit someD) (rrap (unit likes) (uunit (up $ everyD sb)))) (rap listensTo girl6)
-- returns False for the identity assignment
eval $ lap (reset $ llower $ uup $ rap (unit someD) (rrap (unit likes) (uunit (up $ everyD sb)))) (rap listensTo girl6)

-- in contrast, "Someone liking every short boy overwhelm Girl6" (inversely
-- linked) returns False for all assignments, because overwhelm here is
-- collective in its subject
eeval $ llap (unit $ llower $ uup $ rap (unit someD) (rrap (unit likes) (uunit (up $ everyD sb)))) (rrap (unit overwhelm) (unit girl6))
-- returns True when the boys are assigned to poems, because together +p1+p2+p3
-- overwhelm Girl6
eeval $ llap (rreset $ unit $ llower $ uup $ rap (unit someD) (rrap (unit likes) (uunit (up $ everyD sb)))) (rrap (unit overwhelm) (unit girl6))
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
