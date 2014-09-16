module WModel where

data Ent = Atom (String,Int)
         | Plur {atoms :: [Ent]}
         -- | Func {unfunc :: M.Map Ent Stack}

data World = W -- just one world, for starters

instance Show Ent where
  show (Atom (x,y)) = x ++ show y
  show (Plur xs)    = foldl (\a b -> a ++ "+" ++ show b) "" xs

instance Eq Ent where
  (Atom x) == (Atom y)   = x == y
  (Plur xs) == (Plur ys) = xs == ys
  _ == _                 = False

instance Ord Ent where
  compare (Atom (_,tag)) (Atom (_,tag')) = compare tag tag'
  compare _ _                            = EQ



-- ===============
-- ** THE MODEL **
-- ===============

-- Entities
-- ================================================

-- Atomic Individuals
-- ------------------------------------------------
boys, girls, poems :: [Ent]
boys     = map (\x -> Atom ("b",x)) [1..6]
girls    = map (\x -> Atom ("g",x)) [1..6]
poems    = map (\x -> Atom ("p",x)) [1..6]

_b1, _b2, _b3, _b4, _b5, _b6 :: Ent
[_b1, _b2, _b3, _b4, _b5, _b6] = boys

_g1, _g2, _g3, _g4, _g5, _g6 :: Ent
[_g1, _g2, _g3, _g4, _g5, _g6] = girls

_p1, _p2, _p3, _p4, _p5, _p6 :: Ent
[_p1, _p2, _p3, _p4, _p5, _p6] = poems
-- ------------------------------------------------

-- Plural Individuals
-- ------------------------------------------------
shortboys, shortgirls, shortpoems :: Ent
shortboys  = Plur $ take 3 boys
shortgirls = Plur $ take 3 girls
shortpoems = Plur $ take 3 poems
-- ------------------------------------------------

-- The Domain
-- ------------------------------------------------
domAtoms, domPlurs, univ :: [Ent]
domAtoms = concat [boys, girls, poems]
domPlurs = [shortboys, shortgirls, shortpoems]
univ     = domAtoms ++ domPlurs

domWorlds :: [World]
domWorlds = [W]
-- ------------------------------------------------


-- Relations
-- ================================================

-- One-Place Relations
-- ------------------------------------------------
_boy, _girl, _poem, _thing :: World -> Ent -> Bool

_boy   = const (`elem` boys)
_girl  = const (`elem` girls)
_poem  = const (`elem` poems)
_thing = const $ const True
-- ------------------------------------------------

-- Two-Place Relations
-- ------------------------------------------------
_likes, _envies, _pities, _listensTo, _overwhelm :: World -> Ent -> Ent -> Bool

-- people like other people when their indices match:
-- b1 likes g1, g3 likes b3, but g5 doesn't like b4 or g4
_likes _ (Atom (x,n)) (Atom (y,m)) = n == m && y /= "p" && x /= "p"
_likes _ _ _                       = False

-- people envy people of the same gender that they are less than:
-- b1 envies b3, but b3 does not envy b1 nor does he envy g6
_envies _ (Atom (x,n)) (Atom (y,m)) = x == y && n > m
_envies _ _ _                       = False

-- people pity people that envy them:
-- b3 pities b1, but not g1, nor does b1 pity him
_pities _ (Atom (x,n)) (Atom (y,m)) = x == y && n < m
_pities _ _ _                       = False

-- people listen to people of the opposite gender that they divide evenly:
-- b2 listens to g6, as does b3, but b4 doesn't, and neither does g2
_listensTo _ (Atom (x,n)) (Atom (y,m)) = n `mod` m == 0 &&
                                         (x == "g" && y == "b"  ||
                                          x == "b" && y == "g")
_listensTo _ _ _                       = False

-- +p1+p2+p3 overwhelm g6, and +b1+b2+b3 overwhelm each of b1,b2, and b3;
-- nothing else overwhelms anyone else
_overwhelm _ y xs = xs == shortpoems && y == girls!!5 ||
                    xs == shortboys  && y `elem` take 3 boys
-- ------------------------------------------------

-- Three-Place Relations
-- ------------------------------------------------
_gave :: World -> Ent -> Ent -> Ent -> Bool
-- boys give girls poems in runs:
-- b1 gave g2 p3, and b4 gave g5 p6, but b1 didn't give g3 anything, and he
-- didn't give p4 to anybody
_gave _ (Atom (x,n)) (Atom (y,m)) (Atom (z,o)) = x == "g" && y == "p" &&
                                                 z == "b" && n == o+1 && m == n+1
_gave _ _ _ _                                  = False
-- ------------------------------------------------

-- More Relations
-- ------------------------------------------------
_of :: World -> (Ent -> Bool) -> Ent -> Ent -> Bool
-- approximates English 'of'. It takes two arguments, a noun and an individual
-- (the owner). So "poem `of_` b3" is the set of poems belonging to b3.
--
-- note that b1 doesn't have any poems.
_of _ p (Atom (_,n)) e@(Atom (y,m)) = p e && y == "p" && n == m && n /= 1
_of _ _ _ _                         = False

_short, _tall :: World -> (Ent -> Bool) -> Ent -> Bool
-- anything less than or equal to 3 is short
_short _ p e@(Atom (_,n)) = p e && n <= 3
_short _ _ _              = False

-- everything else is tall
_tall _ p e@(Atom (_,n)) = p e && n > 3
_tall _ _ _              = False
-- ------------------------------------------------


-- Functions
-- ================================================

-- Relational Nouns
-- ------------------------------------------------
_fav :: World -> (Ent -> Bool) -> Ent -> Ent
-- everybody's favorite blah is the blah that they match:
-- b2's favorite poem is p2, his favorite girl is g2, and his favorite boy is
-- himself
_fav _ nom (Atom (_,n)) = filter nom domAtoms !! (n-1)
_fav _ _ _              = _p1
