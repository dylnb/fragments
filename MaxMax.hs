{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module MaxMax where

import Data.List
import Data.Maybe

type Atom = String
-- entities are sums (lists) of atoms
newtype Ent = Ent [Atom] deriving (Eq)
-- two variables, U and V
data Var = U | V  deriving (Eq, Enum, Ord)
-- info states are assignment functions
type InfS = Var -> Ent
-- updates are relations on assignments
type Update = InfS -> InfS -> Bool

-- fancy printer for an assignment function
instance Show InfS where
  show g = "[u := " ++ show (g U) ++ ", v := " ++ show (g V) ++ "]"

-- assignments equal if they're equal at every variable
instance Eq InfS where
  g == h = all (\d -> g d == h d) vars
  
-- fancy printer for sum individuals
instance Show Ent where
  show (Ent xs) = intercalate "+" xs

------------------------------------------------------------------------------
-- Auxiliary Functions
------------------------------------------------------------------------------
-- set inclusion
sub, propSub :: Ent -> Ent -> Bool
(Ent xs) `sub` (Ent ys) = all (`elem` ys) xs
x `propSub` y = x `sub` y  &&  x /= y

-- check whether an update is true at the ith and jth assignments
-- (and print the answer together with displays of those assignments)
eval :: Update -> Int -> Int -> String
eval m i j = show (m g h) ++ ", " ++ show g ++ " --> " ++ show h
  where (g, h) = (funcs !! i, funcs !! j)

-- run an update at a given input (the ith assigment) and show all possible
-- outputs
outs :: Update -> Int -> IO ()
outs m i = sequence_ [display h j | (h, j) <- zip funcs [0..], m g h]
  where g = funcs !! i
        display h j = putStrLn $ show j ++ ": " ++ show h

------------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------------
-- domain of atomic individuals
atoms :: [Atom]
atoms = ["J", "M", "B"]

-- domain of sum individuals
dom :: [Ent]
dom = map Ent . tail . subsequences $ atoms

-- stock of variables
vars :: [Var]
vars = [U, V]

-- all possible assignments
funcs :: [InfS]
funcs = [\x -> if x == U then d else d' | d <- dom, d' <- dom]

-- a single binary atomic relation
saw' :: [(Atom, Atom)]
saw' = [("J", "J"), ("J", "M"), ("J", "B"), ("M", "B")]
-- saw' = [("J", "J"), ("M", "M"), ("B", "B")]

------------------------------------------------------------------------------
-- Dynamic Lexicon
------------------------------------------------------------------------------
-- g[x]h
switch :: Var -> Update
switch x = \g h -> h `elem` (g `savefor` x)
  where savefor g x = [\y -> if y == x then d else g y | d <- dom]

-- g ; h
conj :: Update -> Update -> Update
left `conj` right = \g h -> any (\k -> g `left` k  &&  k `right` h) funcs

-- max_x (body)
maxB :: Var -> Update -> Update
maxB x body = \g h -> g `pos` h  &&  g `neg` h
  where pos = switch x `conj` body
        neg g h = not $ any (\h' -> h x `propSub` h' x  &&  g `pos` h') funcs
        -- neg g h = all (\h' -> h' x `sub` h x  ||  not (g `pos` h')) funcs

-- single cumulative binary predicate
saw :: Var -> Var -> Update
x `saw` y = \g h ->
  let (Ent xs, Ent ys) = (h x, h y) in
  g == h  &&  h x `sub` Ent [d | (d,e) <- saw', e `elem` ys]  &&
              h y `sub` Ent [e | (d,e) <- saw', d `elem` xs]


------------------------------------------------------------------------------
-- Example Formulas
------------------------------------------------------------------------------
senSaw :: Update
senSaw = U `saw` V

-- outs senSaw 0
-- 0: [u := J, v := J]

senSwitchV :: Update
senSwitchV = switch V

-- outs senSwitchV 0
-- 0: [u := J, v := J]
-- 1: [u := J, v := M]
-- 2: [u := J, v := J+M]
-- 3: [u := J, v := B]
-- 4: [u := J, v := J+B]
-- 5: [u := J, v := M+B]
-- 6: [u := J, v := J+M+B]

senConj1, senConj2 :: Update
senConj1 = senSaw `conj` senSwitchV
senConj2 = senSwitchV `conj` senSaw

-- outs senConj1 10
-- 7: [u := M, v := J]
-- 8: [u := M, v := M]
-- 9: [u := M, v := J+M]
-- 10: [u := M, v := B]
-- 11: [u := M, v := J+B]
-- 12: [u := M, v := M+B]
-- 13: [u := M, v := J+M+B]
--
-- outs senConj2 10
-- 10: [u := M, v := B]

senMaxU, senMaxV :: Update
senMaxU = maxB U senSaw
senMaxV = maxB V senSaw

-- outs senMaxU 6
-- 20: [u := J+M, v := J+M+B]
--
-- outs senMaxV 0
-- 0: [u := J, v := J+M+B]

senMaxMaxUV, senMaxMaxVU :: Update
senMaxMaxUV = maxB U (maxB V senSaw)
senMaxMaxVU = maxB V (maxB U senSaw)

-- outs senMaxMaxUV 0
-- 20: [u := J+M, v := J+M+B]
-- 
-- outs senMaxMaxVU 0
-- 20: [u := J+M, v := J+M+B]

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- two formulas (equivalently) representing
-- the `neg` component of senMaxMaxUV, for testing
test1 :: Update
test1 g h =
  none (\j -> -- there's no j s.t.
    h U `propSub` j U  && -- h u < j u  &  s.t.
    some (\k -> -- there's a k s.t.
      switch U g k  &&  switch V k j  &&  saw U V j j  && -- g[u]k & k[v]j & (saw u v) j j &
        none (\j' -> j V `propSub` j' V && switch V k j' && saw U V j' j'))) -- there's no j' s.t. j v < j' v & k[v]j' & (saw u v) j' j'
  where none = not . some
        some = flip any funcs

test2 :: Update
test2 g h =
  every (\j -> -- forall j
    every (\k -> -- forall k
      not (h U `propSub` j U && switch U g k && switch V k j && saw U V j j)  || -- (h u < j u & g[u]k & k[v]j & (saw u v) j j) =>
      some (\j' -> -- there's a j' s.t.
        j V `propSub` j' V && switch V k j' && saw U V j' j'))) -- j v < j' v & k[v]j' & (saw u v) j' j'
  where every = flip all funcs
        none = not . some
        some = flip any funcs
