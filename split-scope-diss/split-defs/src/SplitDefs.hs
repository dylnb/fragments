module SplitDefs where

import Grammar
import Control.Monad.State
import Data.List.Extra (allSame, groupSortOn)

---------------------------------------------------
-- Model ------------------------------------------
---------------------------------------------------

-- Individuals ------------------------------------

domain :: [E]
domain = [john', mary', bill', thumper', bugs', h1', h2']
john' = "John"
mary' = "Mary"
bill' = "Bill"
thumper' = "Thumper"
bugs' = "Bugs"
h1' = "H1"
h2' = "H2"

-- Properties -------------------------------------

predDomain :: [[E]]
predDomain = [boy', girl', rabbit', hat', brown']
boy' = [john', bill']
girl' = [mary']
rabbit' = [thumper', bugs']
hat' = [h1', h2']
brown' = [thumper']

-- Relations -------------------------------------

relDomain :: [[(E,E)]]
relDomain = [likes', inside']
likes' = [(john', bill'), (john', mary'), (bill', mary')]
inside' = [(bugs', h1')]

---------------------------------------------------
-- Language ---------------------------------------
---------------------------------------------------

-- Names ------------------------------------------

john, mary, bill, thumper, bugs, h1, h2 :: E
[john, mary, bill, thumper, bugs, h1, h2] = domain

-- One-place predicates ---------------------------

boy, girl, rabbit, hat, brown :: E -> T
[boy, girl, rabbit, hat, brown] = map (\xs x -> x `elem` xs) predDomain

-- Two-place predicates ---------------------------

likes, inside :: E -> E -> T
[likes, inside] = map (\rel x y -> (y,x) `elem` rel) relDomain

-- Determiners ------------------------------------

some :: K (K (D r) (D r) E) (D T) E
some = Tower $ \p -> Tower $ \k -> some' p >>= k
  where some' :: (E -> D T) -> D E
        some' p = do x <- lift domain
                     p x >>= guard
                     state $ \s -> (x, s++[x])

the :: Int -> F r' -> K (D r') (D r') (K (K (D r) (D r) E) (D T) E)
the n t = Tower $ \c -> unique n . t $ c some
the' n = the n id

-- Quantificational adjectives --------------------

unique :: Int -> F a
unique n = mapStateT exactlyOne
  where exactlyOne xs
          | null xs                      = errorWithoutStackTrace "existence failure"
          | allSame [s!!n | (_,s) <- xs] = xs
          | otherwise                    = errorWithoutStackTrace "uniqueness failure"

biggest :: Int -> F a
biggest n = mapStateT $ last . groupSortOn ((!!n) . snd)
