module SplitDefs where

import Grammar
import Control.Monad.State
import Data.List.Extra (allSame, groupSortOn)

---------------------------------------------------
-- Model ------------------------------------------
---------------------------------------------------

-- Individuals ------------------------------------

domain :: [E]
domain = ["John", "Mary", "Bill", "Thumper", "Bugs", "H1", "H2"]

-- One-place properties ---------------------------

predDomain :: [[E]]
predDomain = [boy', girl', rabbit', hat', brown']
boy' = ["John", "Bill"]
girl' = ["Mary"]
rabbit' = ["Thumper", "Bugs"]
hat' = ["H1", "H2"]
brown' = ["Thumper"]

-- Two-place properties ---------------------------

relDomain :: [[(E,E)]]
relDomain = [likes', inside']
likes' = [("J","B"), ("J","M"), ("B","M")]
inside' = [("Bugs", "H1")]

---------------------------------------------------
-- Language ---------------------------------------
---------------------------------------------------

-- Names ------------------------------------------

john, mary, bill, thumper, bugs, h1, h2 :: E
[john, mary, bill, thumper, bugs, h1, h2] = domain

-- Predicates -------------------------------------

boy, girl, rabbit, hat, brown :: E -> T
[boy, girl, rabbit, hat, brown] = map (\xs x -> x `elem` xs) predDomain

-- Relations --------------------------------------

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
          | null xs                      = error "existence failure"
          | allSame [s!!n | (_,s) <- xs] = xs
          | otherwise                    = error "uniqueness failure"

tallest :: Int -> F a
tallest n = mapStateT $ last . groupSortOn ((!!n) . snd)
