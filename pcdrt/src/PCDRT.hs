{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module PCDRT where

import Data.List
import Padded
import Control.Monad (guard)

-- entities are names
type Ent = String
-- two variables, U and V
data Var = U | V  deriving (Eq, Enum, Ord)
--  assignments of variables to entities
type Asmnt = Var -> Ent
-- info states are sets of assignment functions
type InfS = [Asmnt]
-- updates are relations on info states
type Update = InfS -> InfS -> Bool

-- fancy printer for an assignment function
instance Show Asmnt where
  show g = "[u := " ++ show (g U) ++ ", v := " ++ show (g V) ++ "]"

-- assignments equal if they're equal at every variable
instance Eq Asmnt where
  g == h = all (\d -> g d == h d) vars

------------------------------------------------------------------------------
-- Auxiliary Functions
------------------------------------------------------------------------------
-- mereological inclusion
sub, propSub :: [Ent] -> [Ent] -> Bool
xs `sub` ys = all (`elem` ys) xs
x `propSub` y = x `sub` y  &&  x /= y

-- check whether an update is true at particular inputs/outputs
-- (and print the answer together with displays of those assignments)
eval :: Update -> [Int] -> [Int] -> [String]
eval m is js = show (m (map snd gs) (map snd hs)) : trunk trans
  where (gs, hs) = ([(i, asmnts!!i) | i <- is], [(j, asmnts!!j) | j <- js])
        trans = (\g h -> g ++ " > " ++ h) <$> (pad gs) <*> (pad hs)
        pad as = map show as :-  "                        "

-- run an update at a given input (the ith assigment) and show all possible
-- outputs
outs :: Update -> [Int] -> IO ()
outs m is = sequence_ . intersperse (putStrLn "") $ do
  js <- subsequences (zip [0..] asmnts)
  guard $ m (map (asmnts!!) is) (map snd js)
  return $ mapM_ putStrLn $ tail $ eval m is (map fst js)

------------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------------
-- domain of atomic individuals
dom :: [Ent]
dom = ["J", "M", "B"]

-- stock of variables
vars :: [Var]
vars = [U, V]

-- all possible assignments
asmnts :: [Asmnt]
asmnts = [\x -> if x == U then d else d' | d <- dom, d' <- dom]

-- a single binary atomic relation
saw' :: [(Ent, Ent)]
saw' = [("J", "J"), ("J", "M"), ("J", "B"), ("M", "B")]
-- saw' = [("J", "J"), ("M", "M"), ("B", "B")]

------------------------------------------------------------------------------
-- Dynamic Lexicon
------------------------------------------------------------------------------
-- g[x]h
switch1 :: Var -> Asmnt -> Asmnt -> Bool
switch1 x = \g h -> h `elem` (g `savefor` x)
  where savefor g x = [\y -> if y == x then d else g y | d <- dom]

switch :: Var -> Update
switch x = \gs hs -> 
  all (\g -> any (\h -> switch1 x g h) hs) gs  &&
  all (\h -> any (\g -> switch1 x g h) gs) hs

-- g ; h
conj :: Update -> Update -> Update
left `conj` right =
  \gs hs -> any (\ks -> gs `left` ks  &&  ks `right` hs) (subsequences asmnts)

-- single cumulative binary predicate
saw :: Var -> Var -> Update
x `saw` y =
  \gs hs -> gs == hs && all (\h -> (h x, h y) `elem` saw') hs

