{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module MaxMax where

import Data.List
import Data.Maybe

type Atom = String
newtype Ent = Ent [Atom] deriving (Eq)
data Var = U | V  deriving (Eq, Enum, Ord)
type InfS = Var -> Ent
type Update = InfS -> InfS -> Bool

instance Show InfS where
  show g = "[u := " ++ show gu ++ ", v := " ++ show gv ++ "]"
    where (gu, gv) = (g U, g V)

instance Eq InfS where
  g == h = all (\d -> g d == h d) vars

instance Enum InfS where
  toEnum n | n < 49    = funcs !! n
           | otherwise = error "InfS.toEnum: bad argument"

  fromEnum g = fromMaybe err (elemIndex g funcs)
    where err = error "InfS.fromEnum: bad argument"
  
instance Show Ent where
  show (Ent xs) = intercalate "+" xs

sub, propSub :: Ent -> Ent -> Bool
(Ent xs) `sub` (Ent ys) = all (`elem` ys) xs
x `propSub` y = x `sub` y  &&  x /= y

atoms :: [Atom]
atoms = ["J", "M", "B"]

dom :: [Ent]
dom = map Ent . tail . subsequences $ atoms

vars :: [Var]
vars = [U, V]

funcs :: [InfS]
funcs = [\x -> if x == U then d else d' | d <- dom, d' <- dom]

eval :: Update -> Int -> Int -> String
eval m i j = show (m g h) ++ ", " ++ show g ++ " --> " ++ show h
  where (g, h) = (funcs !! i, funcs !! j)

outs :: Update -> Int -> IO ()
outs m i = sequence_ [display h j | (h, j) <- zip funcs [0..], m g h]
  where g = funcs !! i
        display h j = putStrLn $ show j ++ ": " ++ show h

switch :: Var -> Update
switch x = \g h -> h `elem` (g `savefor` x)
  where savefor g x = [\y -> if y == x then d else g y | d <- dom]

conj :: Update -> Update -> Update
left `conj` right = \g h -> any (\k -> g `left` k  &&  k `right` h) funcs

maxB :: Var -> Update -> Update
maxB x body = \g h -> g `pos` h  &&  g `neg` h
  where pos = switch x `conj` body
        neg g h = not $ any (\h' -> h x `propSub` h' x  &&  g `pos` h') funcs

saw :: Var -> Var -> Update
x `saw` y = \g h ->
  let Ent xs = h x
      Ent ys = h y
      saw' = [("J", "J"), ("M", "M"), ("B", "B")]
  in
      g == h  &&
      h x `sub` Ent [d | (d,e) <- saw', e `elem` ys]  &&
      h y `sub` Ent [e | (d,e) <- saw', d `elem` xs]

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

-- outs senConj1 0
-- 0: [u := J, v := J]
-- 1: [u := J, v := M]
-- 2: [u := J, v := J+M]
-- 3: [u := J, v := B]
-- 4: [u := J, v := J+B]
-- 5: [u := J, v := M+B]
-- 6: [u := J, v := J+M+B]
--
-- outs senConj2 0
-- 0: [u := J, v := J]

senMaxU, senMaxV :: Update
senMaxU = maxB U senSaw
senMaxV = maxB V senSaw

-- outs senMaxU 0
-- 0: [u := J, v := J]
--
-- outs senMaxV 0
-- 0: [u := J, v := J]

senMaxMaxUV, senMaxMaxVU :: Update
senMaxMaxUV = maxB U (maxB V senSaw)
senMaxMaxVU = maxB V (maxB U senSaw)

-- outs senMaxMaxUV 0
-- 48: [u := J+M+B, v := J+M+B]
-- 
-- outs senMaxMaxVU 0
-- 48: [u := J+M+B, v := J+M+B]
