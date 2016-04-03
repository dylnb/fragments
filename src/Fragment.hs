module Fragment where

import Grammar
import Control.Monad.State
import IxCont
import Data.List.Extra hiding (lower)
import Control.Exception (assert)

-- ------------------------------------------------

domain :: [Ent]
domain = ["J", "M", "B", "F"]

-- ------------------------------------------------

john, mary :: E (D r)
john = return "J"
mary = return "M"

boy, girl :: ET (D r)
boy = return (\x -> x `elem` ["J", "B", "F"])
girl = return (\x -> x `elem` ["M"])

likes, is :: EET (D r)
likes = return (\x y -> (y,x) `elem` [("J","B"), ("J","M"), ("B","M")])
is = return (==)

-- ------------------------------------------------

_some :: (Ent -> D Bool) -> D Ent
_some p = do x <- lift domain
             p x >>= guard
             return x

some :: K (D Ent) (D Bool) Ent
some = ixcont _some

the :: Int -> F r -> K (D r) (D r) (K (D Ent) (D Bool) Ent)
the n t = ixcont $ \c -> unique n . t $ c (push some)

the' :: Int -> K (D r) (D r) (K (D Ent) (D Bool) Ent)
the' n = the n id

_every :: (Ent -> D Bool) -> E (D Bool)
_every p = ixcont $ \k -> _neg $ _some p >>= _neg . k

every :: K (E (D Bool)) (D Bool) Ent
every = ixcont _every

-- ------------------------------------------------

unique :: Int -> F a
unique n = mapStateT $ \xs -> assert (allSame [s!!n | (_,s) <- xs]) xs

tallest :: Int -> F a
tallest n = mapStateT $ last . groupSortOn ((!!n) . snd)

-- ------------------------------------------------

conj :: Monad m => m Bool -> m Bool -> m Bool
conj = liftM2 (&&)

disj :: MonadPlus m => m a -> m a -> m a
disj = mplus

_neg :: D Bool -> D Bool
_neg m = state $ \s -> (not . or $ evalStateT m s, s)

neg :: K (D r) (D r) (D Bool -> D Bool)
neg = return _neg

-- ------------------------------------------------

-- compare with _some above
who :: D Bool -> D a -> D a
who rc dp = do x <- dp
               rc >>= guard
               return x

_prn :: Int -> D Ent
_prn n = gets (!!n)

prn :: Int -> E (D r)
prn n = ixlift $ _prn n
