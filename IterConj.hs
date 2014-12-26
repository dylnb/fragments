{-# LANGUAGE FlexibleInstances #-}

module IterConj where

-- an implementation of the monadic denotational semantics for distributive
-- universal quantifiers described in Bumford 2014: "Iterated conjunction and
-- the dynamics of pair-list phenomena" and Bumford (ms): "Universal
-- quantification as iterated polymorphic dynamic conjunction"

import Model
import ContStateList
import Control.Monad.Cont
import Control.Monad.State
-- import Data.List.Split (chunksOf)
-- import qualified Data.Map as M
-- import Data.Maybe (mapMaybe)


-- CONNECTIVES
-- ================================================

-- Conjunction
-- ------------------------------------------------
-- polymorphic conjunction: conjoins booleans, fuses individuals

class Fusable a where
  fuse :: a -> a -> a
instance Fusable Bool where
  fuse = (&&)
instance Fusable Ent where
  fuse = oplus
instance Fusable Int where
  fuse = (*)
instance (Monad m, Fusable a) => Fusable (m a) where
  fuse = liftM2 fuse
-- ------------------------------------------------

-- ADJECTIVES
-- ================================================

-- Adjectives of Comparison
-- ------------------------------------------------
-- properties of individuals that stand in certain relations to other
-- individuals

-- 'diff' and 'longr' target specific ranges of the stack
_diff, _longr :: (Ent -> Bool) -> D ((Ent -> Bool) -> Ent -> Bool)
_diff comps = do s <- get
                 let s' = filter comps s
                 unit $ \p x -> p x && x `notElem` s'

_longr comps = do s <- get
                  unit $ \p x -> let s' = filter (fuse comps p) s in
                                 p x && (null s' || x > maximum s')

diff, longr :: (Ent -> Bool) -> K r ((Ent -> Bool) -> Ent -> Bool)
diff comps = lift (_diff comps)
longr comps = lift (_longr comps)

-- 'different' and 'longer' are convenience versions of 'diff'and 'longr' that
-- target the entire stack
_different, _longer :: D ((Ent -> Bool) -> Ent -> Bool)
_different = _diff (const True)
_longer    = _longr (const True)

different, longer :: K r ((Ent -> Bool) -> Ent -> Bool)
different = lift _different
longer    = lift _longer
-- ------------------------------------------------


-- DETERMINERS
-- ===========

-- Auxiliary functions for working with restrictors
-- ------------------------------------------------
-- collect a set of the individuals satisfying some property p (at a stack s),
-- along with the side effects that evaluation of (p x) may have introduced:
--   = [ (\s'' -> [(x, s'' + (s' - s))])  |  any fst (p x s) ]
bottle :: ET Bool -> Stack -> [D Ent]
bottle p s = do x <- domAtoms
                guard $ any fst (run s $ check x)
                let dx = mfilter id (check x) --@ \_ -> unit x
                return dx
  where check x = lower $ p ~/~ pure x
-- ------------------------------------------------

-- Universals
-- ------------------------------------------------
-- bottle up the restrictor into a set of stateful individuals;
-- pass each one through the continuation, then fold up the resulting stateful
-- functions with 'mtimes', a polymorphic dynamic conjunction operator
everyD :: Fusable r => ET Bool -> E r
everyD p = ContT $ \k -> do s <- get
                            let ms = [m --@ k | m <- bottle p s]
                            foldl1 fuse ms

-- externally static version of everyD;
-- performs the iterated update, and then resets the stack to what its
-- initial configuration
everyS :: Fusable r => ET Bool -> E r
everyS p = ContT $ \k -> do s <- get
                            let m = runContT (everyD p) k
                            withStateT (const s) m

-- externally static and deterministic version of everyD;
-- performs the iterated update, then evaluates the result to guarantee that
-- at least one thread of the fold came out true, and resets the stack
everyS' :: ET Bool -> E Bool
everyS' p = ContT $ \k -> StateT $ \s -> [(or $ evalStateT (runContT (everyD p) k) s, s)]



-- ==============
-- ** EXAMPLES **
-- ==============

{-

BASIC SENTENCES
===============

"Every tall boy likes some tall girl"
eval $ lap (up $ everyD tb) (rap likes (up $ some tg))

"Some tall girl likes every tall boy" [inverse scope]
eeval $ llap (uup $ pure $ some tg) (rrap (pure likes) (uup $ ppure $ everyD tb))

"Someone who envies every tall boy listens to Girl4"
eval $ lap (up $ some (rap envies (up $ everyD tb))) (rap listensTo g4)

"Someone liking every short girl listens to Girl6" [inverse scope]
eeval $ llap (uup (rap (pure some) (rrap (pure likes) (uup $ ppure $ everyD sg)))) (rrap (pure listensTo) (pure g6))

"Every short boy envies a different tall boy"
eval $ lap (up $ everyD sb) (rap envies (up $ some (rap different tb)))

"Every short boy envies a longer tall boy"
eval $ lap (up $ everyD sb) (rap envies (up $ some (rap longer tb)))

"A different tall boy pities every short boy" [inverse scope]
eeval $ llap (pure $ up $ some (rap different tb)) (rrap (pure pities) (ppure $ up $ everyD sb))


-- RESET
-- =====

-- Type T sentences
-- ------------------------------------------------
-- returns False (equal to "Every short boy is a boy and pities b2")
eval $ conj (lap (up $ everyS' sb) boy)  (lap (he 0) (rap pities boy2))
-- presupposition failure (equal to "Every short boy is a boy. He pities b2")
eval $ conj (reset $ lap (up $ everyS' sb) boy)  (lap (he 0) (rap pities boy2))

-- returns False for b1 and b2, but True for b3
eval $ conj (lap (up $ some sb) boy)  (lap (he 0) (rap pities boy2))
-- reset makes no difference; still False for b1 and b2, True for b3
eval $ conj (reset $ lap (up $ some sb) boy)  (lap (he 0) (rap pities boy2))
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
eval $ up $ reset $ llower $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))
-- "rreset" and "altrreset" can only apply to a universalish DP if it is first
-- lowered and then relifted; "liftM reset" can be, but it doesn't interact
-- with binding very well (individual likers always make it to the stack)
eeval $ uup $ rreset $ pure $ llower $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))
eeval $ uup $ altrreset $ pure $ llower $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))
eeval $ uup $ (liftM reset) $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))
-- -------------------------------------------------

-- Whole sentences with reset universal DPs
-- -------------------------------------------------
-- a plain universal DP, when reset, can satisfy a collective predicate
eval $ lap (up $ reset $ everyD (rap short poem)) (rap overwhelm girl6)
-- if not reset, it can't
eval $ lap (up $ everyD (rap short poem)) (rap overwhelm girl6)

-- when a universal is boxed without scope, there are options.
-- regular "reset" leaves the universal distributive
eeval $ llap (reset $ pure $ llower $ pure $ everyD (rap short poem)) (rrap (pure overwhelm) (pure girl6))
-- the recursive rresets collectivize it
eeval $ llap (rreset $ pure $ llower $ pure $ everyD (rap short poem)) (rrap (pure overwhelm) (pure girl6))
eeval $ llap (altrreset $ pure $ llower $ pure $ everyD (rap short poem)) (rrap (pure overwhelm) (pure girl6))
eeval $ llap ((liftM reset) $ pure $ everyD (rap short poem)) (rrap (pure overwhelm) (pure girl6))

-- same options available to a universal with boxed with scope, except for
-- "liftM reset", which now leaves things distributive, like regular "reset",
-- if it isn't first llowered and boxed, like the others
eeval $ llap (reset $ pure $ llower $ ppure $ everyD (rap short poem)) (rrap (pure overwhelm) (pure girl6))
eeval $ llap ((liftM reset) $ ppure $ everyD (rap short poem)) (rrap (pure overwhelm) (pure girl6))
-- the other recursive rresets still collectivize
eeval $ llap ((liftM reset) $ pure $ llower $ ppure $ everyD (rap short poem)) (rrap (pure overwhelm) (pure girl6))
eeval $ llap (rreset $ pure $ llower $ ppure $ everyD (rap short poem)) (rrap (pure overwhelm) (pure girl6))
eeval $ llap (altrreset $ pure $ llower $ ppure $ everyD (rap short poem)) (rrap (pure overwhelm) (pure girl6))



-- -------------------------------------------------

-- Whole sentences with reset [universal > indefinite] DPs
-- -------------------------------------------------
-- w/o reset, "Someone liking every short boy listens to Girl6" (inversely
-- linked) returns True when the boys are assigned to themselves
eeval $ llap (uup $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))) (rrap (pure listensTo) (pure girl6))
-- but when the subject is reset, it returns False for the same assignment,
-- because the likers have been summed!
eeval $ llap (uup $ rreset $ pure $ llower $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))) (rrap (pure listensTo) (pure girl6))

-- other ways of resetting produce the same contrast as above.
-- regular "reset" and immediate "liftM reset" leave things distributive:
-- returns True for the identity assignment
eeval $ llap (uup $ reset $ pure $ llower $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))) (rrap (pure listensTo) (pure girl6))
eeval $ llap (uup $ (liftM reset) $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))) (rrap (pure listensTo) (pure girl6))
-- recursive resets collectivize:
-- returns False for the identity assignment
eeval $ llap (uup $ rreset $ pure $ llower $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))) (rrap (pure listensTo) (pure girl6))
eeval $ llap (uup $ altrreset $ pure $ llower $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))) (rrap (pure listensTo) (pure girl6))
eeval $ llap (uup $ (liftM reset) $ pure $ llower $ rap (pure some) (rrap (pure likes) (uup (ppure $ everyD sb)))) (rrap (pure listensTo) (pure girl6))

-- obversely, "Someone liking every short boy overwhelm Girl6" (inversely
-- linked) returns False for all assignments, because overwhelm here is
-- collective in its subject
eeval $ llap (pure $ llower $ uup $ rap (pure some) (rrap (pure likes) (ppure (up $ everyD sb)))) (rrap (pure overwhelm) (pure girl6))
-- returns True when the boys are assigned to poems, because together +p1+p2+p3
-- overwhelm Girl6
eeval $ llap (rreset $ pure $ llower $ uup $ rap (pure some) (rrap (pure likes) (ppure (up $ everyD sb)))) (rrap (pure overwhelm) (pure girl6))
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
