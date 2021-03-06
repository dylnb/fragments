{-# LANGUAGE FlexibleContexts #-}

module Main where

import Grammar
import SplitDefs
import Control.Monad.State
import Control.Exception (ErrorCall(..), handle)

---------------------------------------------------
-- To show results of evaluating expressions ------
---------------------------------------------------

-- Run an update in a default (empty context) -----
run :: D b -> [(b, Stack)]
run m = runStateT m []

-- Pass in final continuation and run -------------
evl :: (Low (D b) o a) => K (D b) o a -> [(b, Stack)]
evl = run . lowr

---------------------------------------------------
-- Expressions generated by the fragment ----------
---------------------------------------------------

main :: IO ()
main = do
  -- test suite
  putStr "\nTesting..."

  -- print truth/false/failure value for expressions
  mapM_ (handle (\(ErrorCall e) -> putStrLn e))

    [ putStrLn ""

    , putStrLn "\n-- some hat"
    , let somehat :: [(E, Stack)]
          somehat = evl $ lowr $ some ~\~ u hat
      in print somehat

    , putStrLn "\n-- some girl"
    , let somegirl :: [(E, Stack)]
          somegirl = evl $ lowr $ some ~\~ u girl
      in print somegirl

      -- too many hats; should be uniqueness failure
    , putStrLn "\n-- the hat"
    , let thehat :: [(E, Stack)]
          thehat = evl $ ilowr (the' 0 ~\~ uu hat)
      in print thehat

     -- should be the same as "some girl"
    , putStrLn "\n-- the girl"
    , let thegirl :: [(E, Stack)]
          thegirl = evl $ ilowr (the' 0 ~\~ uu girl)
      in print thegirl

      -- should be true
    , putStrLn "\n-- some hat is a hat"
    , let sen :: [(T, Stack)]
          sen = evl $ lowr (some ~\~ u hat) ~\~ u hat
      in print sen

      -- should be uniqueness failure
    , putStrLn "\n-- the hat is a hat"
    , let thehat :: K (D r) (D r) E
          thehat = reset $ ilowr (the' 0 ~\~ uu hat)
          sen :: [(T, Stack)]
          sen = evl $ thehat ~\~ u hat
      in print sen

      -- should be true
    , putStrLn "\n-- the girl is a girl"
    , let thegirl :: K (D r) (D r) E
          thegirl = reset $ ilowr (the' 0 ~\~ uu girl)
          sen :: [(T, Stack)]
          sen = evl $ thegirl ~\~ u girl
      in print sen

      -- should be true
    , putStrLn "\n-- john likes the girl"
    , let thegirl :: K (D r) (D r) E
          thegirl = reset $ ilowr (the' 0 ~\~ uu girl)
          sen :: [(T, Stack)]
          sen = evl $ u john ~\~ (u likes ~/~ thegirl)
      in print sen

      -- should be failure
    , putStrLn "\n-- the rabbit in the hat (absolute)"
    , let thehat :: K (D r') (D r') (K (D r) (D r) E)
          thehat = u $ reset $ ilowr (the' 0 ~\~ uu hat)
          trith :: [(E, Stack)]
          trith = evl $ ilowr (the' 1 ~\~ (uu rabbit ~|~ (uu inside ~/~ thehat)))
      in print trith

      -- should be bugs (with H1 on the stack)
    , putStrLn "\n-- the rabbit in the hat (relative)"
    , let thehat :: K (D r') (D r') (K (D r) (D r) E)
          thehat = ilowr (the' 0 ~\~ uu hat)
          trith :: [(E, Stack)]
          trith = evl $ ilowr (the' 1 ~\~ (uu rabbit ~|~ (uu inside ~/~ thehat)))
      in print trith

      -- should be false
    , putStrLn "\n-- the rabbit in the hat (relative) is brown"
    , let thehat :: K (D r') (D r') (K (D r) (D r) E)
          thehat = ilowr (the' 0 ~\~ uu hat)
          sen :: [(T, Stack)]
          sen = evl $ ilowr (the' 1 ~\~ (uu rabbit ~|~ (uu inside ~/~ thehat))) ~\~ uu brown
      in print sen

      -- should be H2
    , putStrLn "\n-- the biggest hat"
    , let tbh :: [(E, Stack)]
          tbh = evl $ ilowr (the 0 (biggest 0) ~\~ uu hat)
      in print tbh

      -- should be [] (because there are no rabbits in H2)
    , putStrLn "\n-- the rabbit in the biggest hat (absolute)"
    , let tbh :: K (D r') (D r') (K (D r) (D r) E)
          tbh = u $ reset $ ilowr (the 0 (biggest 0) ~\~ uu hat)
          tritbh :: [(E, Stack)]
          tritbh = evl $ ilowr (the' 1 ~\~ (uu rabbit ~|~ (uu inside ~/~ tbh)))
      in print tritbh

    -- should be bugs (with H1 on the stack)
    , putStrLn "\n-- the rabbit in the biggest hat (relative)"
    , let ttr :: K (D r') (D r') (K (D r) (D r) E)
          ttr = ilowr (the 0 (biggest 0) ~\~ uu hat)
          tritbh :: [(E, Stack)]
          tritbh = evl $ ilowr (the' 1 ~\~ (uu rabbit ~|~ (uu inside ~/~ ttr)))
      in print tritbh

    ]

  -- end test suite
  putStrLn ""

-- ----------------------------------------------------- 

-- evaluate :: K (D a) (D b) b -> [(a, Stack)]
-- evaluate = run . lower

-- eval :: LowersTo m (D b) => m -> [(b,Stack)]
-- eval = run . low
