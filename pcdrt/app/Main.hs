module Main where

import PCDRT

main :: IO ()
main = sequence_ $
  [ putStrLn ""
  , putStrLn "senSaw [0]"
  , printOutputs senSaw [0]
  , putStrLn ""
  , putStrLn "senSwitchV [0]"
  , printOutputs senSwitchV [0]
  , putStrLn ""
  , putStrLn "senConj1 [5]"
  , printOutputs senConj1 [5]
  , putStrLn ""
  , putStrLn "senConj2 [5]"
  , printOutputs senConj2 [5]
  ]

------------------------------------------------------------------------------
-- Example Formulas
------------------------------------------------------------------------------
senSaw :: Update
senSaw = U `saw` V

-- printOutputs senSaw [0]
-- [u := "J", v := "J"] > [u := "J", v := "J"]

senSwitchV :: Update
senSwitchV = switch V

-- printOutputs senSwitchV [0]
-- [u := "J", v := "J"] > [u := "J", v := "J"]
--
-- [u := "J", v := "J"] > [u := "J", v := "M"]
--
-- [u := "J", v := "J"] > [u := "J", v := "J"]
--                      > [u := "J", v := "M"]
--
-- [u := "J", v := "J"] > [u := "J", v := "B"]
--
-- [u := "J", v := "J"] > [u := "J", v := "J"]
--                      > [u := "J", v := "B"]
--
-- [u := "J", v := "J"] > [u := "J", v := "M"]
--                      > [u := "J", v := "B"]
--
-- [u := "J", v := "J"] > [u := "J", v := "J"]
--                      > [u := "J", v := "M"]
--                      > [u := "J", v := "B"]

senConj1, senConj2 :: Update
senConj1 = senSaw `conj` senSwitchV
senConj2 = senSwitchV `conj` senSaw

-- printOutputs senConj1 [5]
-- [u := "M", v := "B"] > [u := "M", v := "J"]
--
-- [u := "M", v := "B"] > [u := "M", v := "M"]
--
-- [u := "M", v := "B"] > [u := "M", v := "J"]
--                      > [u := "M", v := "M"]
--
-- [u := "M", v := "B"] > [u := "M", v := "B"]
--
-- [u := "M", v := "B"] > [u := "M", v := "J"]
--                      > [u := "M", v := "B"]
--
-- [u := "M", v := "B"] > [u := "M", v := "M"]
--                      > [u := "M", v := "B"]
--
-- [u := "M", v := "B"] > [u := "M", v := "J"]
--                      > [u := "M", v := "M"]
--                      > [u := "M", v := "B"]

-- printOutputs senConj2 [5]
-- [u := "M", v := "B"] > [u := "M", v := "B"]
