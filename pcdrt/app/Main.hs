module Main where

import PCDRT

main :: IO ()
main = sequence_ $
  [ putStrLn ""
  , putStrLn "senSaw [0]"
  , outs senSaw [0]
  , putStrLn ""
  , putStrLn "senSwitchV [0]"
  , outs senSwitchV [0]
  , putStrLn ""
  , putStrLn "senConj1 [5]"
  , outs senConj1 [5]
  , putStrLn ""
  , putStrLn "senConj2 [5]"
  , outs senConj2 [5]
  ]

------------------------------------------------------------------------------
-- Example Formulas
------------------------------------------------------------------------------
senSaw :: Update
senSaw = U `saw` V

-- outs senSaw [0]
-- (0,[u := "J", v := "J"]) > (0,[u := "J", v := "J"])

senSwitchV :: Update
senSwitchV = switch V

-- outs senSwitchV [0]
-- (0,[u := "J", v := "J"]) > (0,[u := "J", v := "J"])
--
-- (0,[u := "J", v := "J"]) > (1,[u := "J", v := "M"])
--
-- (0,[u := "J", v := "J"]) > (0,[u := "J", v := "J"])
--                          > (1,[u := "J", v := "M"])
--
-- (0,[u := "J", v := "J"]) > (2,[u := "J", v := "B"])
--
-- (0,[u := "J", v := "J"]) > (0,[u := "J", v := "J"])
--                          > (2,[u := "J", v := "B"])
--
-- (0,[u := "J", v := "J"]) > (1,[u := "J", v := "M"])
--                          > (2,[u := "J", v := "B"])
--
-- (0,[u := "J", v := "J"]) > (0,[u := "J", v := "J"])
--                          > (1,[u := "J", v := "M"])
--                          > (2,[u := "J", v := "B"])

senConj1, senConj2 :: Update
senConj1 = senSaw `conj` senSwitchV
senConj2 = senSwitchV `conj` senSaw


-- outs senConj1 [5]
-- (5,[u := "M", v := "B"]) > (3,[u := "M", v := "J"])
--
-- (5,[u := "M", v := "B"]) > (4,[u := "M", v := "M"])
--
-- (5,[u := "M", v := "B"]) > (3,[u := "M", v := "J"])
--                          > (4,[u := "M", v := "M"])
--
-- (5,[u := "M", v := "B"]) > (5,[u := "M", v := "B"])
--
-- (5,[u := "M", v := "B"]) > (3,[u := "M", v := "J"])
--                          > (5,[u := "M", v := "B"])
--
-- (5,[u := "M", v := "B"]) > (4,[u := "M", v := "M"])
--                          > (5,[u := "M", v := "B"])
--
-- (5,[u := "M", v := "B"]) > (3,[u := "M", v := "J"])
--                          > (4,[u := "M", v := "M"])
--                          > (5,[u := "M", v := "B"])

-- outs senConj2 [5]
-- (5,[u := "M", v := "B"]) > (5,[u := "M", v := "B"])
