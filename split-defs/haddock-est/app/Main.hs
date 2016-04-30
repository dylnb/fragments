module Main where

import Grammar
import IxCont
import SplitDefs
import Control.Monad.State
import Control.Monad.Indexed
import Control.Exception

main :: IO ()
main = mapM_ (handle $ \(AssertionFailed e) -> putStrLn "presup failure")
  [ putStrLn "-- some boy is a boy"
  , print $ eval $ push (ixlift . lower $ some <\> boy) <\> boy

  , putStrLn "-- the boy is a boy"
  , print $ eval $ (ixlift . llower $ the' 0 <\\> return boy) <\> boy

  , putStrLn "-- the girl is a girl"
  , print $ eval $ (ixlift . llower $ the' 0 <\\> return girl) <\> girl

  , putStrLn "-- john  likes the girl"
  , print $ eval $ push john <\> likes </> (ixlift . llower $ the' 1 <\\> return girl)
  ]
