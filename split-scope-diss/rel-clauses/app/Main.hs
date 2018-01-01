module Main where

import Grammar
import IxCont
import RelClauses
import Control.Monad.State
import Control.Monad.Indexed
import Control.Exception

{-# ANN module "HLint: ignore Use fmap" #-}
{-# ANN module "HLint: ignore Use head" #-}

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

  , putStrLn "-- some boy who john is"
  , print $ flip runStateT [] $
    let smBoy = _push $ _some (\x -> return $ elem x ["J", "B", "F"])
     in who (lower $ john <\> (is </> prn 0)) smBoy

  , putStrLn "-- some boy left who john is"
  , print $ flip runStateT [] $
    let { _left = flip elem ["J","B"]
        ; smBoyLeft = liftM _left (_push $ _some (\x -> return $ elem x ["J", "B", "F"]))
        }
     in who (lower $ john <\> (is </> prn 0)) smBoyLeft

  , putStrLn "-- some boy and some girl"
  , print $ flip runStateT [] $
    _push $ liftM2 (++) (lower $ some <\> boy) (lower $ some <\> girl)

  , putStrLn "-- some boy and some girl who fought"
  , print $ flip runStateT [] $
    let { _fought = flip elem ["JM"]
        ; smBoyGrl = _push $ liftM2 (++) (lower $ some <\> boy) (lower $ some <\> girl)
        }
     in who (liftM _fought $ _prn 0) smBoyGrl
 
  , putStrLn "-- some boy left and some girl left who fought"
  , print $ flip runStateT [] $
    let { _left = flip elem ["J", "M", "B"]
        ; _fought = flip elem ["JM"]
        ; smBoyLeft = liftM _left (_push $ lower $ some <\> boy)
        ; smGrlLeft = liftM _left (_push $ lower $ some <\> girl)
        ; sblsgl = conj smBoyLeft smGrlLeft >>= \x -> state (\s -> (x, s++[s!!0 ++ s!!1]))
        }
     in who (liftM _fought $ _prn 2) sblsgl
 
  , putStrLn "-- the boy and the girl who fought"
  , print $ flip runStateT [] $ flip runIxCont id $
    let { _fought = flip elem ["JM"]
        ; cnj = iliftM2 (liftM2 (++))
        ; thBoyGirl = liftM _push $ cnj (llower1 $ the' 0 <\\> ireturn boy) (llower1 $ the' 1 <\\> ireturn girl)
        }
     in ireturn (who (liftM _fought $ _prn 2)) </> thBoyGirl
 
  , putStrLn "-- the boy left and the girl left who fought"
  , print $ flip runStateT [] $ flip runIxCont id $
    let { _left = flip elem ["J", "M", "B"]
        ; _fought = flip elem ["JM"]
        ; thBoyLeft = iliftM (liftM _left) $ llower1 $ the' 0 <\\> ireturn boy
        ; thGrlLeft = iliftM (liftM _left) $ llower1 $ the' 1 <\\> ireturn girl
        ; tbltgl = iliftM (>>= \x -> state $ \s -> (x, s++[s!!0 ++ s!!1])) $ iliftM2 conj thBoyLeft thGrlLeft
        }
     in ireturn (who (liftM _fought $ _prn 2)) </> tbltgl
  ]
