import Wco_dyn_scope

import Control.Monad.State

filterS :: (E -> T) -> Stack -> Stack
filterS n = filter (\y -> truthy $ eval $ n (unit y))

diff :: (E -> T) -> E -> T
diff n x = do
  s <- get
  let s' = filterS n s
  (n x) `conj` (do { x' <- x; unit (x' `notElem` s') })

same :: (E -> T) -> E -> T
same n x = do
  s <- get
  let s' = filterS n s
  (n x) `conj` (do { x' <- x; unit ((x' `elem` s') || length s' < 1) })

-- "internally dynamic" universal
everyD :: (E -> T) -> (E -> T) -> T
everyD n c = do
  let (p:ps) = map (\x -> c $ unit' [x] x) $ filterS n [1..10]
  foldl dyn_conj p ps

-- to kill off the binding potential, we need a static shell
everyS :: (E -> T) -> (E -> T) -> T
everyS n c = StateT $ \s ->
  let xs = runStateT (everyD n c) s in
  [(truthy xs, s)]
-- ideally, we would use "compress xs" instead of "[]" here, but because the
-- elements of the restrictor all happen to land in the exact same positions
-- in the respective output stacks, they pass the compression filter. 
  
someD :: (E -> T) -> E
someD n = mapunit' $ filterS n [1..10]

someO :: (E -> T) -> (E -> T) -> T
someO n c = do
  let (p:ps) = map (\x -> c $ unit' [x] x) $ filterS n [1..10]
  foldl disj p ps
  

{-
every' :: (E -> T) -> (E -> T) -> T
every' n = \c -> do
  let p = filterS n [1..10]
  if (trace ("p: " ++ show p) (p == []))
    then unit True
    else do
            let (x:xs) = p
                b      = every' (charF xs) c
            c (unit' [x] x) `dyn_conj` (trace ("every p c: " ++ (show $ eval b)) b)

every'' :: (E -> T) -> (E -> T) -> T
every'' n = \c -> do
  let p = filter (\y -> truthy $ eval $ n (unit y)) [1..10]
  if (trace ("p: " ++ show p) (p == []))
    then unit True
    else do
            let (x:xs) = p
                b      = neg $ every'' (charF xs) c
            neg (lower1 $ bslash (bind1 $ lift1 $ neg (c (unit' [x] x))) $ slash (lift1 disj) (trace ("every p c: " ++ (show $ eval b)) (bind1 $ lift1 b)) )
-}



-- examples

-- the recursive (folded) denotation for "everyD" does not get off the
-- ground when sentences are lowered. what is needed is to lower *each* of the
-- sentences within the universal's scope independently; but at the moment this
-- does not seem compositionally possible


-- now each binding stack reveals a total assignment of "over 7"s to "under 4"s
-- (i.e. each of the possible stacks encodes a functional witness for the
-- universal + indefinite
--
-- eval $ ($ id) $ bslash (everyD $ under 4) $ slash (lift1 lthan) (some $ over 7)


-- this means that "different" just has to weed out the non-injective
-- functional witnesses
--
-- eval $ ($ id) $ bslash (everyD $ under 4) $ slash (lift1 lthan) (some $ diff $ over 7)


-- intriguingly, the necessity of non-lowering predicts the lack of
-- diff > every "crossover" straightaway
--
-- eval $ ($ id) $ lower2 $ bslash2 (lift1 (some $ diff $ over 7)) $ slash2 (lift1 $ lift1 gthan) (lift2 $ everyD $ under 4)
--
-- the question, then, is whether diff > every "crossover" alleviates he >
-- every (weak) crossover, as in "A different one of her students was
-- bothering every teacher", or more subtly, with implicitly relational nouns,
-- as in "A different shareholder hated every company" (where the shareholders
-- partially vary with companies). initial reaction is negative: these are no better or
-- worse than the corresponding sentences without "different"
