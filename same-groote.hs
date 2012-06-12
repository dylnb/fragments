-- mashup of Barker's 2007 parasitic "same" with de Groote's 2007 continuations

import Debug.Trace
import Data.List
import Data.Maybe

data Ent = Atom Char
         | Plur [Ent] deriving (Eq,Show)
type Stack = [Ent]
type Continuation = Stack -> Bool
type Prop = Stack -> Continuation -> Bool
type GQ = (Ent -> Prop) -> Prop

showPr :: (Ent -> Prop) -> String
showPr p = show (filter (eval . p) domain)

showGQ :: GQ -> String
showGQ g = show (map (\h -> [z | z <- atoms, eval (h z)]) funcs)
  where fn s@(Atom y) = (\x i k -> x == s)
        fn   (Plur y) = (\x i k -> elem x y)
        funcs = filter (eval . g . ast) (map fn domain)
 
ins :: Int -> Ent -> Stack -> Stack
ins 0 x i = x:i
ins n x (a:i) = a:(ins (n - 1) x i)

[a,b,c,d,e,f,g,h] = map Atom "abcdefgh"
atoms = [a,b,c,d,e,f,g,h]

plurs = map Plur (filter (\x -> length x > 1) (subsequences atoms))
 
domain = atoms ++ plurs

makePlurs :: [Ent] -> [Ent]
makePlurs []              = []
makePlurs (x@(Atom i):is) = (Plur [x]):(makePlurs is)
makePlurs (x@(Plur i):is) = x:(makePlurs is)

join :: [Ent] -> Ent
join is | length ls > 1   = Plur ls
        | otherwise       = head ls
  where simpleAdd []              = []
        simpleAdd (x@(Atom i):is) = x:(simpleAdd is)
        simpleAdd (x@(Plur i):is) = i ++ (simpleAdd is)
        ls = (nub . simpleAdd) is 

trivial :: Continuation
trivial i = True

eval :: Prop -> Bool
eval s = s [] trivial

-- continuization operators
cont_e :: Ent -> GQ
cont_e x p i k = p x (x:i) k

cont_et :: (Ent -> Bool) -> (Ent -> Prop)
cont_et p x i k = p x && (k i)

cont_eet :: (Ent -> Ent -> Bool) -> (Ent -> Ent -> Prop)
cont_eet r x y i k = r x y && (k i)

-- type lifters
ar_et :: (Ent -> Prop) -> GQ -> Prop
ar_et p g i k = g p i k

ar_eet :: (Ent -> Ent -> Prop) -> GQ -> Ent -> Prop
ar_eet r g y i k = g (\x -> r x y) i k

-- dynamic connectives
conj :: Prop -> Prop -> Prop --after de Groote p. 3, (3) 
conj left right i k = left i (\i' -> right i' k)

un :: Prop -> Prop
un s i k = not (s i k) && (k i)

-- sum-forming "and"
oplus :: [Ent] -> GQ
oplus xs = cont_e (join xs)
-- oplus xs p i k = (foldr conj (\i' k' -> True) (map p xs)) (Plur xs:i) k

-- partitive "of"; returns the set of individuals at the bottom of the GQ
-- lattice (returns the empty set if the GQ is not an ultrafilter)
of_p :: GQ -> Ent -> Prop
of_p g y i k = and (map (\h -> eval (h y)) funcs) && (k i)
  where fn s@(Atom y) = (\x i k -> x == s)
        fn   (Plur y) = (\x i k -> elem x y)
        funcs = filter (eval . g . ast) (map fn domain)

-- Link's maximal sum individual
top :: (Ent -> Prop) -> Ent
top p = join (filter (eval . p) domain)

-- "asterisk", Link's all-inclusive pluralizer
ast :: (Ent -> Prop) -> Ent -> Prop
ast p s@(Atom y) i k = p s i k
ast p   (Plur y) i k = and (map (eval . p) y) && (k i)

-- plurals only
pl :: (Ent -> Prop) -> Ent -> Prop
pl p   (Atom y) i k = False
pl p s@(Plur y) i k = ast p s i k

-- projection operator
get_pl :: Stack -> [Ent]
get_pl is | isNothing (first_pl is)     = [is!!0, is!!1]
          | otherwise                   = fromJust (first_pl is)

first_pl :: Stack -> Maybe [Ent]
first_pl []            = Nothing
first_pl ((Plur i):is) = Just i
first_pl ((Atom i):is) = first_pl is

-- names
alex', bill', chris', dubliners' :: Ent
[alex', bill', chris', dubliners'] = [a, b, c, d]

--continuized names, pronouns
alex, bill, chris :: GQ
[alex, bill, chris] = map cont_e [alex', bill', chris']

dubliners :: Ent
dubliners = dubliners'

he, they :: Int -> GQ
he n p i k = p (i!!n) i k
they n p i k = p (i!!n) i k

-- basic nominals
student', book' :: Ent -> Bool
student' y = elem y [a,b,c]
book' y    = elem y [d,e,f]

-- continuized nominals
student, book :: Ent -> Prop
[student, book] = map cont_et [student', book']

-- basic intransitives
laugh', smoke' :: Ent -> Bool
laugh' y   = elem y [a,b,c]
smoke' y   = elem y [a]

-- continuized, asterisk-ized intransitives
laugh, smoke :: Ent -> Prop
[laugh, smoke] = map (ast . cont_et) [laugh', smoke']

-- basic transitives
want', receive' :: Ent -> Ent -> Bool

want' x s@(Atom y) = elem (x,s) [(d,a), (d,b), (d,c)]
want' x   (Plur y) = and (map (\z -> elem (x,z) [(d,a), (d,b), (d,c)]) y)

receive' x s@(Atom y) = elem (x,s) [(d,a), (e,b), (f,c)]
receive' x   (Plur y) = and (map (\z -> elem (x,z) [(d,a), (e,b), (f,c)]) y)

-- continuized transitives
want, receive :: Ent -> Ent -> Prop
[want, receive] = map cont_eet [want', receive']

-- quantifiers, articles
every :: (Ent -> Prop) -> GQ
every res scope i k = 
  and [not (res x i (\i' -> not (scope x (x:(top res):i') trivial))) | x <- domain] && (k i)

some :: (Ent -> Prop) -> GQ
some res scope i k =
  or [res x i (\i' -> scope x (x:i') k) | x <- domain]

no :: (Ent -> Prop) -> GQ
no res scope i k =
  and [not (res x i (\i' -> scope x (x:i') trivial)) | x <- domain] && (k i)

the :: (Ent -> Prop) -> GQ
the res = cont_e (top res)
{-
the2 :: (Ent -> Prop) -> GQ
the2 res scope i k =
  and [not (res x i (\i' -> not (scope x (x:i') trivial))) | x <- domain] && (k (x:i))
-}

-- scope-taking adjectives
same, different :: (((Ent -> Prop) -> Ent -> Prop) -> GQ) -> (Ent -> Ent -> Prop) -> Ent -> Prop
same dp verb x i k =
  let fn s@(Atom x) = elem s
      fn   (Plur x) = (\w -> all (\r -> elem r w) x) in
  and [eval (dp (\g -> \y -> conj (verb y u) (g y)) (\z -> verb z v))
        | u <- atoms, v <- (delete u domain),
          elem u (get_pl i), fn v (get_pl i)] && (k i)

different dp verb x i k =
  let fn s@(Atom x) = elem s
      fn   (Plur x) = (\w -> all (\r -> elem r w) x) in
  and [eval (dp (\g -> \y -> conj (verb y u) (g y)) (\z -> un (verb z v)))
        | u <- atoms, v <- (filter (\(Plur x) -> notElem u x) plurs) ++ (delete u atoms),
          elem u (get_pl i), fn v (get_pl i)] && (k i)

{- 
different :: Int -> (Int -> Prop) -> Int -> Prop
different index nom m = conj (nom m) (\is -> \k -> ((is!!0)!!m) /= ((is!!index)!!m) && (k is))

-- butfor is like the g[x]h operation in DPL and CDRT; it checks that stacks
--   i and j agree on every column except possibly the ones in ns
butfor :: [Int] -> Stack -> Stack -> Bool
butfor ns i j = 
 and [(i!!x) == (j!!x) | x <- filter (\y -> notElem y ns) [0..length i - 1]]

-- "diff" is another implementation option for different. the index on "diff" is
--   just the index of its associated distributor. it guarantees that if rows 
--   i and j agree on everything except possibly column n, then they differ on column n
diff :: Int -> (Int -> Prop) -> Int -> Prop
diff ind nom m =
 conj (nom m) (\is -> \k -> and [(i!!m) /= (j!!m)
       | i <- is, j <- is, i /= j, (butfor [ind,m] i j)] && (k is))
-}

-- eval (john entered) == True
-- he 0 sat [[a,b]] trivial == True
-- he 1 sat [[a,d],[d,b]] trivial == False
-- eval ((john entered) `conj` (he 0 sat)) == True
-- eval (indef 0 boy sat) == True
-- eval(every 0 boy entered) == True
-- eval(every 0 boy sat) == False

-- Every boy read a (different) poem:
-- eval((every 0 boy) (\x -> (indef 1 poem) (\y -> recite y x))) == True
-- eval((every 0 boy) (\x -> (indef 1 (different 1 poem)) (\y -> recite y x))) == True

-- Every boy enjoyed a (different) poem:
-- eval((every 0 boy) (\x -> (indef 1 poem) (\y -> enjoy y x))) == True
-- eval((every 0 boy) (\x -> (indef 1 (different 1 poem)) (\y -> enjoy y x))) == False

-- Throws a runtime error, since "different" requires more than one stack on the stackset:
-- eval(john (\x -> (indef 1 (different 1 poem)) (\y -> enjoy y x)))

{-
girl n is k = (and (map (\i -> elem (i!!n) [e,f]) is)) && (k is)
give n m l is k = (and (map (\i -> elem ((i!!n), (i!!m), (i!!l))
                                        [(f,c,a),(e,d,b),(f,c,b),(e,d,a)])
                            is)) && (k is)
give' n m l is k = (and (map (\i -> elem ((i!!n), (i!!m), (i!!l))
                                        [(f,c,a),(e,c,b),(f,d,b),(e,d,a)])
                            is)) && (k is)
give'' n m l is k = (and (map (\i -> elem ((i!!n), (i!!m), (i!!l))
                                        [(f,c,a),(e,c,a),(f,d,b),(e,d,b)])
                            is)) && (k is)
-}

-- Ambiguous: Every boy gave/showed every girl a different poem
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 poem) (\m -> give n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 2 poem)) (\m -> give n m l)))) == False
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 poem) (\m -> give' n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give' n m l)))) == False
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 2 poem)) (\m -> give' n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give'' n m l)))) == False

-- Every boy recited a same poem:
-- eval((every 0 boy) (\x -> (indef 1 (same 1 poem)) (\y -> recite y x))) == False

-- Every boy enjoyed a same poem:
-- eval((every 0 boy) (\x -> (indef 1 (same 1 poem)) (\y -> enjoy y x))) == True
