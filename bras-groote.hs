-- mashup of Brasoveanu 2011 with de Groote 2007
import Debug.Trace

type Ent = Char
type Stack = [Ent]
type Stackset = [Stack]
type Continuation = Stackset -> Bool
type Prop = Stackset -> Continuation -> Bool

insert :: Int -> Ent -> Stack -> Stack
insert 0 x i = x:i
insert n x (a:i) = a:(insert (n - 1) x i)

[a,b,c,d,e,f] = "abcdef"
domain = [a,b,c,d,e,f]

trivial :: Continuation
trivial i = True

eval :: Prop -> Bool
eval s = s [[]] trivial

john :: (Int -> Prop) -> Prop
john p is k = p 0 (map (\i -> a:i) is) k

he :: Int -> (Int -> Prop) -> Prop
he n p is k = p n is k

--boy, entered, poem, sat :: Int -> Prop
boy     n is k = (and (map (\i -> elem (i!!n) [a,b]) is)) && (k is)
entered n is k = (and (map (\i -> elem (i!!n) [a,b]) is)) && (k is)
poem    n is k = (and (map (\i -> elem (i!!n) [c,d]) is)) && (k is)
sat     n is k = (and (map (\i -> elem (i!!n) [a]) is)) && (k is)

recite, enjoy :: Int -> Int -> Prop
recite n m is k = (and (map (\i -> elem ((i!!n), (i!!m)) [(c,a),(d,b)]) is)) && (k is)
enjoy  n m is k = (and (map (\i -> elem ((i!!n), (i!!m)) [(c,a),(c,b)]) is)) && (k is)

conj :: Prop -> Prop -> Prop  -- after de Groote p. 3, (3) 
conj left right is k = left is (\is' -> right is' k)

every n res scope is k = 
  let fn x y = concat (map (\i -> [insert n x i, insert n y i]) is) in
    (and [conj (res n) (scope n) (fn x y) trivial
           | x <- domain, y <- domain, x /= y, res n (fn x y) trivial])
    && (k is)

-- given stackset [i1, i2, ..., im], test whether there exist x1, x2, ..., xm
--   such that [i1^{x1/n}, i2^{x2/n}, ..., in^{xm/m}] satisfies res n; scope n
indef n res scope is k =
  or [conj (res n) (scope n) is' k 
       | is' <- foldr (\i -> \jss -> [(insert n x i):js | x <- domain, js <- jss]) [[]] is]

different :: Int -> (Int -> Prop) -> Int -> Prop
different index nom m = conj (nom m) (\is -> \k -> ((is!!0)!!m) /= ((is!!index)!!m) && (k is))

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

girl n is k = (and (map (\i -> elem (i!!n) [e,f]) is)) && (k is)
give n m l is k = (and (map (\i -> elem ((i!!n), (i!!m), (i!!l))
                                        [(f,c,a),(e,d,b),(f,c,b),(e,d,a)])
                            is)) && (k is)
give' n m l is k = (and (map (\i -> elem ((i!!n), (i!!m), (i!!l))
                                        [(f,c,a),(e,c,b),(f,d,b),(e,d,a)])
                            is)) && (k is)

-- Ambiguous: Every boy gave/showed every girl a different poem
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 poem) (\m -> give n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 2 poem)) (\m -> give n m l)))) == False
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 poem) (\m -> give' n m l)))) == True
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 3 poem)) (\m -> give' n m l)))) == False
-- eval ((every 0 boy) (\l -> (every 1 girl) (\n -> (indef 2 (different 2 poem)) (\m -> give' n m l)))) == True

same :: Int -> (Int -> Prop) -> Int -> Prop
same index nom m = conj (nom m) (\is -> \k -> ((is!!0)!!m) == ((is!!index)!!m) && (k is))

-- Every boy recited a same poem:
-- eval((every 0 boy) (\x -> (indef 1 (same 1 poem)) (\y -> recite y x))) == False

-- Every boy enjoyed a same poem:
-- eval((every 0 boy) (\x -> (indef 1 (same 1 poem)) (\y -> enjoy y x))) == True
