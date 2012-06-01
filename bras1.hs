-- mashup of Brasoveanu 2011 with de Groote 2007

type Ent = Char
type Stack = [Ent]
type Continuation = Stack -> Stack -> Bool
type Prop = Stack -> Stack -> Continuation -> Bool

insert :: Int -> Ent -> Stack -> Stack
insert 0 x i = x:i
insert n x (a:i) = a:(insert (n - 1) x i)

[a,b,c,d,e,f] = "abcdef"
domain = [a,b,c,d,e,f]

john :: (Int -> Prop) -> Prop
john p i j k = p 0 (a:i) (a:j) k

he :: Int -> (Int -> Prop) -> Prop
he n p i j k = p n i j k

boy, entered, poem, sat :: Int -> Prop
boy     n i j k = (elem (i!!n) [a,b]) && (elem (j!!n) [a,b]) && (k i j)
entered n i j k = (elem (i!!n) [a,b]) && (elem (j!!n) [a,b]) && (k i j)
poem    n i j k = (elem (i!!n) [c,d]) && (elem (j!!n) [c,d]) && (k i j)
sat     n i j k = (elem (i!!n) [a]) && (elem (j!!n) [a]) && (k i j)

recite, enjoy :: Int -> Int -> Prop
recite n m i j k = (elem ((i!!n), (i!!m)) [(c,a),(d,b)]) && 
                   (elem ((j!!n), (j!!m)) [(c,a),(d,b)]) && 
                   (k i j)
enjoy n m i j k = (elem ((i!!n), (i!!m)) [(c,a),(c,b)]) && 
                  (elem ((j!!n), (j!!m)) [(c,a),(c,b)]) && 
                  (k i j)

trivial :: Continuation
trivial i j = True

eval :: Prop -> Bool
eval s = s [] [] trivial

conj :: Prop -> Prop -> Prop  -- after de Groote p. 3, (3) 
conj left right i j k = left i j (\i' -> \j' -> right i' j' k)

indef, every :: Int -> (Int -> Prop) -> (Int -> Prop) -> Prop
indef n res scope i j k = 
    or [(conj (res n) (scope n) (insert n x i) (insert n y j) k) 
         | x <- domain, y <- domain]

every n res scope i j k = 
  (and [conj (res n) (scope n) (insert n x i) (insert n y j) trivial 
          | x <- domain, y <- domain, x /= y, res n (insert n x i) (insert n y j) trivial])
  && (k i j)

different :: Int -> (Int -> Prop) -> Int -> Prop
different n p m = conj (p m) (\i -> \j -> \k -> (i!!n) /= (j!!n) && (k i j))

-- eval (john entered) == True
-- he 0 sat [a,b] [a,b] trivial == True
-- he 1 sat [a,d] [d,b] trivial == False
-- eval ((john entered) `conj` (he 0 sat)) == True
-- eval (indef 0 boy sat) == True
-- eval(every 0 boy entered) == True
-- eval(every 0 poem sat) == False

-- Every boy read a (different) poem:
-- eval((every 0 boy) (\x -> (indef 1 poem) (\y -> recite y x))) == True
-- eval((every 0 boy) (\x -> (indef 1 (different 1 poem)) (\y -> recite y x))) == True

-- Every boy enjoyed a (different) poem:
-- eval((every 0 boy) (\x -> (indef 1 poem) (\y -> enjoy y x))) == True
-- eval((every 0 boy) (\x -> (indef 1 (different 1 poem)) (\y -> enjoy y x))) == False
