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

un :: Prop -> Prop --VP negation
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
want', want2', receive' :: Ent -> Ent -> Bool

want' x s@(Atom y) = elem (x,s) [(d,a), (d,b), (d,c)]
want' x   (Plur y) = and (map (\z -> elem (x,z) [(d,a), (d,b), (d,c)]) y)

want2' x s@(Atom y) = elem (x,s) [(d,a), (d,b), (d,c), (e,a), (e,b), (e,c)]
want2' x   (Plur y) = and (map (\z -> elem (x,z) [(d,a), (d,b), (d,c), (e,a),
  (e,b), (e,c)]) y)

receive' x s@(Atom y) = elem (x,s) [(d,a), (e,b), (f,c)]
receive' x   (Plur y) = and (map (\z -> elem (x,z) [(d,a), (e,b), (f,c)]) y)

-- continuized transitives
want, want2, receive :: Ent -> Ent -> Prop
[want, want2, receive] = map cont_eet [want', want2', receive']

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

-- "the" is like "every" except that it doesn't throw anything other than what
-- it is quantifying over onto the stack; uniqueness presuppositions absent here
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


-- Basic Examples

-- eval (alex laugh) == True
-- he 0 laugh [a,b] trivial == True
-- he 1 smoke [a,b] trivial == False
-- eval ((alex laugh) `conj` (he 0 smoke)) == True
-- eval (some student laugh) == True
-- eval (every student laugh) == True
-- eval (every student smoke) == False

-- "Every student V-ed the (same) book":
-- eval (every student (\m -> the book (\n -> want n m))) == False
-- eval (every student (\m -> the book (\n -> receive n m))) == False
-- eval (every student (same (\f -> the (f book)) (\m n -> want m n))) == True
-- eval (every student (same (\f -> the (f book)) (\m n -> receive m n))) ==
--   False

-- "Every student V-ed a (different) book":
-- eval (every student (\m -> some book (\n -> want n m))) == True
-- eval (every student (\m -> some book (\n -> receive n m))) == True
-- eval (every student (different (\f -> some (f book)) (\m n -> want m n))) ==
--   False
-- eval (every student (different (\f -> some (f book)) (\m n -> receive m n)))
--   == True

-- Throws a runtime error, since stack must have either a sum-individual or two
-- atomic individuals to distribute over
-- eval (alex (different (\f -> some (f book)) (\m n -> receive m n)))
-- eval (alex (same (\f -> the (f book)) (\m n -> receive m n)))
-- eval (some student (different (\f -> some (f book)) (\m n -> receive m n)))
-- eval (some student (same (\f -> the (f book)) (\m n -> receive m n)))


-- Plurals
--
-- eval (the (pl student) (\m -> want dubliners m)) == True
-- eval (the (pl student) (same (\f -> the (f book)) (\m n -> want m n))) ==
--   True
-- eval (the (pl student) (same (\f -> the (f book)) (\m n -> receive m n))) ==
--   False
-- eval (oplus [a,b] (same (\f -> the (f book)) (\m n -> want m n))) == True
-- eval (oplus [a,b] (same (\f -> the (f book)) (\m n -> receive m n))) == False
--
--
-- No apparatus for bare plurals yet, but if we pretend that plurals can license
-- singular "different"...
--
-- eval (the (pl student) (different (\f -> some (f book)) (\m n -> want m n)))
--   == False
-- eval (the (pl student) (different (\f -> some (f book)) (\m n -> receive m
--   n))) == True
-- eval (oplus [a,b] (different (\f -> some (f book)) (\m n -> want m n))) ==
--   False
-- eval (oplus [a,b] (different (\f -> some (f book)) (\m n -> receive m n))) ==
--   True


-- "No student(s) V-ed the (same) book":
--
-- eval (no student (\m -> some book (\n -> want n m))) == False
-- eval (no student (\m -> some book (\n -> receive n m))) == False
--
-- Throws a runtime error (though marginally grammatical)
-- eval (no student (same (\f -> the (f book)) (\m n -> want m n)))
-- eval (no student (different (\f -> some (f book)) (\m n -> want m n)))
--
-- eval (no (pl student) (same (\f -> the (f book)) (\m n -> want m n))) ==
--   False
-- eval (no (pl student) (same (\f -> the (f book)) (\m n -> receive m n))) ==
--   True
-- eval (no (pl student) (different (\f -> some (f book)) (\m n -> want m n)))
--   == True
-- eval (no (pl student) (different (\f -> some (f book)) (\m n -> receive m
--   n))) == False


-- Partitives
--
-- Have to use "ast" instead of "pl" for the plural partitive object, again
-- becuase there's no apparatus for bare plurals
--
-- eval (some (of_p (the (pl student))) smoke) == True
-- eval (alex (\m -> some (of_p (the (ast book))) (\n -> want n m))) == True
--
--"Alex and Bill / The students / Every student V-ed some of the same books":
-- eval (oplus [a,b] (same (\f -> some (of_p (the (f (ast book))))) (\m n ->
--   want m n))) == True
-- eval (oplus [a,b] (same (\f -> some (of_p (the (f (ast book))))) (\m n ->
--   receive m n))) == False
-- eval (the (pl student) (same (\f -> some (of_p (the (f (ast book))))) (\m n
--   -> want m n))) == True
-- eval (the (pl student) (same (\f -> some (of_p (the (f (ast book))))) (\m n
--   -> receive m n))) == False
-- eval (every student (same (\f -> some (of_p (the (f (ast book))))) (\m n ->
--   want m n))) == True
-- eval (every student (same (\f -> some (of_p (the (f (ast book))))) (\m n ->
--   receive m n))) == False
--
-- "Alex and Bill / etc. V-ed none of the same books":
-- eval (oplus [a,b] (same (\f -> no (of_p (the (f (ast book))))) (\m n -> want
--   m n))) == False
-- eval (oplus [a,b] (same (\f -> no (of_p (the (f (ast book))))) (\m n ->
--   receive m n))) == True
-- eval (the (pl student) (same (\f -> no (of_p (the (f (ast book))))) (\m n ->
--   want m n))) == False
-- eval (the (pl student) (same (\f -> no (of_p (the (f (ast book))))) (\m n ->
--   receive m n))) == True
-- eval (every student (same (\f -> no (of_p (the (f (ast book))))) (\m n ->
--   want m n))) == False
-- eval (every student (same (\f -> no (of_p (the (f (ast book))))) (\m n ->
--   receive m n))) == True


-- Problem Sentences
-- eval (no (pl student) (\m -> some book (\n -> want n m))) == False
-- eval (no (pl student) (\m -> some book (\n -> receive n m))) == True
