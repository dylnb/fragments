{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module RecVP where

type Ent = Int
-- Dummy zero-ary type for individuals

data Stack a = Stack [a]
-- "Stack" is a dummy monadic constructor that wraps around any list of things
-- (these could be dynamic "VP"s). In the type signature of an instance of one
-- of these "Stack" objects, the "a" parameter identifies the type of things
-- on the stack. 

data VP a = VP (Stack (VP a) -> a -> Bool)
-- "VP" is a constructor that wraps around a dynamic verb phrase, a function
-- from "Stacks" of "VP"-wrapped things (themselves functions from ...) to
-- regular <x,t> functions

-- Just for fun, here's a pretty trivial instance of overloading, both in the
-- types and in the semantics
type family Unwrapped (a :: *)
type instance Unwrapped (Stack a) = [a]
type instance Unwrapped (VP a)    = Stack (VP a) -> a -> Bool
-- "Unwrapped" is a type constructor (rather than a data constructor), I
-- think. Or something like that. Effectively, it provides a means of finely
-- tuning the type-polymorphism of certain functions. In this case, the
-- "Unwrapped" type of a "Stack", say an stack of individuals (type "Stack
-- Ent") is just the type of the underlying list. And the "Unwrapped" type of
-- a VP is the type of the underlying function. (I should mention there are
-- much simpler ways to recover boxed up types in Haskell, but this works)

class Unwrappable a where
  unwrap :: a -> Unwrapped a
-- This defines a class of data types to which the "unwrap" function will
-- apply. All this definition does is declare the existence of the "unwrap"
-- function, and paramterizes its type to the type of its argument.
-- Specifically, "unwrap" will always be a function from some "Unwrappable"
-- type "a" to the type of "a" when it's "Unwrapped", according to the type
-- family declared above.

instance Unwrappable (Stack a) where
  unwrap (Stack s) = s
instance Unwrappable (VP a) where
  unwrap (VP v) = v
-- Finally, this defines the overloaded instances of the "unwrap" function for
-- the different types it applies to (the two "Unwrappable" types). In both
-- cases, it is as boring as possible.


-- ========== Auxiliary Functions ========== 

-- Grabs the smallest two individuals satisfying "v"
firstTwo :: Stack (VP Ent) -> VP Ent -> Stack Ent
firstTwo s v = Stack $ take 2 $ filter (unwrap v s) (unwrap domain)


-- ========== Model ========== 

domain :: Stack Ent
domain = Stack [1..10]


-- ========== Language ========== 

-- Everyone less than 5 cooked. After the dollar sign, we have a completely
-- standard relation between discourse stacks and sets of
-- individuals, which holds of any stack and the set of individuals less than
-- five. Then we wrap it up in a VP shell (lol)
cook :: VP Ent
cook = VP $ \_ x -> x < 5

-- Everyone over 5 cleaned.
clean :: VP Ent
clean = VP $ \_ x -> x > 5

-- Grabs the first VP on the stack, extracts the underlying function from it,
-- and runs that function against the stack
proVP :: VP Ent
proVP = VP $ \s x -> unwrap (head $ unwrap s) s x

-- Grabs the second VP on the stack, etc.
proVP2 :: VP Ent
proVP2 = VP $ \s x -> unwrap (unwrap s !! 1) s x

-- The people who "want to v" are the smallest two people who, in fact, "v".
-- "firstTwo v" returns a "Stack" object, so to access the underlying list, we
-- have to "unwrap" it. As with "cook", "wantsTo" doesn't care about the stack
wantsTo :: VP Ent -> VP Ent
wantsTo v  = VP $ \s x -> x `elem` unwrap (firstTwo s v)


--  ========== Discourse ==========

s' :: Stack (VP Ent)
s' = Stack [cook, wantsTo cook]

s'' :: Stack (VP Ent)
s'' = Stack [wantsTo proVP, cook]
-- this causes infinite loops if one is not careful!


-- ========== Examples ==========

-- unwrap cook (Stack []) 3
-- (True)

-- unwrap cook s' 7
-- (False)

-- unwrap proVP (Stack []) 2
-- (Exception: empty list)

-- unwrap proVP s' 2
-- (True)

-- unwrap proVP s' 7
-- (False)

-- unwrap (wantsTo cook) (Stack []) 2
-- (True)

-- unwrap (wantsTo cook) (Stack []) 4
-- (False)

-- unwrap (wantsTo proVP) s' 2 
-- (True)

-- unwrap (wantsTo proVP) s' 4
-- (False)

-- unwrap proVP s'' 2
-- INFINITE LOOP!!!

---------------------------------

-- Here's a dynamified-by-declaration, mickey mouse version of the
-- "cook ~ clean" case

-- let t = Stack []
-- unwrap cook t 2
--
-- let t = Stack [cook]
-- unwrap (wantsTo proVP) t 2
--
-- let t = Stack [wantsTo proVP, cook]
-- unwrap clean t 2
--
-- let t = Stack [clean, wantsTo proVP, cook]
-- unwrap proVP2 t 2
