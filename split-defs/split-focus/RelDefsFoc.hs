module RelDefsFoc where

import RelDefs


type C a = Stack -> ([(a, Stack)], Post)

instance Monad C where
  return x = \s -> ([(x, s)], mempty)
  m >>= k = \s -> (concat [fst (k a s') | (a,s') <- fst (m s)],
                   mconcat [snd (k a s') | (a,s') <- fst (m s)])
