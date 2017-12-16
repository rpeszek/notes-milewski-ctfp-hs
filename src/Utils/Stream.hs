module Utils.Stream where
import Data.Monoid((<>))
import Control.Comonad

-- | from the book
data Stream a = Cons a (Stream a)
instance Functor Stream where
   fmap f (Cons a as) = Cons (f a) (fmap f as)
instance Comonad Stream where
   extract (Cons a _) = a
   duplicate (Cons a as) = Cons (Cons a as) (duplicate as)

-- | utilities
streamIterate :: (a -> a) -> a -> Stream a
streamIterate f x = Cons x (streamIterate f (f x))

streamToList :: Int -> Stream a -> [a]
streamToList n (Cons a as) 
        | n <= 0 = [] 
        | n > 0  = a : (streamToList (n-1) as)


