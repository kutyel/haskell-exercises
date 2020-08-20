{-# LANGUAGE FlexibleInstances #-}

module Exercises where

class PopQuiz a

-- | Which of the following instances require 'FlexibleInstances'? Don't cheat
-- :D This is a tricky one, but look out for nested concrete types!
instance PopQuiz Bool

instance PopQuiz [Bool] -- ✅ needs extension

instance PopQuiz [a]

instance PopQuiz (a, b)

instance PopQuiz [(a, b)] -- ✅ needs extension

instance PopQuiz (IO a)

newtype RIO r a = RIO (r -> IO a) -- Remember, this is a /new type/.

type RIO' r a = r -> IO a

instance PopQuiz (RIO Int a) -- ✅ needs extension

instance PopQuiz (RIO r a)

instance PopQuiz (RIO' r a) -- ✅ needs extension

-- instance PopQuiz (r -> IO a) -- ✅ needs extension -> THIS IS EQUAL TO THE ONE ON L29!

instance PopQuiz (a -> b) -- We can write (a -> b) as ((->) a b).

instance PopQuiz (a -> b -> c) -- ✅ needs extension

instance PopQuiz (a, b, c)

instance PopQuiz (a, (b, c)) -- ✅ needs extension

instance PopQuiz ()

instance PopQuiz (a, b, c, a) -- ✅ needs extension

data Pair a = Pair a a

type Pair' a = (a, a)

-- instance PopQuiz (a, a) -- ✅ needs extension -> THIS IS EQUAL TO THE ONE ON L53!

instance PopQuiz (Pair a)

instance PopQuiz (Pair' a) -- ✅ needs extension
