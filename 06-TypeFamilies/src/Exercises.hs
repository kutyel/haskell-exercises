{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Exercises where

import Data.Kind (Constraint, Type)

-- | Before we get started, let's talk about the @TypeOperators@ extension. All
-- this does is allow us to write types whose names are operators, and write
-- regular names as infix names with the backticks, as we would at the value
-- level.

{- ONE -}

data Nat = Z | S Nat

-- | a. Use the @TypeOperators@ extension to rewrite the 'Add' family with the
-- name '+':
type family (+) (a :: Nat) (b :: Nat) :: Nat where
  'Z + y = y
  'S x + y = 'S (x + y)

-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why? 🤷🏻‍♂️
type family (**) (a :: Nat) (b :: Nat) :: Nat where
  'Z ** _ = 'Z
  'S x ** y = y + (x ** y)

-- | c. Write a function to add two 'SNat' values.
data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

add :: SNat x -> SNat y -> SNat (x + y)
add SZ y = y
add (SS x) y = SS (add x y)

{- TWO -}

data Vector (count :: Nat) (a :: Type) where
  VNil :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | a. Write a function that appends two vectors together. What would the size
-- of the result be?
append :: Vector m a -> Vector n a -> Vector (m + n) a
append VNil ws = ws
append (VCons v vs) ws = VCons v (append vs ws)

-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.
flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n ** m) b
flatMap VNil _ = VNil
flatMap (VCons x xs) f = f x `append` flatMap xs f

{- THREE -}

-- | a. More boolean fun! Write the type-level @&&@ function for booleans.
type family (&&) (a :: Bool) (b :: Bool) :: Bool where
  'True && 'True = 'True
  _ && _ = 'False

-- | b. Write the type-level @||@ function for booleans.
type family (||) (a :: Bool) (b :: Bool) :: Bool where
  'False || x = x
  'True || _ = 'True

-- | c. Write an 'All' function that returns @'True@ if all the values in a
-- type-level list of boleans are @'True@.
type family All (xs :: [Bool]) :: Bool where
  All '[] = 'True
  All (x ': xs) = x && All xs

{- FOUR -}

-- | a. Nat fun! Write a type-level 'compare' function using the promoted
-- 'Ordering' type.
type family Compare (x :: Nat) (y :: Nat) :: Ordering where
  Compare 'Z 'Z = 'EQ
  Compare 'Z ('S _) = 'LT
  Compare ('S _) 'Z = 'GT
  Compare ('S x) ('S y) = Compare x y

-- | b. Write a 'Max' family to get the maximum of two natural numbers.
type family Max (x :: Nat) (y :: Nat) :: Nat where
  Max x y = Max' (Compare x y) x y

type family Max' (o :: Ordering) (x :: Nat) (y :: Nat) :: Nat where
  Max' 'GT x _ = x
  Max' _ _ x = x

-- | c. Write a family to get the maximum natural in a list.
type family Maximum (x :: [Nat]) :: Nat where
  Maximum '[] = 'Z
  Maximum (x ': xs) = Max x (Maximum xs)

{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.
type family Insert (x :: Nat) (xs :: Tree) :: Tree where
  Insert x 'Empty = 'Node 'Empty x 'Empty
  Insert x ('Node l c r) = Insert' (Compare x c) x ('Node l c r)

type family Insert' (o :: Ordering) (x :: Nat) (xs :: Tree) :: Tree where
  Insert' 'LT x ('Node l c r) = 'Node (Insert x l) c r
  Insert' 'GT x ('Node l c r) = 'Node l c (Insert x r)
  Insert' 'EQ _ xs = xs

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type family Delete (x :: Nat) (xs :: Tree) :: Tree where
  Delete _ 'Empty = 'Empty
  Delete x ('Node l c r) = Delete' (Compare x c) x ('Node l c r)

type family Delete' (o :: Ordering) (x :: Nat) (xs :: Tree) :: Tree where
  Delete' 'LT x ('Node l c r) = 'Node (Delete x l) c r
  Delete' 'GT x ('Node l c r) = 'Node l c (Delete x r)
  Delete' 'EQ _ ('Node 'Empty _ r) = r
  Delete' 'EQ _ ('Node l _ r) = Repair (Biggest l) r

type family Repair (parts :: (Nat, Tree)) (xs :: Tree) :: Tree where
  Repair '(c, l) r = 'Node l c r

type family Biggest (xs :: Tree) :: (Nat, Tree) where
  Biggest ('Node l c 'Empty) = '(c, l)
  Biggest ('Node l c r) = Biggest' l c (Biggest r)

type family Biggest' (l :: Tree) (c :: Nat) (r' :: (Nat, Tree)) :: (Nat, Tree) where
  Biggest' l c '(x, r) = '(x, 'Node l c r)

{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.
data HList (xs :: [Type]) where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

-- | Write a function that appends two 'HList's.
type family (++) (xs :: [a]) (ys :: [a]) :: [a] where
  '[] ++ xs = xs
  (x ': xs) ++ ys = x ': (xs ++ ys)

-- Actually I've written a version that works for `any` type...
-- By adding "PolyKinds", to be used in L196 🥸

{- EIGHT -}

-- | Type families can also be used to build up constraints. There are, at this
-- point, a couple things that are worth mentioning about constraints:
--
-- - As we saw before, '()' is the empty constraint, which simply has "no
--   effect", and is trivially solved.
--
-- - Unlike tuples, constraints are "auto-flattened": ((a, b), (c, (d, ())) is
--   exactly equivalent to (a, b, c, d). Thanks to this property, we can build
--   up constraints using type families!
type family CAppend (x :: Constraint) (y :: Constraint) :: Constraint where
  CAppend x y = (x, y)

-- | a. Write a family that takes a constraint constructor, and a type-level
-- list of types, and builds a constraint on all the types.
type family Every (c :: Type -> Constraint) (x :: [Type]) :: Constraint where
  Every _ '[] = ()
  Every f (x ': xs) = (f x, Every f xs)

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.
instance Every Show xs => Show (HList xs) where
  show HNil = "[]"
  show (HCons x xs) = show x ++ " : " ++ show xs

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
instance Every Eq xs => Eq (HList xs) where
  HNil == HNil = True
  HCons x xs == HCons y ys = x == y && xs == ys

instance (Every Eq xs, Every Ord xs) => Ord (HList xs) where
  compare HNil HNil = EQ
  compare (HCons x xs) (HCons y ys) = compare x y <> compare xs ys

{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type family RangeFrom1To (x :: Nat) :: [Nat] where
  RangeFrom1To 'Z = '[ 'Z]
  RangeFrom1To ('S n) = RangeFrom1To n ++ '[ 'S n]

-- | b. Write a type-level prime number sieve.
type family Sieve (x :: Nat) :: [Nat] where
  Sieve x = Sieve' (Drop ('S ('S 'Z)) (RangeFrom1To x))

type family Sieve' (xs :: [Nat]) :: [Nat] where
  Sieve' '[] = '[]
  Sieve' (x ': xs) = x ': Sieve' (DropEvery x xs)

type family Drop (n :: Nat) (xs :: [Nat]) :: [Nat] where
  Drop 'Z xs = xs
  Drop _ '[] = '[]
  Drop ('S n) (_ ': xs) = Drop n xs

type family DropEvery (n :: Nat) (xs :: [Nat]) :: [Nat] where
  DropEvery n xs = DropEvery' n n xs

type family DropEvery' (c :: Nat) (n :: Nat) (xs :: [Nat]) :: [Nat] where
  DropEvery' n ('S 'Z) (_ ': xs) = DropEvery' n n xs
  DropEvery' _ _ '[] = '[]
  DropEvery' n ('S c) (x ': xs) = x ': DropEvery' n c xs

-- | c. Why is this such hard work?
-- No type-level higher-order-functions...🤷🏻‍♂️
