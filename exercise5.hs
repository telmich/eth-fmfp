import Debug.Trace

{- 1: General type -}

{- (a) -}
{-

1. (\x y z -> x (y z)) :: t1 -> t2 -> t3 -> t1 -> t4 ?????
                       :: (b -> c) -> (a -> b) -> (a -> c) <- korrekt!
                       x nimmt einen Parameter: a
                       y nimmt einen Parameter: b
                       x gibt einen Parameter zurück: c

                       :: (a -> c) -> (b -> a) -> ?????

2. (\f -> (\h -> (f,h))) :: a -> b -> (a, b) [KORREKT]

3. map (elem 0)
   Hat einen Parameter bekommen. benötigt noch eine Liste.
   :: [a] -> [Bool]
   Korrekt: Num a => [[a]] -> [Bool]
   elem benötigt auch einen Foldable!

4. (\x -> x (<)) :: Ord a, b => a -> (a -> b) -> Bool FALSCH
λ> :t  (\x -> x (<))
(\x -> x (<)) :: Ord a => ((a -> a -> Bool) -> r) -> r


5. (.) . (.) ::
   Verknüpft die beiden Verknüpfungen miteinander
   (.) :: (b -> c) -> (a -> b) -> a -> c

λ> :t (.) . (.)
(.) . (.) :: (b -> c) -> (a -> a1 -> b) -> a -> a1 -> c
λ>


1. (\x y z -> x (y z))     :: (t1 -> t2 -> t3) -> t1 -> t2 -> t3 FFFFFF
2. (\f -> (\h -> (f,h)))   :: t1 -> t2 -> (t1, t2) ok
3. map (elem 0)            :: [a] -> [Bool] ???? (haskell says: map (elem 0) :: (Eq a, Num a, Foldable t) => [t a] -> [Bool]
4. (\x -> x (<))           :: Ord a => a -> a -> Bool FFFFFFF

-}

{- (b) -}
{-
1. (a -> a -> b) -> a -> b
2. (a -> b) -> [a] -> b
3. (Num a, Eq b) => (b -> Bool) -> [b] -> [a]


1. (a -> a -> b) -> a -> b

Funktion die a und a nimmt und b zurückgibt, z.B. Num -> Num -> Bool
Und a bekommt und b zurückgibt

(\x y -> x > y)  --> zu spezifisch! Ord & Bool: Ord a => a -> a -> Bool

(\x y -> x y)    --> (r1 -> r) -> r1 -> r

(\x y z -> z y x)




2. (a -> b) -> [a] -> b

Funktion, die a nimmt, b zurückgibt
Liste von a nach b umwandelt -> klingt nach fold

λ> :t foldr
foldr :: Foldable t => (a -> b -> b) -> b -> t a -> b

map!!!!!!!


3. (Num a, Eq b) => (b -> Bool) -> [b] -> [a]




-}

{- Haskell / Higher Order Functions -}
applytwice :: (a -> a) -> a -> a
applytwice f x = f (f x)



flip' :: (a -> b -> c) -> (b -> a -> c)
flip' f x y = f y x

filter' :: (a -> Bool) -> [a] -> [a]
filter' _ [] = []
filter' f (x:xs) = if f x then x: filter' f xs else filter' f xs
{-
λ> filter' (>3) [1,2,3,4,5]
[4,5]
-}


largestDivisible :: (Integral a) => a -> a -> a
largestDivisible maximum divisor = head [x | x <- [maximum,(maximum-1)..], x `mod` divisor == 0]

divisible :: (Integral a) => a -> a -> [a]
divisible maximum divisor = [x | x <- [maximum,(maximum-1)..0], x `mod` divisor == 0]


{- The sum of all odd squares that are smaller than 10,000 -}
-- sumOfOddSquares :: (Integral a) => a -> a -> a
sumOfOddSquares upto = sum $ takeWhile (<=upto) [x^2 | x <- [1..], odd x]

sumOfOddSquares2 upto = sum $ takeWhile (<=upto) $ map (^2) $ filter odd [1..]

-- Bad idea: does never stop
-- sumOfOddSquares3 upto = [y | y <- [1..], odd y, y^2 <= upto]


-- map via fold
map' :: (a -> b) -> [a] -> [b]
map' f xs = foldr (\current acc -> f current : acc) [] xs

-- left to right
map'' f xs = foldl (\acc current -> acc ++ [f current]) [] xs
-- map' f xs = foldl (\acc x -> acc ++ [f x]) [] xs

-- One big difference is that right folds work on infinite lists, whereas left ones don't!

oddSquareSum :: Integer -> Integer
oddSquareSum x =
  let oddSquare = filter odd $ map (^2) [1..]
      upperLimit = takeWhile (<x) oddSquare
  in
    sum upperLimit

{- http://learnyouahaskell.com/making-our-own-types-and-typeclasses -}

{- data MyBool = True | False
data Shape = Circle Float Float Float | Rectangle Float Float Float Float -}
--     deriving (Show)

data Point = Point Float Float deriving (Show)
data Shape = Circle Point Float | Rectangle Point Point deriving (Show)

{- own type to float -}
-- surface :: Shape -> Float
-- surface (Circle _ _ r) = pi * r ^ 2
-- surface (Rectangle x1 y1 x2 y2) = (abs $ x2 - x1) * (abs $ y2 - y1)

nudge :: Shape -> Float -> Float -> Shape
nudge (Circle (Point x y) r) xdelta ydelta = Circle (Point (x+xdelta) (y+ydelta)) r
nudge (Rectangle (Point x1 y1) (Point x2 y2)) xdelta ydelta = Rectangle
                                                              (Point (x1+xdelta) (y1+ydelta))
                                                              (Point (x2+xdelta) (y2+ydelta))


-- map ((\x -> nudge x 3 4) . (\x -> Circle (Point x 20) 5)) [1,2,3,4]

data Person = Person { firstName :: String
                     , lastName :: String
                     , age :: Int
                     , height :: Float
                     , phoneNumber :: String
                     , flavor :: String
                     } deriving (Show)
{-
λ> let c = Person { firstName="a", lastName="b", height=3, age=87, phoneNumber="333343", flavor="..." }
λ> c
Person {firstName = "a", lastName = "b", age = 87, height = 3.0, phoneNumber = "333343", flavor = "..."}
λ>
-}

data Vielleicht a = Nichts | Nur a


{- w4 / Algebraic Data Types -}

data Month = January | February | March | April | May | June | July |
  August | September | October | November | December


-- data People = Person Name Age
-- type Name = String
-- type Age = Int


-- me = Person "Myname" 69


sum' :: Int -> Int -> Int
sum' a b = a + b

{- w5 / Lazy Evaluation -}
loop x = (loop x) + 1
divzero = 1 `div` 0
f g x = g 7

-- f (+1) (loop 3)

{-
f x y = x + y

f (9 − 3) (f 34 3)
= (9 − 3) + (f 34 3)         - falsch: zuerst 9 - 3...
= (9 - 3) + (34 + 3)
= (9 - 3) + 37
= 6 + 37
= 43

-}

-- https://www.schoolofhaskell.com/user/mutjida/order-of-evaluation
tr msg x = seq x $ trace msg x

f' x = v2 + 4
  where v2 = tr "v2" $ v1 / 3 + x'
        v0 = tr "v0" $ undefined + 1
        v1 = tr "v1" $ 2 * x'
        x' = tr "x" x

main = putStrLn $ show (f' 10)

data E a b = L a | R b

keepRs [] = []
keepRs (R x : xs) = x : keepRs xs
keepRs (L _ : xs) = keepRs xs

g = sum . keepRs

{------------------------------------- Ü5 - v3 ;-) ---------------------------------------}

{- to read: w4, w5 -}

{- to learn:
 - data types
 - class deriving
-}



{- 1a: to find: most general type for function

1. (\x y z -> x (y z)) :: (b -> c) -> (a -> b) -> a -> c

  z :: a
  y :: a -> b
  x :: b -> c


2. (\f -> (\h -> (f,h))) :: a -> b -> (a, b)

Just left to right reading


3. map (elem 0) :: (Num a, Eq a) => [[a]] -> [Bool]

(elem 0) is partially applied,
  requires [a],
  has a = Num, thus Num a => [a]

  a also needs to be of class Eq, defined by elem

  according to ghci:

  map (elem 0) :: (Eq a, Num a, Foldable t) => [t a] -> [Bool]

  It seems that elem is not a -> [a] -> Bool anymore, but was also
  changed: elem :: (Eq a, Foldable t) => a -> t a -> Bool

4. (\x -> x (<)) :: Ord a => ((a -> a -> Bool) -> b) -> b

(<) requires Ord

(<) :: Ord a => a -> a -> Bool

Thus: x has to take a function of type  a -> a -> Bool

x returns arbitralily -> type b -> must also be return of full expression


5. (.) . (.) ::

(.) :: (b -> c) -> (a -> b) -> a -> c

rightmost (.) takes a function f of type (a->b)
middle . combines rightmost (.) with leftmost (.)
leftmost (.) takes a function g of type (c -> d)


(a -> b) -> (b -> c) ->




-}

{- 1b to find: expression w/ same type

1. (a -> a -> b) -> a -> b

Function that gets two a's and returns a b
Plus a and whole construct returns b:

(\x y -> x y y)


2. (a -> b) -> [a] -> b

Looks like map with the list replaced by a single element

First argument must be a function that goes from a -> b and second argument must be a list:


(\x (y:ys) -> x y)


3. (Num a, Eq b) => (b -> Bool) -> [b] -> [a]

(\x (y:ys) -> if x y && y == y then [0] else [1] )

Not very smart solution, but fulfils the type.

-}

{- 1c Mini-Haskell, let; to find: typing rule for let construct -}





{- 2a: to find: prove for mini-haskell statement = typing rules -}


{- 3: https://codeboard.io/projects/15569 -}

{- a -}
data Prop = Var Bool | Not Prop | And Prop Prop | Or Prop Prop deriving (Show)

{- b -}

foldProp :: Prop -> Prop
foldProp (Var x) = foldVar x
-- foldProp (Not x) = not x -- only works for vars...
-- foldProp

foldVar :: Prop -> Prop
foldVar a = a

foldNot :: Prop -> Prop
foldNot (Not (Var x)) = Var (not x)
foldNot (Not (And x y)) = Or  (Not x) (Not y)
foldNot (Not (Or x y))  = And (Not x) (Not y)

foldAnd :: Prop -> Prop
foldAnd (And x y) =


-- foldOr

-- evalProp :: (a -> Bool) -> Prop a -> Bool u
