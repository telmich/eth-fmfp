{- Exercise / Lession: andreloc: Aus Deutschland -}
import Data.Bits -- xor

{- remove elements until emtpy? -}
last2 :: [a] -> a
-- same as: last (x:[]) = x
last2 [x] = x
last2 (_:xs) = last2 xs

{- everything without the last element -}
init1 :: [a] -> [a]
init1 xs = reverse (tail (reverse xs))

init2 :: [a] -> [a]
init2 [x] = []
init2 (x:xs) = x : init xs

{- get element by position; LISTs are NOT ARRAY -}
nth :: Int -> [a] -> a
nth 0 (y:ys) = y
nth x (y:ys)  = nth (x -1) ys
nth _ [] = error "Index too large"

{- Pascal's Dreieck: 1, 1 1, 1 2 1, 1 3 3 1
 - Row n = n elements
 - Row n (>1) requires n-1 elements from previous row
-}


{-
pascal :: Int -> [Int]
pascal 0 = [1]
pascal 1 = [1,1]
pascal n = nextRow (pascal (n-1))
  where
    nextRow [x]      = [x, x]
    nextRow [x1, x1] = [x1, x2, x2]
    nextRow (x1 : x2 : xs) = (x1+x2) : nextRow (x2 : xs)
-}

pascal2 :: Int -> [Int]
pascal2 0 = [1]
pascal2 n = 1: map add (zip row (tail row)) ++ [1]
  where
    add (x, y) = x + y
    row = pascal2 (n-1)


{- hints:
null [] -> True

head [x] = x -> get first element
tail (x:xs) = xs

: fügt Element und Liste zusammen

last: Letzte Element aus der Liste
init: alle bis auf das letzte Element

++ hänge eine Liste an die andere
λ> [3,4] ++ [4,5]
[3,4,4,5]


-}

zip2 :: [a] -> [b] -> [(a,b)]
zip2 [] [] = []
zip2 (a:as) (b:bs) = (a,b) : zip as bs

-- w2-lists
drop2 :: Int -> [a] -> [a]
drop2 0 (x:xs) = x:xs
drop2 n (x:xs) = drop2 (n-1) xs
drop2 n []     = []

{- Examples
[2*x | x <- [1,2,3,4]]
[2,4,6,8]


λ>  [2*x | x <- [1,2,3,4], x > 3]
[8]



-}


{- Libray:
- whatxborrowed
- whoborrowedx
- isxborrowed
-}

type Library = [(Person, Book)]
type Person  = String
type Book    = String

myDB = [("p1", "b1"), ("p1", "b2"), ("p3", "b2"), ("p3", "b3")]


whathasxborrowed :: Person -> Library -> [Book]
whathasxborrowed p db = [book | (per,book) <- db, per == p]
                       
whohasxborrowed :: Book -> Library -> [Person]
whohasxborrowed b db = [per | (per,book) <- db, book == b]

isxborrowed :: Book -> Library -> Bool
isxborrowed b db
  | [] == whohasxborrowed b db = False
  | otherwise = True

isxborrowed2 :: Book -> Library -> Bool
isxborrowed2 b db = whohasxborrowed b db /= []



type Message = [Bool]
type CryptoText = Message
type Key = [Bool]

{- Assignment 2 -}

encrypt1 :: (Bool, Bool) -> Bool
encrypt1 pair = xor (fst pair) (snd pair)

encrypt2 :: Bool -> Bool -> Bool
encrypt2 msg key = xor msg key


otp1 :: [Bool] -> [Bool] -> [Bool]
otp1 message key = map encrypt1 (zip message key)

otp2 :: [Bool] -> [Bool] -> [Bool]
otp2 message key = zipWith encrypt2 message key

otp = otp2

-- Alternative to map / zip:
{- Needs as arguments:
* Two lists: [a] [a] (or [a] [b])
* One function: a -> b -> c
* Looks promising: zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]

-}

{- Assignment 3 -}

-- isprime1 :: Int -> Bool
isprime n = onlyoneandn n == [1,n]
  where
    onlyoneandn n = [x | x <- [1 .. n], mod n x == 0]

-- for codeboard
prime = isprime


primesupton :: Int -> [Int]
primesupton n = filter isprime [1 .. n]

-- for codeboard
primes = primesupton

firstPrimes :: Int -> [Int]
firstPrimes m = take m [x | x <- [1 ..], isprime x]

{- Assignment 4 -}


-- test: ["riseto", "han" , "votesir", "nah", "isetov"]
palindromes :: [String] -> [String]
palindromes inputlist = [x | x <- inputlist]
