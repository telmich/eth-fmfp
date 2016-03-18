{--------------------- Fast track ---------------------------------------------------}

{- Notes
  nub

  infix always weaker than function application

  Lists next time

-}


-- $ to prevent binding to function argument

{-
calc x y z = a + 2b + 4c
  where
    a = min x $ min y z
    c = max x $ max y z
    b = x + y + z - a - c
-}

sos_max2 a b c = sq a + sq b + sq c - sq (min a $ min b c)
  where sq x = x * x


{- Assignment 1

a) ∀x.p(x) ∧ q(y)
   ∀y.p(y) ∧ q(x)

Rename of x to y is not possible, because x is originally bound.




b) ∀x.∀y.p(x, y) ∧ p(x, z) ∧ ∃z.p(x, z) and
   ∀y.∀x.p(y, x) ∧ p(y, z) ∧ ∃z.p(y, z)


-}

{- v1 -}
improve1 :: Double -> Double -> Double
improve1 x guess = (guess + x/guess)/2

goodEnough1 :: Double -> Double -> Bool
goodEnough1 approx approxbefore = abs ((approx - approxbefore)/approxbefore) < 0.001


{- v2 -}
goodEnough2 :: Double -> Double -> Double -> Bool
goodEnough2 approx approxbefore eps = abs ((approx - approxbefore)/approxbefore) < eps

root2 :: Double -> Double -> Double -> Double
root2 x guess eps
  | goodEnough2 x guess eps = x
  | otherwise = root2 x (improve x guess) eps




{- v3 -}

-- import System.Exit

improve3 :: Double -> Double -> Double
improve3 x yn = (yn + (x / yn)) / 2

goodEnough3 :: Double -> Double -> Bool
goodEnough3 y y_old = abs ((y-y_old)/y_old) < 0.001

root3 x = makegoodenough x x 1
  where
    makegoodenough x yold ynew
      | (goodEnough yold ynew) = ynew
      | otherwise = makegoodenough x ynew (improve x ynew)


{- Should use exception instead of error in main:
https://wiki.haskell.org/Error_vs._Exception

https://hackage.haskell.org/package/base-4.8.2.0/docs/System-Exit.html
-}

{-
main :: IO ()
main = do
  putStrLn "Compute the root of:"
  number <- getLine
  let result = root (read number)
  if root < 0 then exitFailure else putStrLn ("Square root: " ++ (show result))
-}

{- main :: IO ()
main = do
  putStrLn "Compute the root of:"
  x <- getLine
  validate ( convert x )
  main
  where 
    convert x = read x :: Double 
    validate x
      | x < 0     = exitFailure 
      | otherwise = putStrLn ( "Square root: " ++ show ( root x ) )

-}

{- v4 final-}

-- module SquareRoot where

-- import System.Exit

improve :: Double -> Double -> Double
improve x yn = (yn + (x / yn)) / 2

goodEnough :: Double -> Double -> Bool
goodEnough y y_old = abs ((y-y_old)/y_old) < 0.001

root x = makegoodenough x x 1
  where
    makegoodenough x yold ynew
      | (goodEnough yold ynew) = ynew
      | otherwise = makegoodenough x ynew (improve x ynew)


{-
main :: IO ()
main = do
  putStrLn "Compute the root of:"
  x <- getLine
  validate $ convert x
  main
  where 
    convert x = read x :: Double 
    validate x
      | x < 0     = exitFailure 
      | otherwise = putStrLn $ "Square root: " ++ show (root x)
-}

                    
{- 1. Lauf
yn = improve3 x 1

if not goodEnough3 yn yn_old then improve3 x yn
-}


{-
Hint: Think recursively.
The number of ways to change amount A using N different kinds of
coins is equal to the sum of
 - the number of ways to change A using all but the first kind of coin, and
 - the number of ways to change amount A − d using the N kinds of coins,
   where d is the denomination of the first kind of coin

50:
  50
  20 20 10
  20 20 5 5
  20 10 10 10
  20 10 10 5 5
  20 10 5 5 5 5
  20 5 5 5 5 5 5
  10 10 10 10 10
  ...

40:

  dividable by highest?
  yes, 20 = 1

  subtract highest, try again

  
  result = 2 * 20
  dividable by 2nd hi

  


30:
  20 + 10?

  prog number
    for coin in 20 10 5; do
      divide by coin?
      yes: +1
    
    subtract coin


  20 10
  20 5 5

  10 10 10

  10 10 5 5
  10 5 5 5 5
  5 5 5 5 5 5

20:
  20        -- divide by 20 -> yes -> 1
  10 10     -- divide 
  10 5 5
  5 5 5 5

10:
  10
  5 5

-}


-- coins = [ 5, 10, 20, 50, 100, 200, 500 ]
coins = [ 5, 10, 20 ]
coinsUp = reverse coins



cntChange :: Int -> Int
cntChange value = change value
  where
    change value
      | 


{-
cntChange x
 | mod x 5 /= 0 = 0
 | x == 5  = 1
 | x == 10 = 1 + 2 * (cntChange 5)
 | otherwise 
  -}           
-- | otherwise = cntChange (x - 10) + cntChange (x - 5)

-- | x == 20 = 1 + 2 * (cntChange 10)

{-

 | x == 100 = 1 + 2 * cntChange 20/2
 | x == 200 = 1 + 2 * cntChange 10/2
 | x == 500 = 1 + 2 * cntChange 20/2
            
cntChange n = n-5
-}

letztes :: [a] -> a
letztes [x] = x
letztes (_:xs) = letztes xs


primzahlen = sieb [2 ..]
  where sieb (x:xs ) = x: sieb [n|n<-xs , mod n x > 0]

-- List comprehension

