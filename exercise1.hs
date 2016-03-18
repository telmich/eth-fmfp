{- Ex1:
 - EncE (Atom "k1")
 - EncE (Atom "k2")
 - Ax
 - PairER (Atom "k1")
 - Ax
 - EncE (Atom "k1")
 - Ax
-}

{- Ex2:
 EncI
 EncE (Atom "k1")
 Ax
 Ax
 EncE (Atom "k1")
 Ax
 Ax

-}

{- Ex3:

EncE (Pair (Pair (Atom "a") (Atom "b")) (Atom "c"))
Ax
PairI
PairI
PairEL (Pair (Atom "b") (Atom "c"))
Ax
PairEL (Atom "c")
PairER (Atom "a")
Ax
PairER (Atom "b")
PairER (Atom "a")
Ax

-}

{-
https://www.ethz.ch/content/dam/ethz/special-interest/infk/inst-infsec/information-security-group-dam/education/ss2016/fmfp/sheet1.pdf

1a) negative: infinite loop

-}


gcdiv :: Int -> Int -> Int
gcdiv x y                         
 | x == y      = x
 | y > x       = gcdiv x (y-x)
 | otherwise   = gcdiv (x-y) y


gcdInt :: Int -> Int -> Int
gcdInt a b
 | a < 0 = gcdInt (-a) b
 | b < 0 = gcdInt a (-b)
 | otherwise = gcdiv a b

gcdInt2 :: Int -> Int -> Int
gcdInt2 a b = gcdiv (abs (a)) (abs (b))

{- 3.6 7.2 -> geht, 3.6 7.199 -> läuft unendlich -}

gcdouble :: Double -> Double -> Double
gcdouble x y                         
 | x == y      = x
 | y > x       = gcdouble x (y-x)
 | otherwise   = gcdouble (x-y) y



-- module Complex where
-- write your implementation of complex numbers here

re :: (Double, Double) -> Double
re (a, _) = a

im :: (Double, Double) -> Double
im (_, b) = b

re2 :: (Double, Double) -> Double
re2 (a, b) = fst (a,b)

im2 :: (Double, Double) -> Double
im2 (a, b) = snd(a, b)


conj :: (Double, Double) -> (Double, Double)
conj (a, b) = (a, -b) 


add :: (Double, Double) -> (Double, Double) -> (Double, Double)
add (a, b) (c, d) = (a+c, b+d)

mult :: (Double, Double) -> (Double, Double) -> (Double, Double)
mult (a, b) (c, d) = (a*c - b*d, a*d + b*c)

absv :: (Double, Double) ->  Double
absv (a, b) = sqrt (a*a + b*b)


myMain :: IO ()
myMain = do
  putStrLn("Enter your complex number's real component:")
  real <- getLine
  putStrLn("Enter your complex number's imaginary component:")
  img <- getLine
  putStrLn("Your complex number's absolute value is: " ++ show (absv (read real :: Double, read img ::Double)))
  


{- notes:

intbool a b = if (b ==True) then a else 0


not b = case b of
  True -> False
  False -> True
-}



{- Assignment 3

fibLouis :: Int -> Int
fibLouis 0 = 0
fibLouis 1 = 1
fibLouis n = fibLouis (n-1) + fibLouis (n-2)


fibLouis 4
  = fibLouis (4-1) + fibLouis (4-2)
  = fibLouis 3 + fibLouis (4-2)
  = fibLouis (3-1) + fibLouis (3-2) + fibLouis (4-2)
  = fibLouis 2 + fibLouis (3-2) + fibLouis (4-2)
  = fibLouis (2-1) + fibLouis(2-2) + fibLouis (3-2) + fibLouis (4-2)
  = fibLouis 1 + fibLouis(2-2) + fibLouis (3-2) + fibLouis (4-2)
  = 1 + fibLouis(2-2) + fibLouis (3-2) + fibLouis (4-2)
  = 1 + fibLouis 0 + fibLouis (3-2) + fibLouis (4-2)
  = 1 + 0 + fibLouis (3-2) + fibLouis (4-2)
  = 1 + fibLouis (3-2) + fibLouis (4-2)
  = 1 + 0 + fibLouis (3-2) + fibLouis (4-2)
  = 1 + fibLouis (3-2) + fibLouis (4-2)
  = 1 + fibLouis 1 + fibLouis (4-2)
  = 1 + 1 + fibLouis (4-2)
  = 2 + fibLouis (4-2)
  = 2 + fibLouis 2
  = 2 + fibLouis (2-1) + fibLouis (2-2)
  = 2 + fibLouis 1 + fibLouis (2-2)
  = 2 + 1 + fibLouis (2-2)
  = 3 + fibLouis (2-2)
  = 3 + fibLouis 0
  = 3 + fibLouis 0
 =  3 + 0
 = 3



fibEva :: Int -> Int
fibEva n = fst (aux n)
  where
    aux 0 = (0,1)
    aux n = next (aux (n-1))
    next (a,b) = (b, a+b)


fibEva 4
  = fst (aux 4)
  = fst (next (aux (4-1)))
  = fst (next (aux (3)))
  = fst (next (next(aux(3-1))))
  = fst (next (next(aux(2))))
  = fst (next (next(next(aux(2-1)))))
  = fst (next (next(next(aux(1)))))
  = fst (next (next(next(next(aux(1-1))))))
  = fst (next (next(next(next(aux(0))))))
  = fst (next (next(next(next((0,1))))))
  = fst (next (next(next((1,1)))))
  = fst (next (next((1,2))))
  = fst (next ((2,3))
  = fst (3,5)
  = 3




-}

{- Assignment 4

a)
  A ∨ B → C → A ∧ C ∨ B ∧ C
  (A ∨ B) → (C → ((A ∧ C) ∨ (B ∧ C)))

b)
  (A → B → C) → A ∧ B → C
  (A → (B → C)) → ((A ∧ B) → C)


-}


{- Haskell lernen -}

{- Notes: -1 geht nicht, aber (-1) -}

infixr 9 #


(#) :: Bool -> Bool -> Bool
(#) True True = True
(#) False False = True
(#) _ _ = False

-- Lambda-Notation


quadrat = \x -> x*x

quadrat2 x = x * x

xor True y = not y
xor False y = y

greater a b
  | a >= b = a
  | otherwise = b

opnand True True = False
opnand _ _ = True


fak :: Int -> Int
fak 0 = 1
fak n
  | (n>0)     = n * fak (n-1)
  | otherwise = error "Eingabe muss mehr als 0 sein"

faklam = \n -> (if n == 1 then 1 else n* faklam (n-1))


ackermann a b
  | b == 0 = a+1
  | (a == 0) && (b > 0) = ackermann 1 (b-1)
  | otherwise  = ackermann (ackermann (a-1) b) (b-1)


sumTo n = sumTo2 n 0
  where
    sumTo2 0 a = a
    sumTo2 n a = sumTo2 (n-1) (a+n)
