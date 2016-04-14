{- 1: https://codeboard.io/projects/15109 DFA: submitted -}

import Prelude hiding (Word)
import Data.Char -- chr, ord

{- (a) -}
type State = Int
type Alphabet a = [a]
type Word     a = [a]
type DFA a =
  ( Alphabet a -- alphabet
  , State -- initial state
  , State -> a -> State -- transition function
  , State -> Bool) -- test for final state


alphabet :: DFA a -> Alphabet a
alphabet (a, _, _ ,_ ) = a

initial :: DFA a -> State
initial (_, initialstate, _, _) = initialstate

transition :: DFA a -> (State -> a -> State)
transition (_, _, delta, _) = delta

finalState :: DFA a -> State -> Bool
finalState (_, _, _, state) = state

{- advantage: abstracts away the data structure, makes code more readable -}

{- (b) -}

{- for testing -}
takefirststep :: DFA a -> Word a -> State -- why does takeonestep :: DFA a -> Word b -> State  not work?
takefirststep dfa (x:xs) = transition dfa (initial dfa) x

{- traverse using standard recursion -}
traverse2 :: DFA a -> Word a -> State -> State
traverse2 dfa [] qx = qx
traverse2 dfa (x:xs) qx = traverse2 dfa xs (delta qx x)
  where
    delta = transition dfa

{- traverse using foldl -> start from left and continue to right -}
traverse3 :: DFA a -> Word a -> State -> State
traverse3 dfa word qx = foldl delta q0 word
  where
    delta = transition dfa
    q0 = initial dfa

{- traverse w/ check for final state -}
accepts :: DFA a -> Word a -> Bool
accepts dfa word = isfinal qreal
  where
    q0        = initial dfa
    isfinal   = finalState dfa
    qreal     = traverse3 dfa word q0


{- (c) -}

{- prepend alphabet to every element in existing list -}
addalphabet :: Alphabet a -> [Word a] -> [Word a]
addalphabet alphabet words = [ [x] ++ y | x <- alphabet , y <- words ]

{- explicit recursion -}
lexicon1 :: Alphabet a -> Int -> [Word a]
lexicon1 alphabet 0 = [[]] -- λ> [[]] == [""]  -> True
lexicon1 alphabet 1 = [ [x] | x <- alphabet ] -- abortion for recursion
lexicon1 alphabet n = addalphabet alphabet (lexicon alphabet (n-1))

{- using foldr instead of explicit recursion - the former looks easier though,
   as recursion is nicely suited for numbers wheras foldr seems to be more suited for
   lists. The exercise stated to use an integer instead of sample length list, which
   might have made fold more suitable -}
lexicon :: Alphabet a -> Int -> [Word a]
lexicon alphabet 0 = [[]]
lexicon alphabet 1 = [ [x] | x <- alphabet ]
lexicon alphabet n = foldr (\_ y -> addalphabet alphabet y) (lexicon alphabet 1) [ [x] | x <- [2..n] ]

{- unfinished:
lexicon "" 0 should evaluate to [""] : failed got []
lexicon "ab" 0 should evaluate to [""] : failed got []
-}

{- (d): return words for which the DFA goes into accepting state -}

language :: DFA a -> Int -> [Word a]
language dfa n = validwords
  where
    dictionary = lexicon (alphabet dfa) n
    validwords = [ x | x <- dictionary, accepts dfa x ]

{- Summing up a list:
λ> foldr (\x y -> 1+y) 0 [1,2,3]
3
-}

-- Testing data
myokword = "12"
mynotokword = "111111111111"
myalphabet = foldr (++) "" (map show [1..3]) -- just required for fun?
myalpha2 = ["1", "2", "3"]


mydelta :: State -> Char -> State
mydelta 1 '1' = 2 -- 1 goes to q2, others stay
mydelta 1 '2' = 1
mydelta 1 '3' = 1

mydelta 2 '1' = 2
mydelta 2 '2' = 3 -- 2 goes to q3, others stay
mydelta 2 '3' = 2

mydelta 3 _ = 3 -- always stay in final state

myinitialstate = 1 :: State

myisfinalstate a = (a == (3 :: State))

mydfa = ( myalphabet, myinitialstate, mydelta, myisfinalstate)


{- ???????????? https://codeboard.io/projects/13585 -}


{-
Lemma itrev_rev: itrev xs ys .=. reverse xs ++ ys
Proof by induction on List xs

Case [] -- Base case
  To show: itrev [] ys .=. reverse [] ++ ys
  Proof
    itrev [] ys
    (by def itrev) .=. ys

    reverse [] ++ ys
    (by def reverse) .=. [] ++ ys
    (by def ++)      .=. ys

    QED

Case x:xs -- Induction step
  To show: itrev (x:xs) ys .=. reverse (x:xs) ++ ys
  IH: itrev xs ys .=. reverse xs ++ ys

  Proof
    itrev (x:xs) ys
    (by def itrev) .=. itrev xs (x:ys)


    reverse (x:xs) ++ ys


  QED

QED


-- defs:

data List a = [] | a : List a

itrev [] ys = ys
itrev (x:xs) ys = itrev xs (x:ys)

reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

axiom app_assoc: (xs ++ ys) ++ zs .=. xs ++ (ys ++ zs)

goal itrev xs [] .=. reverse xs

-}

{- 2:  https://codeboard.io/projects/15111 : submitted -}
{-


------------- GIVEN --------------------
Lemma rev rev: ∀xs::[a]. rev (rev xs) = xs.
Lemma app Nil: ∀xs::[a]. xs ++ [] = xs.
Lemma app assoc: ∀xs,ys,zs::[a]. (xs ++ ys) ++ zs = xs ++ (ys ++ zs).


rev :: [a] -> [a]
rev [] = [] -- rev.1
rev (x:xs) = rev xs ++ [x] -- rev.2

(++) :: [a] -> [a] -> [a]
(++) [] ys = ys -- app.1
(++) (x:xs) ys = x : (xs ++ ys) -- app.2

------------- Proof1 --------------------

Lemma: rev (xs ++ rev ys) .=. ys ++ rev xs
Proof by induction on List ys
Case []
  To show: rev (xs ++ rev []) .=. [] ++ rev xs

  Proof

  rev (xs ++ rev [])
  (by def rev)         .=. rev (xs ++ [])
  (by Nil)             .=. rev xs

  [] ++ rev xs
  (by def ++)        .=. rev xs

  QED

Case x:xs
  To show: rev (xs ++ rev y:ys) .=. y:ys ++ rev xs
  IH: rev (xs ++ rev ys) .=. ys ++ rev xs

  Proof

    rev (xs ++ rev y:ys)
    (by def rev)           .=. rev (xs ++ rev ys ++ [y])


    y:ys ++ rev xs
    (by rev_rev)           .=. rev (rev (y:ys ++ rev xs))


  QED

QED

------------- Proof2 --------------------

Lemma: rev (xs ++ rev ys) .=. ys ++ rev xs
Proof by induction on List xs

Case []
  To show: rev ([] ++ rev ys) .=. ys ++ rev []

  Proof

  rev ([] ++ rev ys)
  (by def ++)              .=. rev (rev ys)
  (by rev_rev)             .=. ys
  (by app_Nil)             .=. ys ++ []
  (by def rev)             .=. ys ++ rev []

  QED

Case x:xs
  To show: rev ((x:xs) ++ rev ys) .=. ys ++ rev (x:xs)
  IH: rev (xs ++ rev ys) .=. ys ++ rev xs

  Proof
    rev ((x:xs) ++ rev ys)
    (by def ++)                           .=. rev (x : (xs ++ rev ys))
    (by def rev)                          .=. rev (xs ++ rev ys) ++ [x]
    (by IH)                               .=. (ys ++ rev xs) ++ [x]
    (by app_assoc)                        .=. ys ++ (rev xs ++ [x])
    (by def rev)                          .=. ys ++ rev (x:xs)
  QED

QED


-}



{- 3: https://codeboard.io/projects/15403 submitted -}

{- concat is similar to ++ - just takes a list of lists to concatenate -}

{- (a) -}

-- already defined in prelude
-- concatMap f = concat . map f

concatMap' f = foldr aux e
  where
    aux = ((++) . f)
    e = []


-- foldl :: Foldable t => (b -> a -> b) -> b -> t a -> b
-- foldr :: Foldable t => (a -> b -> b) -> b -> t a -> b

{- b -}
{- λ-abstraction, id, and foldr. -}

{- f = function, v = initial, l = list -}


{- definition like foldl for verification -}
myFoldl :: Foldable t => (b -> a -> b) -> b -> t a -> b
myFoldl f v l = foldr (\a b -> f b a) v l


{- Foldr vs. foldl


foldr (++) "xyz" ["abc","def","ghi"]
=

foldr f e [] = e
foldr f e (x:xs) = f x (foldr f e xs)


foldl f e [] = e
foldl f e (x:xs) = foldl f (f e x) xs




We want:
((e+l1)+l2)+l3

We have w/ foldr
l1+(l2+(l3 + e)

l1+(l2+(e + l3) <---- don't evaluate + here!

f (f (f l3 e) l2) l1 <------- foldr
f f3 (f l2 (f e l1)) <------- foldl

f (f (f l3 e) l2) l1 <------- foldr


f l1 (f l2 (f e l3)) <---- current version

(.)


f f3 (f l2 (f e l1)) <------- foldl





l1+(l2+(e (+ l3)) -> l1 + (l2 + e) + l3 -> l1 + (e + l2) + l3 -> l1 + e (12 + 13)
-> e + l1 + ...


Using $?


Turn it into:

l1+(l2+(l3 + e)





-> (e + ln) -> e + l2 + ln

function composition?

(ln + e) -> (e + ln) check


-}


{- https://codeboard.io/projects/15197  ???? -}

{- 4: codeboard.io/projects/15110 : submitted -}

{- reverse: f -}

f1 :: [[a]] -> [a]
f1 [] = []
f1 (x:xs) = reverse x ++ f xs

g1 :: Eq a => [a] -> [a]  -> [a]
g1 [] _ = []
g1 _ [] = []
g1 (x:xs) (y:ys)
        | x == y = x : g xs ys
        | otherwise = g xs ys


f :: [[a]] -> [a]
f x = foldr (++) [] $ map reverse x

g :: Eq a => [a] -> [a] -> [a]
g a b = map fst $ filter (\x -> (fst x) == (snd x)) (zip a b)

{- aux of h = count even numbers -}
counteven :: [Int] -> Int
counteven a = foldr (+) 0 $ map (\x -> if even x then 1 else 0) a

{- also possible via filter + counting length - what's the better approach? -}
counteven2 :: [Int] -> Int
counteven2 a = length $ filter (\x -> even x) a

h :: [Int] -> Int
h = counteven


{- 5: Give the most general type for each of the following functions.

1. (\x y z -> (x y) z) :: (t1 -> t2 -> t3) -> t1 -> t2 -> t3

2. (\f -> fst (f,f)) :: t1 -> t1
returns f -> looks like the id function


3. (\p f -> filter p . map f) :: (a -> Bool) -> [b

I can see from haskell that it is [supposed to be]
  :: (a -> Bool) -> (a1 -> a) -> [a1] -> [a]

I see that p has to be (a -> Bool), because of signature of filter
and f has to be [a], because of signature of map.
The result of filter is also a map, but I am not sure about the
function composition binding and how that results into the
signature seen above.

Without Haskell I would have derived:

(a -> Bool) -> [a] -> ??? -> [a]

-}
