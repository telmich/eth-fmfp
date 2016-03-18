{- https://codeboard.io/projects/15109 DFA -}

import Data.Char -- chr, ord

{- (a) -}
type State = Integer
type Alphabet a = [a]
type DFA a =
  ( Alphabet a -- alphabet
  , State -- initial state
  , State -> a -> State -- transition function
  , State -> Bool) -- test for final state
type Word2 a = [a]


myokword = "12"
mynotokword = "111111111111"
myalphabet = foldr (++) "" (map show [1..3]) -- just required for fun?


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
takefirststep :: DFA a -> Word2 a -> State -- why does takeonestep :: DFA a -> Word2 b -> State  not work?
takefirststep dfa (x:xs) = transition dfa (initial dfa) x

{- traverse using standard recursion -}
traverse2 :: DFA a -> Word2 a -> State -> State
traverse2 dfa [] qx = qx
traverse2 dfa (x:xs) qx = traverse2 dfa xs (delta qx x)
  where
    delta = transition dfa

{- traverse using foldl -> start from left and continue to right -}
traverse3 :: DFA a -> Word2 a -> State -> State
traverse3 dfa word qx = foldl delta q0 word
  where
    delta = transition dfa
    q0 = initial dfa

{- traverse w/ check for final state -}
accepts :: DFA a -> Word2 a -> Bool
accepts dfa word = isfinal qreal
  where
    q0        = initial dfa
    isfinal   = finalState dfa
    qreal     = traverse3 dfa word q0


{- https://codeboard.io/projects/13585 -}
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



{- https://codeboard.io/projects/15197 -}
