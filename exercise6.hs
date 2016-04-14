{- 1 -}

{-

Lazy
1. Evaluate t1
2. t2 is substituted without evaluation
3. No evaluation under an abstraction

The eager evaluation strategy for an application t1 t2 works as follows.
1. Evaluate t1
2. t2 is evaluated prior to substitution
3. Evaluation is carried out under an abstraction

f g

f = \x -> x (\y -> x y)
g = \x -> (\y -> y) x



(i) Lazy

f g =
  ( \x -> x (\y -> x y) ) (  \x -> (\y -> y) x ) =       substitute t2
  (\x -> (\y -> y) x) (\y -> (\x -> (\y -> y) x) y) =    substitute t2
  (\y -> y) (\y -> (\x -> (\y -> y) x) y) =              evaluate   t1
  (\y -> (\x -> (\y -> y) x) y)


(ii) Eager

f g = ?
  Unclear, when/how \y -> y can be evalualated


-}

{- 2: https://codeboard.io/projects/16119 -}

{-
Lemma: sum (toList t) .=. addSum t 0
Proof
QED


-}
data Tree = Node Tree Tree | Leaf Int

addSum (Leaf x) n = x + n -- addSum.1
addSum (Node l r) n = addSum l (addSum r n) -- addSum.2

toList (Leaf x) = [x] -- toList.1
toList (Node l r) = toList l +++ toList r -- toList.2

sum' [] = 0 -- sum.1
sum' (x:xs) = x + sum xs -- sum.2

[] +++ ys = ys -- ++.1
(x:xs) +++ ys = x : (xs +++ ys) -- ++.2

{-
sum (toList t) = addSum t 0

Ideas:

toList -> Baum in Liste umwandeln
sum -> list in Zahl, Reihenfolge egal

Zu zeigen, das beide Operationen die Summe aller Elemente bilden

sum (toList t) -> macht eine Liste und summiert danach

addSum t 0 ->
  Nimmt gesammelte Werte und addiert Blattwert
  Beim Knoten: Bildet die Summe links und fügt die Summe rechts hinzu

Das Lemma:

Lemma sumAppend: ∀xs, ys :: [Int]. sum (xs ++ ys) = sum xs + sum ys

Wenn wir die Summe zweier Listen bilden, ist es das gleiche wie die Summe der
ersten plus die Summe der zweiten Liste.

Hinweis: generalisieren vorher.
Frage: was kann noch generalisiert werden.
Eventuell x:xs und y:ys?

Oder ist es gemeint, den Beweis zu generalisieren?

sum (toList t) = addSum t 0

Worüber müssen wir Induktion machen?

Erst über das Blatt, dann über den Baum?

Nachschauen der Generalisierungen in...
  w5: lazy -> nack
  w4-noanim:
   Enum types
   Product types

instance Eq Foo where
D1 == D1 = True
D2 == D2 = True
D3 == D3 = True
_ == _ = False

-----> Foo type implementiert Eq

Induction over trees:

Γ |- P(Leaf )       Γ, P(l), P(r) |- P(Node a l r)
-------------------------------------------------- a, l, r not free in Γ or P
Γ |- ∀x ∈ Tree t. P(x)


w4: trees, but not generalisation

sumAppend findet sich wieder in toList indirekt

Base case: t = Leaf x

sum (toList (Leaf x)) =
   sum [x] =                  -- toList.1
   sum                        -- +0 / nach (x:xs)
   ...
   = x

addSum (Leaf x) 0 = x + 0 = x


sum (toList (Node l r)) =
  (by def toList)          sum (toList l ++ toList r)

  -- jetzt wieder Unterscheidung von Leaf/Node machen bei toList! -> Rekursion? !!


  4 cases

  l = Leaf x
  r = Leaf y

  toList (Leaf x) / toList (

  toList (Leaf x) / toList (Node l r) <- geht weiter auf!

-- Proof by induction on tree t

-- addSum t 0 generalisieren?

addSum t n

n + sum (toList t) = addSum t n



addsum t 0 =

-- addSum t 0 generalisieren -> beliebiges t?




sum (toList t) = addSum t 0




-}


{- v3


Lemma: sum (toList t) .=. addSum t 0

Lemma: n + sum (toList t) .=. addSum t n
Lemma:

Proof by induction on Tree x
Case Leaf x
  To show: n + sum (toList (Leaf x)) .=. addSum (Leaf x) n

  Proof
    n + sum (toList (Leaf x))
    (by def toList)           .=. n + sum [x]
    (by def sum)              .=. sum (n:x)

    addSum (Leaf x) n
    (by def addSum)         .=. (x + n)
    (by arith)              .=. (x + n) + 0
    (by arith)              .=. x + (n + 0)
    (by def sum)            .=. x + (n + sum [])
    (by def sum)            .=. x + sum(n:[])
    (by def sum)            .=. sum(x:n:[])


  QED

Case Node l r
  To show: sum (toList (Node l r)) .=. addSum (Node l r) 0

  IH1: Lemma: sum (toList l) .=. addSum l 0
  IH2: Lemma: sum (toList r) .=. addSum r 0

  Proof
    sum (toList (Node l r))
    (by def toList)            .=. sum (toList l ++ toList r)
    (by sumAppend)             .=. sum (toList l) + sum (toList r)
    (by IH2)                   .=. sum (toList l) + addSum r 0
    (by IH1)                   .=. addSum l 0 + addSum r 0
    (by arith)                 .=. addSum l (0 + addsum r 0)
    (by arith)                 .=. addSum l (addSum r 0)         -- ??????? 0 + statt + 0
    (by def addSum)            .=. addSum (Node l r) 0

    QED
QED

-}

{-





Lemma: sum (toList t) .=. addSum t 0

Proof by induction on Tree x
Case Leaf x
  To show: sum (toList (Leaf x)) .=. addSum (Leaf x) 0

  Proof
    sum (toList (Leaf x))
    (by def toList)         .=. sum [x]
    (by arith)              .=. sum [x] + 0
    (by def sum)            .=. sum [x] + sum []
    (by sumAppend)          .=. sum ([x] ++ [])


    addSum (Leaf x) 0
    (by def addSum)         .=. x + 0
    (by def sum)            .=. x + sum []
    (by arith)              .=. x + sum [] + 0

    (by def sum)            .=. sum (x:0)


    (by arith)              .=. x

  QED

Case Node l r
  To show: sum (toList (Node l r)) .=. addSum (Node l r) 0

  IH1: Lemma: sum (toList l) .=. addSum l 0
  IH2: Lemma: sum (toList r) .=. addSum r 0

  Proof
    sum (toList (Node l r))
    (by def toList)            .=. sum (toList l ++ toList r)
    (by sumAppend)             .=. sum (toList l) + sum (toList r)
    (by IH2)                   .=. sum (toList l) + addSum r 0
    (by IH1)                   .=. addSum l 0 + addSum r 0
    (by arith)                 .=. addSum l (0 + addsum r 0)
    (by arith)                 .=. addSum l (addSum r 0)         -- ??????? 0 + statt + 0
    (by def addSum)            .=. addSum (Node l r) 0

    QED
QED


Lemma: sum (xs ++ ys) .=. sum xs + sum ys
Proof by induction on List xs generalizing ys
  Case []
  For arbitrary ys
    To show: sum ([] ++ ys) .=. sum [] + sum ys

    Proof
      sum ([] ++ ys)
      (by def ++)          .=. sum ys

      sum [] + sum ys
      (by def sum)         .=. 0 + sum ys
      (by arith)           .=. sum ys
    QED

  Case x:xs
    For arbitrary ys

    To show: sum ((x:xs) ++ ys) .=. sum (x:xs) + sum ys

    IH: forall ys: sum (xs ++ ys) .=. sum xs + sum ys

    Proof
      sum ((x:xs) ++ ys)
      (by def ++)          .=. sum (x: (xs ++ ys))
      (by def sum)         .=. x + sum (xs ++ ys)
      (by IH)              .=. x + sum xs + sum ys

      sum (x:xs) + sum ys
      (by def sum)         .=. x + sum xs + sum ys
    QED
QED

-}


{- v3


Lemma: sum (toList t) .=. addSum t 0

Lemma: n + sum (toList t) .=. addSum t n
Lemma:

Proof by induction on Tree x
Case Leaf x
  To show: n + sum (toList (Leaf x)) .=. addSum (Leaf x) n

  Proof
    n + sum (toList (Leaf x))
    (by def toList)           .=. n + sum [x]
    (by def sum)              .=. sum (n:x)

    addSum (Leaf x) n
    (by def addSum)         .=. (x + n)
    (by arith)              .=. (x + n) + 0
    (by arith)              .=. x + (n + 0)
    (by def sum)            .=. x + (n + sum [])
    (by def sum)            .=. x + sum(n:[])
    (by def sum)            .=. sum(x:n:[])


  QED

Case Node l r
  To show: sum (toList (Node l r)) .=. addSum (Node l r) 0

  IH1: Lemma: sum (toList l) .=. addSum l 0
  IH2: Lemma: sum (toList r) .=. addSum r 0

  Proof
    sum (toList (Node l r))
    (by def toList)            .=. sum (toList l ++ toList r)
    (by sumAppend)             .=. sum (toList l) + sum (toList r)
    (by IH2)                   .=. sum (toList l) + addSum r 0
    (by IH1)                   .=. addSum l 0 + addSum r 0
    (by arith)                 .=. addSum l (0 + addsum r 0)
    (by arith)                 .=. addSum l (addSum r 0)         -- ??????? 0 + statt + 0
    (by def addSum)            .=. addSum (Node l r) 0

    QED
QED

-}

{-





Lemma: sum (toList t) .=. addSum t 0

Proof by induction on Tree x
Case Leaf x
  To show: sum (toList (Leaf x)) .=. addSum (Leaf x) 0

  Proof
    sum (toList (Leaf x))
    (by def toList)         .=. sum [x]
    (by arith)              .=. sum [x] + 0
    (by def sum)            .=. sum [x] + sum []
    (by sumAppend)          .=. sum ([x] ++ [])


    addSum (Leaf x) 0
    (by def addSum)         .=. x + 0
    (by def sum)            .=. x + sum []
    (by arith)              .=. x + sum [] + 0

    (by def sum)            .=. sum (x:0)


    (by arith)              .=. x

  QED

Case Node l r
  To show: sum (toList (Node l r)) .=. addSum (Node l r) 0

  IH1: Lemma: sum (toList l) .=. addSum l 0
  IH2: Lemma: sum (toList r) .=. addSum r 0

  Proof
    sum (toList (Node l r))
    (by def toList)            .=. sum (toList l ++ toList r)
    (by sumAppend)             .=. sum (toList l) + sum (toList r)
    (by IH2)                   .=. sum (toList l) + addSum r 0
    (by IH1)                   .=. addSum l 0 + addSum r 0
    (by arith)                 .=. addSum l (0 + addsum r 0)
    (by arith)                 .=. addSum l (addSum r 0)         -- ??????? 0 + statt + 0
    (by def addSum)            .=. addSum (Node l r) 0

    QED
QED


Lemma: sum (xs ++ ys) .=. sum xs + sum ys
Proof by induction on List xs generalizing ys
  Case []
  For arbitrary ys
    To show: sum ([] ++ ys) .=. sum [] + sum ys

    Proof
      sum ([] ++ ys)
      (by def ++)          .=. sum ys

      sum [] + sum ys
      (by def sum)         .=. 0 + sum ys
      (by arith)           .=. sum ys
    QED

  Case x:xs
    For arbitrary ys

    To show: sum ((x:xs) ++ ys) .=. sum (x:xs) + sum ys

    IH: forall ys: sum (xs ++ ys) .=. sum xs + sum ys

    Proof
      sum ((x:xs) ++ ys)
      (by def ++)          .=. sum (x: (xs ++ ys))
      (by def sum)         .=. x + sum (xs ++ ys)
      (by IH)              .=. x + sum xs + sum ys

      sum (x:xs) + sum ys
      (by def sum)         .=. x + sum xs + sum ys
    QED
QED

-}

{- v4
Lemma: sum (toList t) = addSum t 0


Hints:
sumAppend: ∀xs, ys :: [Int]. sum (xs ++ ys) = sum xs + sum ys
generalize the statement before using induction.

Generalization can be on 0 only, becasue t is quantified

n + sum (toList t) = addSum t n





λ> 2:[]
[2]


Lemma: sum (toList t) .=. addSum t 0

Proof by induction on Tree x
Case Leaf x
  To show: sum (toList (Leaf x)) .=. addSum (Leaf x) 0

  Proof
    sum (toList (Leaf x))
    (by def toList)         .=. sum (x:[])
    (by def sum)            .=. x + sum []
    (by def sum)            .=. x + 0

    addSum (Leaf x) 0
    (by def addSum)         .=. x + 0
  QED

QED

-------------> first subgoal is different:
Subgoal: sum (toList t~0) .=. addSum t~0 0

-> induction over n???


-}




{- 3 File System Entries codeboard.io/projects/16117 -}

data FSEntry = Folder String [FSEntry] | File String String

fstest = Folder "Home"
          [Folder "Work"
            [File "students.txt" "Alice, Bob",
             File "hint"  "You can use fFSE!"],
          File "Fun" "FMFP"]

-- (a)


fFSE :: (String -> [a] -> a) -> (String -> String -> a) -> FSEntry -> a
fFSE folderf filef (File name content) = filef name content
fFSE folderf filef (Folder name entries) = folderf name $ map (fFSE folderf filef) entries



-- (b)

-- i.

number :: FSEntry -> Int
number entry = fFSE cntFolder cntFile entry where
  cntFile _ _ = 1
  cntFolder _ = foldr (+) 1


-- ii.

count :: Char -> FSEntry -> Int
count search entry = fFSE folderf filef entry where
  filef _ = foldr (\x y -> if x == search then y+1 else y) 0
  folderf _ = foldr (+) 0


-- (c)

{-
 filef needs to return list of strings to match signature of paths
 folderf returns list  of files!!!
 filef only one file!
 -> we need to prepend path for every item in the list
 -> we need to take all strings [filenames] in the list!

------------->>>>>>>>>>> List of Lists of Strings!!!

every file returns entry of itself
every directory returns entries of all children ["list of strings"]


folderf gets list of filenames (?)

folderf gets list of list of strings

folderf needs to return list of strings!


-}

paths :: FSEntry -> [String]
paths entry = fFSE folderf filef entry where
  filef name _ = [name]
  folderf dirname entries = map (\x -> dirname ++ "/" ++ x) $ foldl (\x y -> x ++ y) [] entries



-- not so pretty variant, but works
paths1 :: FSEntry -> [String]
paths1 entry = fFSE folderf filef entry where
  filef name _ = [name] -- needs to be a list of strings, because we use fFSE w/ same signature
  folderf dirname entries = prependedList entries where
    prependedList entries = map (\x -> dirname ++ "/" ++ x) $ flatList entries

    flatList entries = foldl (\x y -> x ++ y) [] entries

--     map (\x -> dirname ++ "/" ++ x)
--  folderf dirname = map (\x -> dirname ++ "/" ++ x)
-- folderf dirname = map (\filelist -> [ dirname ++ '/' ++ filename | filename <- filelist ])
-- folderf name entries  = map (\x -> foldr (++) "" x) entries
-- folderf name entries  = map (\x -> name ++ "/" ++ (foldr (++) "" x)) entries


{- 4: https://codeboard.io/projects/16120 -}

{-
   Implement a function that generates all possible board assignments.



3:

[ 1 1 1 ]
[ 1 1 2 ]
[ 1 1 3 ]
[ ...   ]
[ 3 3 3 ]

x times x combination?

For every queen (= n) every possible position (=n)


-}

generate :: Int -> [[Int]]
generate n = createPositions n n where
  createPositions n 1 = [[x] | x <- [1..n]]
  createPositions n m = [(x:y) | y <- createPositions n (m-1), x <- [1..n]]

{-
   Implement a function that tests whether a given assignment is valid.
-}

test :: [Int] -> Bool
test (x:xs) = False


-- naivequeens :: Int -> [[Int]]
-- naivequeens n = filter test $ generate n


-- {-
--    Headache of the week:
--    Implement a function that solves this n queens problem in a more efficient way
--    such that partial assignments get tested, whether they may be a valid full assignment,
--    as early as possible
-- -}

-- queens :: Int -> [[Int]]
-- queens = undefined
