data NTest = Create Int Int Int | Nothing'

data Point = Point Float Float deriving (Show)
data Shape = Circle Point Float | Rectangle Point Point deriving (Show)

data Person = Person { firstName :: String
                     , lastName :: String
                     , age :: Int
                     , height :: Float
                     , phoneNumber :: String
                     , flavor :: String
                     } deriving (Show)




-- Found hole ‘_’ with type: Int … when using a+_
evaluate (Create _ _ a) = a
evaluate (Nothing') = 0


-- From exercise lesson [also done w/ recursion)
countSat :: (a -> Bool) -> [a] -> Int
countSat f x = length $ filter f x


countSat' :: (a -> Bool) -> [a] -> Int
countSat' p = length . filter p

countSat'' :: (a -> Bool) -> [a] -> Int
countSat'' f = length . filter f

{- 1: https://codeboard.io/projects/16442 -}

data Tree a = Leaf | Node a (Tree a) (Tree a) deriving (Show)

-- labelInOrder :: Tree a -> Tree Int

data NicoD a = NicoNothing | NicoList a (NicoD a) deriving (Show, Eq, Ord)


f = NicoList 33 NicoNothing
g = NicoList 44 NicoNothing
h = NicoList 55 (NicoList 66 (NicoNothing))

instance Functor NicoD where
  fmap f (NicoNothing) = NicoNothing
  fmap f (NicoList nl xs) = (NicoList (f nl) (fmap f xs))

-- λ> fmap (+3) h

instance Foldable NicoD where
  foldMap f NicoNothing = mempty
  foldMap f (NicoList nl xs) = f nl `mappend` foldMap f xs

-- λ> foldr (+) 0 h


-- Show only "good ints"
aGoodInt :: Int -> Maybe Int
aGoodInt n = if isgood n then Just n else Nothing where
  isgood n = elem 0 [ n `mod` x | x <- [23, 42] ]


-- use bind for retrieving goodBigInts
goodBigInt n = aGoodInt n >>= (\x -> if x > 1024 then Just n else Nothing)
