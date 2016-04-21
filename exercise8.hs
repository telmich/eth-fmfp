encode [] = []
encode (x:ys) = encode' ys 1 x []

encode' [] n z cs = cs ++ [n,z]
encode' (x:ys) n z cs
  | x == z = encode' ys (n+1) z cs
  | otherwise = encode' ys 1 x (cs ++ [n,z])

decode [] = []
decode [x] = []
decode (x:y:zs) = (replicate x y) ++ decode zs

replicate 0 y = []
replicate x y = y:(replicate (x-1) y)

srclen [] = 0
srclen [x] = 0
srclen (x:y:zs) = x + (srclen zs)

{- to prove:




Lemma's required:

  (x:ys) ++ zs = x:(ys++zs)
  length zs `mod` 2 = 0 => length (zs ++ [x,y])

To prove:
  forall xs, n, z, cs:

    srclen(encode'(decode xs) n z cs) = (srclen xs) + n + (srclen cs)


--------! Induction on what gets decomposed in the recursion

Use strong structural induction

Generalize -- when??



-}

{- new prove

P(xs) = length (decode xs) = srclen xs

Prove forall xs. P(xs). by strong structural induction on xs

To prove: P(ks), assuming forall ms [ ks. P(ms) as I.H.


Cases on ks
(ks = [])
  length (decode []) = length [] = 0 = srclen ks
(ks = [k])
  analogous
(ks = x:y:zs for some x, y, zs)
  length (decode x:y:zs) = length ( (replicate x y) ++ decode zs)
  = length (replicate x y) + length (decode zs)
  = x + length (decode zs)


Lemmas:

1) length xs ++ ys = length xs + length ys
2) forall x,y >=0 : length (replicate x y) = x

-}

{-

 Induction on the tree

Let Gamma, A, B, X be arbitrary
We assume root(T) = (Gamma |- A) and need to prove EXISTS T'. root(T') =
  (Gamma[X->B] |- A [X -> B])

Cases on last rule applied in T.
(Ax). Then Gamma = (Gamma',  A) for some Gamma'
Gamma[X->B] = (Gamma'[X->B], A[X->B])
so we can construct


-------------------------------- (Ax)
Gamma'[X->B], A[X->B] |- A[X->B]



(Case and EL)
  Then T is of the form:

        T'
    ------------------
    Gamma |- A and A'
    ----------------- (and EL) for some A', T'
    Gamma |- A

(T' [ T, root(T') = (Gamma |- (A and A'))

By I.H. on T' =



Construct new tree:

         T''
     ----------
    Gamma[X->B]



-}


{- not total function -}
{- = und dreigleich -}


{- (1) at home -}

{-

∀ n, z :: Nat, ∀ xs, cs :: [Nat] · (length cs % 2 = 0 ⇒
srclen (encode’ (decode xs) n z cs) = (srclen xs) + n + (srclen cs))

Proof by induction over list xs

  Base Case: []

  srclen (encode’ (decode []) n z cs) = (srclen []) + n + (srclen cs))

  srclen (encode’ (decode []) n z cs) =
    (D1)  srclen (encode’ [] n z cs) =
    (E'1) srclen (cs++[n,z])
    (L3)  srclen cs + n


  (srclen []) + n + (srclen cs)) =
    (S1) 0 + n + (srclen cs)
    (arith?) n + srclen cs
    (arith?) srclen cs + n

  QED

  Step case:
    Step case: Show that P(xs) implies P(x:y:xs).
    IH: srclen (encode’ (decode xs) n z cs) = (srclen xs) + n + (srclen cs))

    To prove:
    srclen (encode’ (decode x:y:xs) n z cs) = (srclen x:y:xs) + n + (srclen cs))

    srclen (encode’ (decode x:y:xs) n z cs) =
    (D3) srclen (encode’ ((replicate x y) ++ (decode xs)) n z cs) =
    (L1) srclen (encode’ (decode xs) (x+n) z cs)
    (IH) (srclen xs) + (x+n) + (srclen cs)
    (arith?) x + srclen xs + n + srclen cs


    srclen (x:y:xs) + n + (srclen cs) =
    (S3) x + srclen xs + n + srclen cs

  QED
QED
-}
