{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

{- imports automatically generated code for FPTP proof counting, -}
{- enables visualisation of proofs on screen and implements      -}
{- proof checking. See end of file for examples.                 -}

import STVCode

{- haskell lists to coq lists -}
h2cl [] = Nil
h2cl (a:as) = Cons a (h2cl as)

{- coq lists to haskell lists -}
c2hl :: List a -> [a]
c2hl Nil = []
c2hl (Cons x xs) = x:(c2hl xs)

{- coq naturals to haskell Ints -}
c2hn :: Nat -> Int
c2hn O = 0
c2hn (S n) = (c2hn n) + 1

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Nat
h2cn 0 = O
h2cn n = S (h2cn (n-1))

{- coq proofs to haskell proofs-}
data HPf cand =
   HAx [[cand]] (cand -> [[cand]]) (cand -> Int) [cand] [cand] 
 | HC1 [[cand]] (cand -> [[cand]]) (cand -> Int) [cand] [cand]  (HPf cand)
 | HEl [[cand]] (cand -> [[cand]]) (cand -> Int) [cand] [cand]  (HPf cand)
 | HTv [[cand]] (cand -> [[cand]]) (cand -> Int) [cand] [cand]  (HPf cand)
 | HEy [[cand]] (cand -> [[cand]]) (cand -> Int) [cand] [cand]  (HPf cand)
 | HTl [[cand]] (cand -> [[cand]]) (cand -> Int) [cand] [cand]  (HPf cand)
 | HHw [cand] (HPf cand)
 | HEw [cand] (HPf cand)

c2hpf :: Pf cand -> HPf cand
c2hpf p = case p of
 (Ax u a t h e)   -> HAx (c2hll u) (\c -> c2hll $ a c) (\c -> c2hn $ t c) (c2hl h) (c2hl e)
 (C1 u a t h e p) -> HC1 (c2hll u) (\c -> c2hll $ a c) (\c -> c2hn $ t c) (c2hl h) (c2hl e) (c2hpf p)
 (El u a t h e p) -> HEl (c2hll u) (\c -> c2hll $ a c) (\c -> c2hn $ t c) (c2hl h) (c2hl e) (c2hpf p)
 (Tv u a t h e p) -> HTv (c2hll u) (\c -> c2hll $ a c) (\c -> c2hn $ t c) (c2hl h) (c2hl e) (c2hpf p)
 (Ey u a t h e p) -> HEy (c2hll u) (\c -> c2hll $ a c) (\c -> c2hn $ t c) (c2hl h) (c2hl e) (c2hpf p)
 (Tl u a t h e p) -> HTl (c2hll u) (\c -> c2hll $ a c) (\c -> c2hn $ t c) (c2hl h) (c2hl e) (c2hpf p)
 (Hw w p) -> HHw (c2hl w) (c2hpf p)
 (Ew w p) -> HEw (c2hl w) (c2hpf p)
 where c2hll = (map c2hl) . c2hl

{- equality for data structures -}
deriving instance Eq Nat
deriving instance Eq Cand
deriving instance (Eq a) => (Eq (List a))
instance (Eq a) => Eq (Cand -> a) where
  (==)  f g = all (\c -> f c == g c) (c2hl cand_all)
  
{- visualisation -}
deriving instance Show Cand

instance (Show a, Show b) => Show (SigT a b) where
 show (ExistT x p) = (show x) ++ "\n" ++ (show p)

instance (Show a) => Show (Cand -> a) where
  show f = show_l (c2hl cand_all) where
    show_l [] = ""
    show_l [c] = (show c) ++ "[" ++ (show (f c)) ++ "]"
    show_l (c:cs) = (show c) ++ "[" ++ (show (f c)) ++ "] " ++ (show_l cs)

instance (Show a) => Show (List a) where
  show l = show (c2hl l)

instance Show Nat where
  show  n = show (c2hn n) 

overline :: String -> String -> String
overline r s = 
  let line = '-':line
  in "\n(" ++ r ++ ")" ++ (take (Prelude.length s - 5) line) ++ "\n" ++ s

show_p :: (Show a) => List a -> String
show_p Nil = "*"
show_p (Cons a as) = "[" ++ (show a) ++ ", ...]"

show_st r u a t h e = overline r
  ("    (" ++ (show_p u) ++ ", " ++ {- (show a) ++  ", "  ++ -} (show t) ++ ", " ++
  (show h) ++ ", " ++ (show e) ++ ")" )

show_w r w = overline r ("    winners (" ++ (show w) ++ ")\n")
instance Show (Pf Cand) where
  show (Ax u a t h e)  = show_st "ax" u a t h e
  show (C1 u a t h e p) = (show p) ++ (show_st "c1" u a t h e)
  show (El u a t h e p) = (show p) ++ (show_st "el" u a t h e)
  show (Tv u a t h e p) = (show p) ++ (show_st "tv" u a t h e)
  show (Ey u a t h e p) = (show p) ++ (show_st "ey" u a t h e)
  show (Tl u a t h e p) = (show p) ++ (show_st "tl" u a t h e)
  show (Hw w p) = (show p) ++ (show_w "hw" w)
  show (Ew w p) = (show p) ++ (show_w "ew" w)


{- auxiliary functions for proof checking -}
{- last judgement in a putative proof -}
data Lst = Lft [[Cand]] (Cand -> [[Cand]]) (Cand -> Int) [Cand] [Cand] | Rgt [Cand] deriving (Show)

{- all ways to write l = lft++[m]++rgt -}
splits :: [a] -> [([a], a, [a])]
splits [] = []
splits (x:xs) = [([], x, xs)] ++ map (\(h, m, t) -> (x:h, m, t)) (splits xs)

{- in replacing x with y in l yields nl -}
{- i.e. l splits as (h, m, t) with nl = l++[y]++r  -}
repl :: (Eq a) => a -> a -> [a] -> [a] -> Bool
repl x y l nl = any (\(h,m,t) -> x == m && nl == h++[y]++t) (splits l)

{- x has been removed from l yielding nl -}
{- i.e. l splits as (h, m, t) with nl = h++t -}
rmd :: (Eq a) => a -> [a] -> [a] -> Bool
rmd x l nl = any (\(h, m, t) -> x == m && nl == h++t) (splits l)

{- adding x to l gives nl -}
{- i.e. nl splits as (h, x t) with l == h ++ t -}
add :: (Eq a) => a -> [a] -> [a] -> Bool
add x l nl = any (\(h, m, t) -> x == m && l == h++t) (splits nl)

{- exists andall others: there's x in l with p x and all y != x have q x -} 
ex_aa :: (Eq a) => [a] -> (a -> Bool) -> (a -> Bool) -> Bool
ex_aa  l p q = any (\x -> p x && all (\y -> y == x || q y) l) l

{- exists x in l with p x -}
ex :: [a] -> (a -> Bool) -> Bool
ex l p = any p l

{- all y in l with y != x have p y -}
all_except :: (Eq a) => a -> [a] -> (a -> Bool) -> Bool
all_except x l p = all (\y -> x == y || p y) l

len = Prelude.length

-- returns the last judgement of a proof if the proof checks, Nothing if it doesn't
checkh :: Int -> Int -> [Cand] -> HPf Cand -> Maybe Lst
checkh q s hop p = case p of
  HAx u a t h e | h == hop && e == [] && a == (\c -> []) && t == (\c -> 0) -> Just (Lft u a t h e)
                | otherwise ->  Nothing
  HC1 u a t h e p ->  (checkh q s hop p) >>= checkc where
    checkc (Lft u0 a0 t0 h0 e0) | e == e0 && h == h0 && ex u0 (\v -> ctd v) =
      Just (Lft u a t h e)  where
        ctd (f:fs) = rmd (f:fs) u0 u && add (f:fs) (a0 f) (a f) && all_except f  h (\c -> t c == t0 c && a c == a0 c)
        ctd _ = False
    checkc _ = Nothing
  HEl u a t h e p -> checkh q s hop p >>= checke where
    checke (Lft u0 a0 t0 h0 e0) | u == u0 && a == a0 && t == t0 && len  e0 < s && ex h0 (\c -> el c) = 
      Just (Lft u a t h e) where
        el c = rmd c h0 h && add c e0 e
    checke _ = Nothing
  HTv u a t h e p -> checkh q s hop p >>= checkt where
    checkt (Lft u0 a0 t0 h0 e0) | a == a0 && t == t0 && h == h0 && e == e0 && ex u0 (\v -> tvd v)  = 
      Just (Lft u a t h e) where
        tvd (f:fs) = not (f `elem` h0) && repl (f:fs) fs u0 u
        tvd _ = False
    checkt _ = Nothing
  HEy u a t h e p -> checkh q s hop p >>= checky where
    checky (Lft u0 a0 t0 h0 e0) | a == a0 && t == t0 && h == h0 && e == e0 && ex u0 (\v -> de v) = 
      Just (Lft u a t h e) where
        de ([]) = rmd [] u0 u
        de _ = False
    checky _ = Nothing
  HTl u a t h e p -> checkh q s hop p >>= checkl where
    checkl (Lft [] a0 t0 h0 e0) | t == t0 && e == e0 && (len e0 + len h0 > s) && ex h0 (\c -> emd c) = 
      Just (Lft u a t h e) where
        emd c = rmd c h0 h && u == a0 c && all (\d -> t0 c <= t c) h0
    checkl _ = Nothing
  HHw  w p -> checkh q s hop p >>= checkw where
    checkw (Lft u0 a0 t0 h0 e0) | len h0 + len e0 <= s && w == e0++h0 = Just (Rgt w)
    checkw _ = Nothing
  HEw w p -> checkh q s hop p  >>= checkw where
    checkw (Lft u0 a0 t0 h0 e0) | len e0 == s && w == e0 =  Just (Rgt w)
    checkw _ = Nothing
checkP q s h (ExistT w p) = case checkh q s h (c2hpf p) of Just (Rgt w') -> (c2hl w) == w'; _ -> False
checkR q s h (ExistT w p) = case checkh q s h (c2hpf p) of 
  Just (Rgt w') -> if (c2hl w) == w' then "accepted: " ++ (show w) else "not accepted."
  _ -> "not accepted."

{- examples -}
{- counting using extracted code after conversion -}
count quota seats hopefuls  ballots = 
  cand_ex_winners_pf (h2cl (map h2cl ballots)) (h2cn
  quota) (h2cn seats) 

{- more concretely: we fix hopefuls, quota and seats -}
h = [Alice, Bob, Charlie, Deliah]
q = 2
s = 2

{- elect two candidates successively -}
ex_1 = count q s h [[Alice, Bob], [Alice, Charlie], [Deliah, Charlie,
  Bob], [Deliah, Alice, Bob], [Bob, Alice], [Bob], [Bob], [Bob],
  [Alice, Deliah, Charlie], [Charlie], [Deliah, Charlie]] 

{- check the correctness of this proof -}
check_1 = checkP  q s h $ ex_1

{- one vote is transferred -}
ex_2 = count q s h [[Alice, Bob], [Alice, Charlie], [Deliah, Charlie,
  Bob] , [Bob, Alice], 
  [Alice, Deliah, Charlie], [Charlie], [Deliah, Charlie]] 

{- check the correctness -}
check_2 = checkP q s h $ ex_2

{- one  cand is eliminated, one vote is transferred, and elected cands win -}
ex_3 = count q s h [[Alice, Bob], [Alice, Charlie], [Deliah, Charlie], [Bob, Alice], [Charlie]] 

{- check correctness -}
check_3 = checkP q s h $ ex_3

{- roll your own: read a list of votes from stdin and count using droop quota -}
deriving instance Read Cand
main :: IO ()
main  = readLn  >>= print . cnt_n_check . read
       where
         cnt_n_check :: [[Cand]] -> String
         cnt_n_check s = let q = (div (Prelude.length s) 3) + 1 in
           checkR q 2 h  $ count q 2 h s
