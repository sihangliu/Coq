{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

{- imports automatically generated code for FPTP proof counting, -}
{- enables visualisation of proofs on screen and implements      -}
{- proof checking. See end of file for examples.                 -}

import Data.List
import FPTPCode

{- conversion between coq and haskell data structures -}
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

{- coq to haskell proofs -}
data HPf cand =
    HAx [cand] (cand -> Int)
  | HC1 [cand] (cand -> Int) (HPf cand)
  | HDw cand (HPf cand)

instance Show (Cand -> Int) where 
  show f = "[tally]"
deriving instance Show (HPf Cand)

c2hpf :: Pf cand -> HPf cand
c2hpf (Ax u t)   = HAx (c2hl u) (\c -> c2hn $ t c)
c2hpf (C1 u t p) = HC1 (c2hl u) (\c -> c2hn $ t c) (c2hpf p)
c2hpf (Dw w p)   = HDw w (c2hpf p)

{- equality for coq data structures -}
deriving instance Eq Cand
deriving instance Eq Nat
deriving instance (Eq a) => Eq (List a)

{- visualisation of data structures -}
deriving instance Show Cand
instance (Show a, Show b) => Show (SigT a b) where
 show (ExistT x p) = (show x) ++ "\n" ++ (show p)

instance Show (Cand -> Nat) where
  show f = show_l (c2hl cand_all) where
    show_l [] = ""
    show_l [c] = (show c) ++ "[" ++ (show (f c)) ++ "]"
    show_l (c:cs) = (show c) ++ "[" ++ (show (f c)) ++ "] " ++ (show_l cs)

instance (Show a) => Show (List a) where
  show l = show (c2hl l)

instance Show Nat where
  show  n = show (c2hn n) 

line :: [Char]
line = ('-'):line
show_st r u t = 
  let s = "    st(" ++ (show u) ++ ", " ++ (show t) ++ ")\n" 
  in "(" ++ r ++ ")" ++ (take (length s - 5) line) ++ "\n" ++ s
show_w  r w   = 
  let s = "    winner(" ++ (show w) ++ ")\n"
  in "(" ++ r ++ ")" ++ (take (length s - 5) line)  ++ "\n" ++ s

instance Show (Pf Cand) where
  show (Ax u t) = show_st "ax" u t
  show (C1 u t p) = (show p) ++ (show_st "c1" u t)
  show (Dw w p)   = (show p) ++ (show_w "dw" w)

{- proof checking -}
{- to avoid name clashes with haskell's Either -}
data P a b = Lft a | Rgt b deriving (Eq, Show)

{- proof checking gives the last judgement for valid proofs, nothing otherwise -}
{- h is the list of (hopeful) candidates.                                      -}
check :: [Cand] -> HPf Cand -> Maybe (P ([Cand], Cand -> Int) Cand)
check h (HAx v t) = if (all ((== 0)  . t) h) then Just (Lft (v, t)) else Nothing
check h (HC1 v t p) = check h p >>= checkc where 
  checkc (Lft (v0, t0)) | any (\s -> okc s t0) (splits v0) = Just (Lft (v, t))
  checkc _ = Nothing
  okc (hd, md, tl) t0 = v == hd++tl && t md == 1 + t0 md && all (\c -> c == md || t c == t0 c) h 
  splits [] = []; splits (x:xs) = ([], x, xs):(map (\(h, m, t) -> (x:h, m, t)) $ splits xs)
check h (HDw w p) = check h p >>= checkw where
  checkw (Lft (v0, t0)) | (v0 == []) && all (\d -> t0 d <= t0 w) h = Just (Rgt w)
  checkw _ = Nothing

{- checking (winner, proof)-pairs converts to haskell and checks proof and winner. -}
checkP h (ExistT w p) = case check h (c2hpf p) of Just (Rgt w') -> w == w'; _ -> False
checkR h (ExistT w p) = case check h (c2hpf p) of 
  Just (Rgt w') | w == w' -> "accepted: " ++ (show w)
  _ -> "not accepted."

{- cheating: maliciously count c's votes for d -}
cheat :: Cand -> Cand -> Pf Cand -> Pf Cand
cheat c d p  = let last_t p = case p of Ax u t -> t; C1 u t p -> t in case p of
  Ax u t ->  Ax u t
  C1 u t0 p0 -> if (c0 == c) then C1 u (inc d) p' else C1 u (inc c0) p'
    where 
      p' = cheat c d p0 -- modified shorter proof
      t' = last_t p'    -- final tally of this proof
      c0 = ctd (c2hl cand_all) -- cand being counted
      ctd [c] = c
      ctd (c:cs) = if (t0 c) == ((last_t p0)  c) then ctd cs else c
      inc c d = if (c==d) then S (t' c) else t' d
  Dw t p0 -> Dw (find_max (c2hl cand_all) (\c -> c2hn ((last_t p') c))) p'
    where 
      p' = cheat c d p0
      find_max [c] f = c
      find_max (c:cs) f = let cm = find_max cs f in
        if (f c >= f cm) then c else cm
cheatP :: Cand -> Cand -> SigT Cand (Pf Cand) -> SigT Cand (Pf Cand)
cheatP c d (ExistT w p) = ExistT w' p' where
  p' = cheat c d p
  w' = case p' of Dw w0 _ -> w0


{- examples -}
{- vote counting using extracted code after conversion -} 
count :: [Cand] -> SigT Cand (Pf Cand)
count = cand_exists_winner_pf . h2cl

{- more concretely: we fix the hopefuls -}
h = [Alice, Bob, Claire, Darren] 
{- more concretely: count the following -}
ex_1 = count [Alice, Claire, Bob, Bob, Alice, Claire, Claire]

{- check the proof we have just obtained -}
check_1 = checkP h ex_1

{- maliciously count Claire's votes for Bob -}
cheat_1 = cheatP Claire Bob ex_1

{- and check that it doesn't type check -}
check_cheat_1 = checkP h cheat_1

{- roll your own: read list of votes from stdin and count -}
deriving instance Read Cand
main :: IO ()
main  = readLn  >>= print . cnt_n_check . read where
  cnt_n_check :: [Cand] -> String
  cnt_n_check s = checkR h $ count s
