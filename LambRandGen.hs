module LambRandGen

where

data Term = Index Integer 
		  | Abs Term 
		  | App Term Term
		  deriving Show

-----------------------------------
-- arbitrary term unranking
-----------------------------------
ttab :: [[[Integer]]] 
ttab = iterate nextn . map return $ [0..] 
	where
	nextn ls = zipWith rake (tail ls) ls
	rake (m1:_) ms = (m1 + conv ms) : ms 
	conv ms = sum $ zipWith (*) ms (reverse ms)

t :: Int -> Int -> Integer 
t n m = head $ ttab !! n !! m

unrankT :: Int -> Int -> Integer -> Term
unrankT 0 m k = Index k 
unrankT n m k 
	| k <= (t (n-1) (m+1)) = Abs (unrankT (n-1) (m+1) k) 
	| (t (n-1) (m+1)) < k = appTerm (n-1) 0 (k - t (n-1) (m+1)) 
	where appTerm n j h 
		| h <= tjmtnjm = let (dv,md) = ((h-1) `divMod` tnjm) 
					     in App (unrankT j m (dv+1)) 
					     		(unrankT (n-j) m (md+1))
		| otherwise = appTerm n (j + 1) (h -tjmtnjm) 
		where tnjm = t (n-j) m
		      tjmtnjm = (t j m) * tnjm

-----------------------------------
--normal form term unranking
-----------------------------------
ftab :: [[Integer]] 
ftab = [0..]:[[ftab !! (n-1) !! (m+1) + gtab !! n !! m
			  | m<-[0..]] 
			  | n<-[1..]]

gtab :: [[Integer]] 
gtab = [0..] : [[s n m | m <- [0..]] | n <- [1..]] 
    where s n m = let
                   fi = [ftab !! i !! m | i <- [0..(n-1)]]
                   gi = [gtab !! i !! m | i <- [0..(n-1)]]
                  in sum $ zipWith (*) fi (reverse gi)

f' :: Int -> Int -> Integer
f' n m = ftab !! n !! m

unrankNF :: Int -> Int -> Integer -> Term 
unrankNF 0 m k = Index k
unrankNF n m k 
  | k <= ftab !! (n-1) !! (m+1) = Abs (unrankNF (n-1) (m+1) k) 
  | ftab !! (n-1) !! (m+1) < k = unrankNG n m (k - ftab !! (n-1) !! (m+1))

unrankNG :: Int -> Int -> Integer -> Term 
unrankNG 0 m k = Index k 
unrankNG n m k = appNF (n-1) 0 m k

appNF :: Int -> Int -> Int -> Integer -> Term 
appNF n j m h 
    | h <= gjmfnjm = let (dv,md) = (h-1) `divMod` fnjm 
                     in App (unrankNG j m (dv+1)) 
                            (unrankNF (n-j) m (md +1))
    | otherwise = appNF n (j + 1) m (h -gjmfnjm) 
    where fnjm = ftab !! (n-j) !! m
          gjmfnjm = gtab !! j !! m * fnjm