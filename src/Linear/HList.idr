module Linear.HList

import public Data.List.Quantifiers

export
FromDouble (HList []) where
  fromDouble x = []

export
FromDouble a => FromDouble (HList as) => FromDouble (HList (a :: as)) where
  fromDouble x = fromDouble x :: fromDouble x

export
(prf : All FromDouble as) => FromDouble (HList as) where
  fromDouble {prf = []} x = []
  fromDouble {prf = prf :: prfs} x = fromDouble x :: fromDouble x

export
[I] Num (HList []) where
  [] + [] = []
  [] * [] = []
  fromInteger x = []

export
[J] Num a => Num (HList as) => Num (HList (a :: as)) where
  (x :: xs) + (y :: ys) = (x + y) :: (xs + ys)
  (x :: xs) * (y :: ys) = (x * y) :: (xs * ys)
  fromInteger x = fromInteger x :: fromInteger x

export
(prf : All Num as) => Num (HList as) where
  (+) [] [] = []
  (+) {prf = prf :: prfs} (x :: xs) (y :: ys) = (x + y) :: (xs + ys)
  (*) [] [] = []
  (*) {prf = prf :: prfs} (x :: xs) (y :: ys) = (x * y) :: (xs * ys)
  fromInteger {prf = []} x = []
  fromInteger {prf = prf :: prfs} x = fromInteger x :: fromInteger x

export
Neg (HList []) using I where
  (-) [] [] = []
  negate [] = []

export
Neg a => Neg (HList as) => Num (HList (a :: as)) => Neg (HList (a :: as)) where
  (-) (x :: xs) (y :: ys) = x - y :: xs - ys
  negate (x :: xs) = negate x :: negate xs

-- export
-- [A] (prf : All Neg as) => (prf2 : Num (HList as)) => Neg (HList as) where
--   (-) [] [] = []
--   (-) {as = a :: as} {prf = prf :: prfs} {prf2 = MkNeg _ _} (x :: xs) (y :: ys) = (x - y) :: (-) @{?f} xs ys
--   negate = ?asd

-- export
-- (prf1 : All Num as) => (prf2 : All Neg as) => Neg (HList as) where
--   (-) [] [] = []
--   (-) {prf1 = prf1 :: prf1s} {prf2 = prf2 :: prf2s} (x :: xs) (y :: ys) = (x - y) :: (xs - ys)
--   negate [] = []
--   negate {prf1 = prf1 :: prf1s} {prf2 = prf2 :: prf2s} (x :: xs) = negate x :: negate xs
