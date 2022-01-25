module Linear

import Data.Nat
import Data.Vect

public export
V : Nat -> Type -> Type
V = Vect

public export
V' : List Nat -> Type -> Type
V' [] a = a
V' (n :: ns) a = V n (V' ns a)

export
{n : _} -> Num a => Num (V n a) where
  xs + ys = zipWith (+) xs ys
  xs * ys = zipWith (*) xs ys
  fromInteger = pure . fromInteger

infixl 6 ^+^
infixl 6 ^-^

public export
interface Functor f => Additive f where
  zero : Num a => f a
  (^+^) : Num a => f a -> f a -> f a
  (^-^) : Neg a => f a -> f a -> f a
  lift : (a -> b -> c) -> f a -> f b -> f c

export
{n : _} -> Additive (V n) where
  zero = 0
  (^+^) = (+)
  (^-^) xs ys = zipWith (-) xs ys
  lift f xs ys = f <$> xs <*> ys

public export
interface Additive f => Metric f where
  dot : Num a => f a -> f a -> a

export
{n : _} -> Metric (V n) where
  dot xs ys = sum (xs * ys)

derives : Vect i a -> Vect (S j) a -> Vect (S j) (Vect (i + j) a)
derives {j = Z} xs (y :: []) = [rewrite plusZeroRightNeutral i in xs]
derives {j = S j} xs (y :: (y' :: ys)) =
  (xs ++ (y' :: ys)) :: (rewrite sym $ plusSuccRightSucc i j in derives (xs `snoc` y) (y' :: ys))

flipflop : Neg a => Bool -> Vect n a -> Vect n a
flipflop _ [] = []
flipflop False (x :: xs) = x :: flipflop True xs
flipflop True (x :: xs) = negate x :: flipflop False xs

export
det : {n : _} -> Neg a => V' [S n, S n] a -> a
det {n = Z} [[n]] = n
det {n = S n} xs = sum $ zipWith (*) (flipflop False (map head xs)) (map det $ derives [] (map tail xs))

export
identity : Num a => {n : _} -> V n (V n a)
identity {n = Z} = []
identity {n = S n} = (1 :: pure 0) :: map (0 ::) identity

export
(*^) : (Functor f, Num a) => a -> f a -> f a
(*^) a = map (a *)

infixl 7 !*!
export
(!*!) : (Functor m, Foldable t, Additive t, Additive n, Num a) => m (t a) -> t (n a) -> m (n a)
xs !*! ys = map (\x => foldl (^+^) zero (lift (*^) x ys)) xs
