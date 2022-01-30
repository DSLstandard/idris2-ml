module Linear.V

import Data.Floating
import Data.Void
import Data.Nat
import public Data.Vect

public export
V : Nat -> Type -> Type
V = Vect

public export
T : List Nat -> Type -> Type
T [] a = a
T (n :: ns) a = V n (T ns a)

export
{n : _} -> FromDouble a => FromDouble (V n a) where
  fromDouble = pure . fromDouble

export
{n : _} -> Num a => Num (V n a) where
  (+) = zipWith (+)
  (*) = zipWith (*)
  fromInteger = pure . fromInteger

export
{n : _} -> Neg a => Neg (V n a) where
  (-) = zipWith (-)
  negate = map negate

export
{n : _} -> Fractional a => Fractional (V n a) where
  (/) = zipWith (/)
  recip = map recip

export
{n : _} -> Floating a => Floating (V n a) where
  pi = pure pi
  exp = map exp
  ln = map ln
  sqrt = map sqrt
  pow = zipWith pow
  log = zipWith log
  sin = map sin
  cos = map cos
  tan = map tan
  asin = map asin
  acos = map acos
  atan = map atan
  sinh = map sinh
  cosh = map cosh
  tanh = map tanh

export
dot : (Num a, Foldable f, Zippable f) => f a -> f a -> a
dot x y = sum $ zipWith (*) x y

punch : V i a -> V (S j) a -> V (S j) (V (i + j) a)
punch {j = Z} xs (y :: []) = [rewrite plusZeroRightNeutral i in xs]
punch {j = S j} xs (y :: (y' :: ys)) =
  (xs ++ (y' :: ys)) :: (rewrite sym $ plusSuccRightSucc i j in punch (xs `snoc` y) (y' :: ys))

flipflop : Neg a => Bool -> V n a -> V n a
flipflop _ [] = []
flipflop False (x :: xs) = x :: flipflop True xs
flipflop True (x :: xs) = negate x :: flipflop False xs

export
det : {n : _} -> Neg a => T [S n, S n] a -> a
det {n = Z} [[n]] = n
det {n = S n} xs = sum $ zipWith (*) (flipflop False (map head xs)) (map det $ punch [] (map tail xs))

export
eye : Num a => {n : _} -> V n (V n a)
eye {n = Z} = []
eye {n = S n} = (1 :: pure 0) :: map (0 ::) eye

infix 7 *^, ^*, *!, !*
export
(*^) : (Functor f, Num a) => a -> f a -> f a
(*^) a = map (a *)

export
(^*) : (Functor f, Num a) => f a -> a -> f a
(^*) = flip (*^)

export
(*!) : (Num a, Num (f a), Functor f, Foldable f, Foldable t, Zippable t) => t a -> t (f a) -> f a
f *! g = sum $ zipWith (*^) f g

export
(!*) : Num a => Foldable t => Functor f => Zippable t => f (t a) -> t a -> f a
m !* v = map (\r => sum $ zipWith (*) r v) m

infixl 7 !*!
export
(!*!) : Num a => Num (n a) => Functor m => Foldable t => Zippable t => Zippable n => Functor n => m (t a) -> t (n a) -> m (n a)
xs !*! ys = map (\x => foldl (+) 0 (zipWith (*^) x ys)) xs

export
outer : (Functor f, Functor g, Num a) => f a -> g a -> f (g a)
outer a b = map (\x => map (* x) b) a

public export
prod : List Nat -> Nat
prod [] = 1
prod (x :: xs) = x * prod xs

-- multRightSuccPlus : (left : Nat) -> (right : Nat) -> left * S right = left + (left * right)

export
group : (n : Nat) -> (m : Nat) -> V (n * m) a -> V n (V m a)
group Z     _ _  = []
group (S n) m xs = let (l, r) = splitAt m xs in l :: group n m r

export
ranged : (n : _) -> T [n] Nat
ranged Z = []
ranged (S i) = Z :: map S (ranged i)

export
bump : (size : List Nat) -> {n : _} -> {auto prf : n = prod size} -> V n a -> T size a
bump [] {n} xs with (prf)
  bump [] {n = 1} [x] | Refl = x
bump (m :: ms) {n} xs with (prf)
  bump (m :: ms) {n = m * prod ms} xs | Refl = map (bump ms) $ group m (prod ms) xs

export
dump : {ns : _} -> T ns a -> V (prod ns) a
dump {ns = []} x = [x]
dump {ns = n :: ns} x = concat $ map dump x

export
reshape : (size : _) -> {auto ns : _} -> {auto prf : prod ns = prod size} -> T ns a -> T size a
reshape size = bump size . dump
