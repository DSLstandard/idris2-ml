module Backprop.Math

import Backprop.CanBack
import Backprop.Core
import Control.Optics

export
view : {a, b : _} -> CanBack a => Simple Lens a b -> Node i a -> Node i b
view l = op1 $ \[x] => (x ^. l, \d => [set l d zero])

infixl 0 ^.
export
(^.) : {a, b : _} -> CanBack a => Node i a -> Simple Lens a b -> Node i b
x ^. l = view l x

export
max, min : {a : _} -> (CanBack a, Num a, Ord a) => Node i a -> Node i a -> Node i a
max = op2 $ \[x, y] => (max x y, \d => [d * if x > y then 1 else 0, d * if y > x then 1 else 0])
min = op2 $ \[x, y] => (min x y, \d => [d * if x < y then 1 else 0, d * if y < x then 1 else 0])

export
sqrt : Node i Double -> Node i Double
sqrt = op1 $ \[x] => (sqrt x, \d => [d / (2 * sqrt x)])

export
pow : Node i Double -> Node i Double -> Node i Double
pow = op2 $ \[x, y] =>
  ( pow x y
  , \d => let k = d * pow x (y - 1) in [k * y, k * x * log x]
  )

export
exp : Node i Double -> Node i Double
exp = op1 $ \[x] => (exp x, \d => [d * exp x])

export
ln : Node i Double -> Node i Double
ln = op1 $ \[x] => (log x, \d => [d / x])

export
log : (base : Node i Double) -> Node i Double -> Node i Double
log base x = ln x / ln base

export
sin, cos, tan, asin, acos, atan, sinh, cosh, tanh : Node i Double -> Node i Double
sin = op1 $ \[x] => (sin x, \d => [d * cos x])
cos = op1 $ \[x] => (cos x, \d => [d * -sin x])
tan = op1 $ \[x] => (tan x, \d => let cos' = cos x in [d / (cos' * cos')])
asin = op1 $ \[x] => (asin x, \d => [d / sqrt (1 - x * x)])
acos = op1 $ \[x] => (acos x, \d => [-d / sqrt (1 - x * x)])
atan = op1 $ \[x] => (atan x, \d => [d / (1 - x * x)])
sinh = op1 $ \[x] => (sinh x, \d => [d * cosh x])
cosh = op1 $ \[x] => (cosh x, \d => [d * sinh x])
tanh = op1 $ \[x] => (tanh x, \d => let cosh' = cosh x in [d / (cosh' * cosh')])

-- machine learning specific

export
sigmoid : Node i Double -> Node i Double
sigmoid x = 1 / (1 + exp (-x))

export
relu : Node i Double -> Node i Double
relu x = max 0 x

||| intergral power
export
power : {a : _} -> (CanBack a, Num a) => Node i a -> Nat -> Node i a
power x Z = 1
power x (S i) = x * power x i
