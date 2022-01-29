module Backprop.Math

import Backprop.CanBack
import Backprop.Core
import Backprop.Op
import Control.Optics

export
view : {a, b : _} -> CanBack a => Simple Lens a b -> Node i a -> Node i b
view l x = op (op_view l) [x]

infixl 0 ^.
export
(^.) : {a, b : _} -> CanBack a => Node i a -> Simple Lens a b -> Node i b
x ^. l = view l x

export
max, min : {a : _} -> (CanBack a, Num a, Ord a) => Node i a -> Node i a -> Node i a
max a b = op op_max [a, b]
min a b = op op_min [a, b]

export
sqrt : Node i Double -> Node i Double
sqrt x = op op_sqrt [x]

export
pow : Node i Double -> Node i Double -> Node i Double
pow x y = op op_pow [x, y]

export
exp : Node i Double -> Node i Double
exp x = op op_exp [x]

export
ln : Node i Double -> Node i Double
ln x = op op_ln [x]

export
log : (base : Node i Double) -> Node i Double -> Node i Double
log base x = ln x / ln base

export
sin, cos, tan, asin, acos, atan, sinh, cosh, tanh : Node i Double -> Node i Double
sin x = op op_sin [x]
cos x = op op_cos [x]
tan x = op op_tan [x]
asin x = op op_asin [x]
acos x = op op_acos [x]
atan x = op op_atan [x]
sinh x = op op_sinh [x]
cosh x = op op_cosh [x]
tanh x = op op_tanh [x]

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
