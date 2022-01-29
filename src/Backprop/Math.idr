module Backprop.Math

import Backprop.Core
import Backprop.Op

export
max, min : (Num a, Ord a) => BVar s a -> BVar s a -> BVar s a
max a b = op op_max [a, b]
min a b = op op_min [a, b]

export
sqrt : BVar s Double -> BVar s Double
sqrt x = op op_sqrt [x]

export
pow : BVar s Double -> BVar s Double -> BVar s Double
pow x y = op op_pow [x, y]

export
exp : BVar s Double -> BVar s Double
exp x = op op_exp [x]

export
ln : BVar s Double -> BVar s Double
ln x = op op_ln [x]

export
log : (base : BVar s Double) -> BVar s Double -> BVar s Double
log base x = ln x / ln base

export
sin, cos, tan, asin, acos, atan, sinh, cosh, tanh : BVar s Double -> BVar s Double
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
sigmoid : BVar s Double -> BVar s Double
sigmoid x = 1 / (1 + exp (-x))

export
relu : BVar s Double -> BVar s Double
relu x = max 0 x

||| intergral power
export
power : Num a => BVar s a -> Nat -> BVar s a
power x Z = 1
power x (S i) = x * power x i
