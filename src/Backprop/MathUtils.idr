module Backprop.MathUtils

||| when x < 0, return -1
||| when x > 0, return +1
||| otherwise, return 0
export
signum_zero : (Neg a, Ord a) => a -> a
signum_zero x = if x > 0 then 1 else if x < 0 then -1 else 0
