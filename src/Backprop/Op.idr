module Backprop.Op

import Backprop.CanBack
import Control.Optics
import Debug.Trace
import public Data.List.Quantifiers

public export
record Op (is : List Type) (o : Type) where
  constructor MkOp
  do_op : HList is -> Pair o (o -> HList is)

export
op_const : a -> Op [] a
op_const x = MkOp $ \[] => (x, const [])

export
op_view : {b : _} -> CanBack a => Simple Lens a b -> Op [a] b
op_view l = MkOp $ \[x] => (x ^. l, \d => [set l d zero])

-- Num operation

export
op_add : Num a => Op [a, a] a
op_add = MkOp $ \[x, y] => (x + y, \d => [d, d])

export
op_sub : Neg a => Op [a, a] a
op_sub = MkOp $ \[x, y] => (x - y, \d => [d, -d])

export
op_mul : Num a => Op [a, a] a
op_mul = MkOp $ \[x, y] => (x * y, \d => [d * y, x * d])

-- Neg interface

export
op_negate : Neg a => Op [a] a
op_negate = MkOp $ \[x] => (-x, \g => [-g])

-- Abs interface

||| when x < 0, return -1
||| when x > 0, return +1
||| otherwise, return 0
export
signum_zero : (Neg a, Ord a) => a -> a
signum_zero x = if x > 0 then 1 else if x < 0 then -1 else 0

export
op_abs : (Neg a, Ord a, Abs a) => Op [a] a
op_abs = MkOp $ \[x] => (abs x, \d => [d * signum_zero x])

-- Fractional interface

export
op_div : (Neg a, Fractional a) => Op [a, a] a
op_div = MkOp $ \[x, y] => (x / y, \d => [d / y, -d * x / (y * y)])

export
op_recip : (Neg a, Fractional a) => Op [a] a
op_recip = MkOp $ \[x] => (recip x, \d => [-d / (x * x)])

-- Ord interface

export
op_max, op_min : (Num a, Ord a) => Op [a, a] a
op_max = MkOp $ \[x, y] => (max x y, \d => [d * if x > y then 1 else 0, d * if y > x then 1 else 0])
op_min = MkOp $ \[x, y] => (min x y, \d => [d * if x < y then 1 else 0, d * if y < x then 1 else 0])

-- Double related

||| fix for `pow` when `pow (-1) 2` returns `+nan.0`
export
pow' : Double -> Double -> Double
pow' x y = exp (y * log x)

export
op_pow : Op [Double, Double] Double
op_pow = MkOp $ \[x, y] =>
  ( pow x y
  , \d => let k = d * pow' x (y - 1) in [k * y, k * x * log x]
  )

export
op_sqrt : Op [Double] Double
op_sqrt = MkOp $ \[x] => (sqrt x, \d => [d / (2 * sqrt x)])

export
op_exp : Op [Double] Double
op_exp = MkOp $ \[i] => (exp i, \d => [d * exp i])

export
op_ln : Op [Double] Double
op_ln = MkOp $ \[x] => (log x, \d => [d / x])

export
op_sin, op_cos, op_tan, op_asin, op_acos, op_atan, op_sinh, op_cosh, op_tanh : Op [Double] Double
op_sin = MkOp $ \[x] => (sin x, \d => [d * cos x])
op_cos = MkOp $ \[x] => (cos x, \d => [d * -sin x])
op_tan = MkOp $ \[x] => (tan x, \d => let cos' = cos x in [d / (cos' * cos')])
op_asin = MkOp $ \[x] => (asin x, \d => [d / sqrt (1 - x * x)])
op_acos = MkOp $ \[x] => (acos x, \d => [-d / sqrt (1 - x * x)])
op_atan = MkOp $ \[x] => (atan x, \d => [d / (1 - x * x)])
op_sinh = MkOp $ \[x] => (sinh x, \d => [d * cosh x])
op_cosh = MkOp $ \[x] => (cosh x, \d => [d * sinh x])
op_tanh = MkOp $ \[x] => (tanh x, \d => let cosh' = cosh x in [d / (cosh' * cosh')])
