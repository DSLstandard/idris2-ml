module Backprop.Op

import public Data.List.Quantifiers

public export
record Op (is : List Type) (o : Type) where
  constructor MkOp
  do_op : HList is -> Pair o (o -> HList is)

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

export
op_abs : Abs a => Op [a] a
op_abs = MkOp $ \[x] => (abs x, ?op_abs_back)

-- Fractional interface

export
op_div : (Neg a, Fractional a) => Op [a, a] a
op_div = MkOp $ \[x, y] => (x / y, \d => [d / y, -d * x / (y * y)])

export
op_recip : (Neg a, Fractional a) => Op [a] a
op_recip = MkOp $ \[x] => (recip x, \d => [-d / (x * x)])

-- Double exponential

export
op_pow : Op [Double, Double] Double
op_pow = MkOp $ \[x, y] =>
  ( pow x y
  , \d => let k = d * pow x (y - 1) in [k * y, k * x * log x]
  )

export
op_sqrt : Op [Double] Double
op_sqrt = MkOp $ \[x] => (sqrt x, \d => [d / (2 * sqrt x)])

export
op_exp : Op [Double] Double
op_exp = MkOp $ \[i] => (exp i, \d => [d * exp i])

-- Double logarithm

export
op_log : Op [Double] Double
op_log = MkOp $ \[x] => (log x, \d => [d / x])

-- Double trigo

export
op_sin : Op [Double] Double
op_sin = MkOp $ \[x] => (sin x, \d => [d * cos x])

export
op_cos : Op [Double] Double
op_cos = MkOp $ \[x] => (cos x, \d => [d * -sin x])

export
op_tan : Op [Double] Double
op_tan = MkOp $ \[x] => let cos' = cos x in (tan x, \d => [d / cos'])

export
op_atan : Op [Double] Double
op_atan = MkOp $ \[x] => (atan x, \d => [d / (1 - x * x)])
