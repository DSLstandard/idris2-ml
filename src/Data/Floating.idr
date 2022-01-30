module Data.Floating

||| Haskell's `Floating` with all inverse hyperbolic trigo functions absent
public export
interface Fractional a => Floating a where
  pi : a
  exp, ln, sqrt : a -> a
  pow : a -> a -> a
  log : (base : a) -> a -> a
  sin, cos, tan, asin, acos, atan, sinh, cosh, tanh : a -> a

export
Floating Double where
  pi = Prelude.pi
  exp = Prelude.exp
  ln = Prelude.log
  log base x = ln x / ln base
  sqrt = Prelude.sqrt
  pow = Prelude.pow
  sin = Prelude.sin
  cos = Prelude.cos
  tan = Prelude.tan
  asin = Prelude.asin
  acos = Prelude.acos
  atan = Prelude.atan
  sinh = Prelude.sinh
  cosh = Prelude.cosh
  tanh = Prelude.tanh
