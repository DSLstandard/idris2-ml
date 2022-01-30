module Backprop.Node

import Backprop.CanBack
import Backprop.MathUtils
import Control.Optics
import Data.Floating
import public Data.List.Quantifiers

%hide Data.Morphisms.Op

public export
Op : (args : List Type) -> (o : Type) -> Type
Op args o = HList args -> Pair o (o -> HList args)

export
data Node : (i : Type) -> (o : Type) -> Type where
  ||| the input itself
  Input : Node a a
  ||| an operation
  Oper : {args : _} -> All CanBack args => Op args o -> All (Node i) args -> Node i o

public export
interface Functor f => NodeDistributive f where
  collect : {o : _} -> CanBack o => f (Node i o) -> Node i (f o)

public export
interface Functor f => NodeTraversable f where
  sequence : {o : _} -> CanBack o => Node i (f o) -> f (Node i o)

public export
NodeFunctor : (Type -> Type) -> Type
NodeFunctor f = (NodeTraversable f, NodeDistributive f)

export
map : {a, b : _} -> (CanBack a, CanBack b, NodeFunctor f) => (Node i a -> Node i b) -> Node i (f a) -> Node i (f b)
map f = collect . map f . sequence

export
input : Node a a
input = Input

export
op1 : {a1 : _} -> CanBack a1 => Op [a1] o -> Node i a1 -> Node i o
op1 op x = Oper op [x]

export
op2 : {a1, a2 : _} -> CanBack a1 => CanBack a2 => Op [a1, a2] o -> Node i a1 -> Node i a2 -> Node i o
op2 op x y = Oper op [x, y]

||| lift a constant into a `Node`
export
const : a -> Node i a
const x = Oper (\[] => (x, const [])) []

export
FromDouble a => FromDouble (Node i a) where
  fromDouble = const . fromDouble

export
{a : _} -> (CanBack a, Num a) => Num (Node i a) where
  (+) = op2 $ \[x, y] => (x + y, \d => [d, d])
  (*) = op2 $ \[x, y] => (x * y, \d => [d * y, x * d])
  fromInteger = const . fromInteger

export
{a : _} -> (CanBack a, Neg a) => Neg (Node i a) where
  (-) = op2 $ \[x, y] => (x - y, \d => [d, -d])
  negate = op1 $ \[x] => (-x, \d => [-d])

export
{a : _} -> (CanBack a, Ord a, Neg a, Abs a) => Abs (Node i a) where
  abs = op1 $ \[x] => (abs x, \d => [d * signum_zero x])

export
{a : _} -> (CanBack a, Neg a, Fractional a) => Fractional (Node i a) where
  (/) = op2 $ \[x, y] => (x / y, \d => [d / y, -d * x / (y * y)])
  recip = op1 $ \[x] => (recip x, \d => [-d / (x * x)])

export
{a : _} -> (CanBack a, Neg a, Floating a, Fractional (Node i a)) => Floating (Node i a) where
  pi = const pi
  sqrt = op1 $ \[x] => (sqrt x, \d => [d / (2 * sqrt x)])
  exp = op1 $ \[x] => (exp x, \d => [d * exp x])
  ln = op1 $ \[x] => (ln x, \d => [d / x])
  log base x = ln x / ln base
  pow = op2 $ \[x, y] =>
    ( pow x y
    , \d => let k = d * pow x (y - 1) in [k * y, k * x * ln x]
    )
  sin = op1 $ \[x] => (sin x, \d => [d * cos x])
  cos = op1 $ \[x] => (cos x, \d => [d * -sin x])
  tan = op1 $ \[x] => (tan x, \d => let cos' = cos x in [d / (cos' * cos')])
  asin = op1 $ \[x] => (asin x, \d => [d / sqrt (1 - x * x)])
  acos = op1 $ \[x] => (acos x, \d => [-d / sqrt (1 - x * x)])
  atan = op1 $ \[x] => (atan x, \d => [d / (1 - x * x)])
  sinh = op1 $ \[x] => (sinh x, \d => [d * cosh x])
  cosh = op1 $ \[x] => (cosh x, \d => [d * sinh x])
  tanh = op1 $ \[x] => (tanh x, \d => let cosh' = cosh x in [d / (cosh' * cosh')])

mutual
  run_all : {as : _} -> {auto prf : All CanBack as} -> CanBack i => All (Node i) as -> i -> (HList as, All (\b => b -> i -> i) as)
  run_all [] input = ([], [])
  run_all {prf = prf :: prfs} (arg :: args) input =
    let (x, y) = run arg input in bimap (x ::) (y ::) (run_all {prf = prfs} args input)

  combine_all : (backs : All (\b => b -> i -> i) as) -> HList as -> i -> i
  combine_all [] [] = id
  combine_all (back :: backs) (x :: xs) = combine_all backs xs . back x

  export
  run : {o : _} -> {auto prf : CanBack i} -> CanBack o => Node i o -> i -> (o, o -> i -> i)
  run Input input = (input, \d => add @{prf} d)
  run (Oper op arg_nodes) input =
    let
      (args, backs) = run_all arg_nodes input
      (output, back) = op args
    in
      (output, combine_all backs . back)

||| output: (the value, the gradient of inputs)
export
backprop : {o : _} -> (CanBack i, CanBack o) => Node i o -> i -> (o, i)
backprop node input = let (y, back) = run node input in (y, back one zero)

||| `backprop` but discards output value
export
grad : {o : _} -> (CanBack i, CanBack o) => Node i o -> i -> i
grad node input = snd $ backprop node input

mutual
  eval_all : All (Node i) as -> i -> HList as
  eval_all [] input = []
  eval_all (x :: xs) input = eval x input :: eval_all xs input

  ||| evaluates a `Node`, more efficient than `run` as gradient calculations are skipped
  |||
  ||| input: inputs, output node
  ||| output: output value
  export
  eval : Node i o -> i -> o
  eval Input input = input
  eval (Oper op args) input = fst $ op (eval_all args input)
