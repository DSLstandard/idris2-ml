module Backprop.Core

import Backprop.CanBack
import Backprop.Op
import Control.Optics
import Linear.HList
import public Data.List.Quantifiers

%hide Data.Morphisms.Op

export
data Node : (i : Type) -> (o : Type) -> Type where
  ||| the input itself
  Input : Node a a
  ||| an operation
  Oper : {args : _} -> All CanBack args => Op args o -> All (Node i) args -> Node i o

||| get input
export
input : Node a a
input = Input

||| lift an operation into a `Node`
export
op : {args : _} -> All CanBack args => Op args o -> All (Node i) args -> Node i o
op = Oper

||| lift a constant into a `Node`
export
const : a -> Node i a
const x = op (op_const x) []

export
FromDouble a => FromDouble (Node i a) where
  fromDouble = const . fromDouble

export
(a : _) => (CanBack a, Num a) => Num (Node i a) where
  a + b = op op_add [a, b]
  a * b = op op_mul [a, b]
  fromInteger = const . fromInteger

export
(a : _) => (CanBack a, Neg a) => Neg (Node i a) where
  a - b = op op_sub [a, b]
  negate a = op op_negate [a]

export
(a : _) => (CanBack a, Neg a, Fractional a) => Fractional (Node i a) where
  a / b = op op_div [a, b]
  recip a = op op_recip [a]

export
(a : _) => (CanBack a, Ord a, Neg a, Abs a) => Abs (Node i a) where
  abs a = op op_abs [a]

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
      (output, back) = do_op op args
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
  eval (Oper op args) input = fst $ do_op op (eval_all args input)
