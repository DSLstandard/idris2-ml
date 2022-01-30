module NN.Dense

import Backprop
import Control.Optics
import Linear.Backprop
import Linear.V
import Utils.String

public export
record Dense (i : Nat) (o : Nat) (a : Type) where
  constructor MkDense
  weights : T [i, o] a
  biases : T [o] a

export
lweights : Simple Lens (Dense i o a) (T [i, o] a)
lweights = lens weights (\s, b => { weights := b } s)

export
lbiases : Simple Lens (Dense i o a) (T [o] a)
lbiases = lens biases (\s, b => { biases := b } s)

export
{i : _} -> {o : _} -> FromDouble a => FromDouble (Dense i o a) where
  fromDouble x = MkDense (fromDouble x) (fromDouble x)

export
{i : _} -> {o : _} -> CanBack a => CanBack (Dense i o a) where
  zero = MkDense zero zero
  one = MkDense one one
  add x1 x2 = MkDense (add x1.weights x2.weights) (add x1.biases x2.biases)

export
{i : _} -> {o : _} -> Num a => Num (Dense i o a) where
  x1 + x2 = MkDense (x1.weights + x2.weights) (x1.biases + x2.biases)
  x1 * x2 = MkDense (x1.weights * x2.weights) (x1.biases * x2.biases)
  fromInteger x = MkDense (fromInteger x) (fromInteger x)

export
{i : _} -> {o : _} -> Neg a => Neg (Dense i o a) where
  x1 - x2 = MkDense (x1.weights - x2.weights) (x1.biases - x2.biases)
  negate x = MkDense (negate x.weights) (negate x.biases)

export
Show a => Show (Dense i o a) where
  show x = show_record "MkDense" [("weights", show x.weights), ("biases", show x.biases)]

export
apply : {i, o, n, a : _} -> CanBack a => Num a => Node s (Dense i o a) -> Node s (T [n, i] a) -> Node s (T [n, o] a)
apply layer x = x <> (layer ^. lweights) + konst (layer ^. lbiases)
