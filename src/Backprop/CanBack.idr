module Backprop.CanBack

import Data.Vect

||| an interface used for manipulating gradient values of type `a` when backpropagating
public export
interface CanBack a where
  ||| representation of 1
  one : a
  ||| representation of 0
  zero : a
  ||| addition
  add : a -> a -> a

export
CanBack Double where
  one = 1
  zero = 0
  add = (+)
