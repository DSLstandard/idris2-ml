module Backprop.CanBack

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
Num a => CanBack a where
  one = 1
  zero = 0
  add = (+)
