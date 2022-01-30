module Backprop.Math

import Backprop.CanBack
import Backprop.Node
import Control.Optics
import public Data.Floating
import public Data.Num

export
view : {a, b : _} -> CanBack a => Simple Lens a b -> Node i a -> Node i b
view l = op1 $ \[x] => (x ^. l, \d => [set l d zero])

infixl 0 ^.
export
(^.) : {a, b : _} -> CanBack a => Node i a -> Simple Lens a b -> Node i b
x ^. l = view l x

export
sum : {a : _} -> (CanBack a, NodeFunctor f, Num a, Foldable f) => Node i (f a) -> Node i a
sum x = Prelude.sum $ Node.sequence x

export
max, min : {a : _} -> (CanBack a, Num a, Ord a) => Node i a -> Node i a -> Node i a
max = op2 $ \[x, y] => (max x y, \d => [d * if x > y then 1 else 0, d * if y > x then 1 else 0])
min = op2 $ \[x, y] => (min x y, \d => [d * if x < y then 1 else 0, d * if y < x then 1 else 0])

-- machine learning specific

export
relu : {a : _} -> (CanBack a, Num a, Ord a) => Node i a -> Node i a
relu x = max 0 x
