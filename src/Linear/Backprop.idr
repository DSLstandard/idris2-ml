module Linear.Backprop

import Backprop
import Control.Optics
import Linear.V
import Linear.Math
import Linear.Optics

export
{n : _} -> CanBack a => CanBack (V n a) where
  zero = pure zero
  one = pure one
  add [] [] = []
  add (x :: xs) (y :: ys) = add x y :: add xs ys

export
(::) : {a, n : _} -> CanBack a => Node s a -> Node s (V n a) -> Node s (V (S n) a)
(::) = op2 $ \[x, xs] => (x :: xs, \(d :: ds) => [d, ds])

export
{n : _} -> NodeTraversable (V n) where
  sequence x = map (\i => x ^. at i) Fin.range

export
{n : _} -> NodeDistributive (V n) where
  collect [] = const []
  collect (node :: nodes) = node :: collect nodes

export
konst : {a, n : _} -> Num a => CanBack a => Node i a -> Node i (V n a)
konst = op1 $ \[x] => (pure x, \d => [sum d])

export
dot : {a : _} -> (Num a, CanBack a, Foldable f, Zippable f, NodeFunctor f)
  => Node i (f a) -> Node i (f a) -> Node i a
dot x y = V.dot (Node.sequence x) (Node.sequence y)

infixl 7 <.>
export
(<.>) : {a, n : _} -> Num a => CanBack a => Node i (V n a) -> Node i (V n a) -> Node i a
(<.>) = op2 $ \[x, y] => (x `dot` y, \d => let d' = pure d in [d' * y, x * d'])

export
outer : {n, m, a : _} -> (Num a, CanBack a) => Node i (T [n] a) -> Node i (T [m] a) -> Node i (T [n, m] a)
outer = op2 $ \[x, y] => (x `outer` y, \d => [d !* y, transpose d !* x])

export
(#>) : {m, n, a : _} -> Num a => CanBack a => Node i (T [m, n] a) -> Node i (T [n] a) -> Node i (T [m] a)
(#>) = op2 $ \[x, y] => (x !* y, \d => [d `outer` y, transpose x !* d])

-- export
-- (<#) : {m, n, a : _} -> Num a => CanBack a => Node i (T [m] a) -> Node i (T [m, n] a) -> Node i (T [n] a)

export
(*^) : {a : _} -> CanBack a => Num a => NodeFunctor f => Node i a -> Node i (f a) -> Node i (f a)
(*^) a = Node.map (a *)

export
(^*) : {a : _} -> CanBack a => NodeFunctor f => Num a => Node i (f a) -> Node i a -> Node i (f a)
x ^* y = y *^ x

-- export
-- (*!) : {a, f : _} -> (CanBack a, Num a, CanBack (f a), NodeTraversable t, NodeTraversable f, Functor t)
--   => Node i (t a) -> Node i (t (f a)) -> Node i (f a)

infixr 7 <>
export
(<>) : {n, p, m, a : _} -> (Num a, CanBack a) => Node i (T [m, n] a) -> Node i (T [n, p] a) -> Node i (T [m, p] a)
(<>) = op2 $ \[x, y] => (x !*! y, \d => [d !*! transpose y, transpose x !*! d])

export
asum : {a, n : _} -> Num a => CanBack a => Node i (V n a) -> Node i a
asum = op1 $ \[x] => (sum x, \d => [pure d])
