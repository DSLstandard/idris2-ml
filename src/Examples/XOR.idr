module Main

import Backprop
import Control.Algebra
import Control.Optics
import Data.List.Quantifiers
import Data.Nat
import Data.Num
import Data.String.Extra
import Data.Vect
import Debug.Trace
import Linear
import Linear.Backprop
import Linear.Math
import Linear.Random
import NN.Dense
import Utils.String

record Params where
  constructor MkParams
  dense1 : Dense 2 3 Double
  dense2 : Dense 3 1 Double

ldense1 : Simple Lens ? ?
ldense1 = lens dense1 $ \s, b => { dense1 := b } s

ldense2 : Simple Lens ? ?
ldense2 = lens dense2 $ \s, b => { dense2 := b } s

FromDouble Params where
  fromDouble x = MkParams (fromDouble x) (fromDouble x)

CanBack Params where
  zero = MkParams zero zero
  one = MkParams one one
  add (MkParams a1 a2) (MkParams b1 b2) = MkParams (add a1 b1) (add a2 b2)

Num Params where
  (+) = add
  MkParams a1 a2 * MkParams b1 b2 = MkParams (a1 * b1) (a2 * b2)
  fromInteger x = MkParams (fromInteger x) (fromInteger x)

Neg Params where
  MkParams a1 a2 - MkParams b1 b2 = MkParams (a1 - b1) (a2 - b2)
  negate (MkParams a1 a2) = MkParams (negate a1) (negate a2)

Show Params where
  show params = show_record "MkParams" [("dense1", show params.dense1), ("dense2", show params.dense2)]

model : {n : _} -> Node i Params -> Node i (T [n, 2] Double) -> Node i (T [n, 1] Double)
model p = sigmoid . apply (p ^. ldense2) . sigmoid . apply (p ^. ldense1)

loss : {a, n : _} -> Neg a => CanBack a => Floating a => (y : Node i (T [n, 1] a)) -> (y' : Node i (T [n, 1] a)) -> Node i a
loss y y' = asum $ asum $ square (y - y')

gd : {loss_t : _} -> (Neg params_t, Num params_t, CanBack params_t, CanBack loss_t, FromDouble params_t) => (loss_node : Node params_t loss_t) -> (params : params_t) -> (learning_rate : Double) -> (loss_t, params_t)
gd loss_node params alpha = let (loss, grads) = backprop loss_node params in (loss, params - fromDouble alpha * grads)

gdn : {loss_t : _} -> HasIO m => (Neg params_t, Show loss_t, Show params_t, Num params_t, CanBack params_t, CanBack loss_t, FromDouble params_t) => (iterations : Nat) -> (loss_node : Node params_t loss_t) -> (params : params_t) -> (learning_rate : Double) -> m params_t
gdn Z loss_node params alpha = pure params
gdn (S i) loss_node params alpha = do
  let (loss, params) = gd loss_node params alpha
  putStrLn $ "\{show i}: loss: \{show loss}"
  gdn i loss_node params alpha

main : IO ()
main = do
  putStrLn "begin"
  let x = the (T [_, _] Double) $ [[0, 0], [0, 1], [1, 0], [1, 1]]
  let y' = the (T [_, _] Double) $ [[0], [1], [1], [0]]
  params <- pure $ MkParams (MkDense !rand_m !rand_v) (MkDense !rand_m !rand_v)
  params <- gdn 100 (loss (model input (const x)) (const y')) params pi
  printLn "done"
