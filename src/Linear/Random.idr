module Linear.Random

import Linear.V
import public System.Random

export
{n : _} -> Random a => Random (V n a) where
  randomIO = sequence $ pure $ randomIO
  randomRIO ([], []) = pure []
  randomRIO ((x :: xs), (y :: ys)) = pure $ !(randomRIO (x, y)) :: !(randomRIO (xs, ys))

||| random between 0 and 1
export
rand : HasIO m => Random a => {ns : _} -> m (T ns a)
rand {ns = []} = randomIO
rand {ns = n :: ns} = sequence $ pure $ rand

export
rand_v : HasIO m => Random a => {n : _} -> m (T [n] a)
rand_v = rand {ns = [_]}

export
rand_m : HasIO m => Random a => {n, p : _} -> m (T [n, p] a)
rand_m = rand {ns = [_, _]}

||| random between `low` and `high`
export
uniform : HasIO m => Random a => {ns : _} -> (low : a) -> (high : a) -> m (T ns a)
uniform {ns = []} low high = randomRIO (low, high)
uniform {ns = n :: ns} low high = sequence $ pure $ uniform low high
