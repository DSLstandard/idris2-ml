module Linear.Math

import public Data.Floating
import public Data.Num

export
sigmoid : (Neg a, Floating a) => a -> a
sigmoid x = 1 / (1 + exp (-x))

export
relu : (Num a, Ord a) => a -> a
relu x = max 0 x
