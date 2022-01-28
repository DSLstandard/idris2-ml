module Backprop.Math

import Backprop.Core
import Backprop.Op

export
sin : BVar s Double -> BVar s Double
sin a = op op_sin [a]

export
exp : BVar s Double -> BVar s Double
exp a = op op_exp [a]

-- machine learning specific

export
sigmoid : BVar s Double -> BVar s Double
sigmoid x = 1 / (1 + exp (-x))
