module Backprop.Core

import Backprop.Op
import Linear.HList
import public Data.List.Quantifiers

namespace IElem
  public export
  data IElem : Nat -> a -> List a -> Type where
    Here : IElem Z x (x :: xs)
    There : IElem i x xs -> IElem (S i) x (x' :: xs)

  public export
  Uninhabited (IElem i x []) where
    uninhabited _ impossible

  public export
  data IElemed : a -> List a -> Type where
    Exist : {i : _} -> (0 _ : IElem i x xs) -> IElemed x xs

  public export
  embed : {i : _} -> (0 _ : IElem i x xs) -> IElem i x (xs ++ right)
  embed Here = Here
  embed (There ptr) = There (embed ptr)

  public export
  weaken : (left : _) -> {i : _} -> (0 _ : IElem i x xs) -> IElem (plus (length left) i) x (left ++ xs)
  weaken [] Here = Here
  weaken [] (There ptr) = There (weaken [] ptr)
  weaken (k :: left) ptr = There (weaken left ptr)

  public export
  insert : (left, xs : _) -> {i : _} -> (0 ptr : IElem i x (left ++ right)) -> IElemed x ((left ++ xs) ++ right)
  insert [] xs ptr = Exist (weaken xs ptr)
  insert (k :: left) xs Here = Exist Here
  insert (k :: left) xs (There ptr) = let Exist ptr' = insert left xs ptr in Exist (There ptr')

||| an interface used for manipulating gradient values of type `a` when backpropagating
public export
interface Backprop a where
  ||| representation of 1
  one : a
  ||| representation of 0
  zero : a
  ||| addition
  add : a -> a -> a

export
Backprop Double where
  one = 1
  zero = 0
  add = (+)

-- export
-- Num a => Backprop a where
--   one = 1
--   zero = 0
--   add = (+)

mutual
  ||| s : a list of the types of the parameters
  ||| a : output type
  export
  data BVar : (s : List Type) -> (a : Type) -> Type where
    ||| an input
    Input : {i : _} -> (0 _ : IElem i a s) -> BVar s a
    ||| a constant
    Const : a -> BVar s a
    ||| an operation
    Oper : All Backprop is => Op is o -> All (BVar s) is -> BVar s o

||| reference to an input according
export
at : {i : _} -> (0 _ : IElem i a s) -> BVar s a
at = Input

||| lift an operation into a `BVar`
export
op : All Backprop is => Op is o -> All (BVar s) is -> BVar s o
op = Oper

||| lift a constant into a `BVar`
export
lift : a -> BVar s a
lift = Const

||| insert new input parameters in a `BVar s a`
export
insert : {left, new : _} -> BVar (left <+> right) a -> BVar (left <+> new <+> right) a
insert (Const x) = Const x
insert (Input ptr) = let Exist ptr = insert _ _ ptr in Input ptr
insert (Oper op args) = Oper op (mapProperty insert args)

export
FromDouble a => FromDouble (BVar s a) where
  fromDouble = Const . fromDouble

export
(Backprop a, Num a) => Num (BVar s a) where
  a + b = op op_add [a, b]
  a * b = op op_mul [a, b]
  fromInteger = Const . fromInteger

export
(Backprop a, Neg a) => Neg (BVar s a) where
  a - b = op op_sub [a, b]
  negate a = op op_negate [a]

export
(Backprop a, Neg a, Fractional a) => Fractional (BVar s a) where
  a / b = op op_div [a, b]
  recip a = op op_recip [a]

export
(Backprop a, Ord a, Neg a, Abs a) => Abs (BVar s a) where
  abs a = op op_abs [a]

export
Num a => Backprop (BVar s a) where
  one = 1
  zero = 0
  add = (+)

-- export
-- (Backprop a, Num a) => Backprop (BVar s a) where
--   zero = lift zero
--   one = lift one
--   add = (+)

export
Backprop (HList []) where
  zero = []
  one = []
  add [] [] = []

export
Backprop a => Backprop (HList as) => Backprop (HList (a :: as)) where
  zero = zero :: zero
  one = one :: one
  add (x :: xs) (y :: ys) = add x y :: add xs ys

export
(prf : All Backprop as) => Backprop (HList as) where
  zero {prf = []} = []
  zero {prf = prf :: prfs} = zero :: zero
  one {prf = []} = []
  one {prf = prf :: prfs} = one :: one
  add [] [] = []
  add {prf = prf :: prfs} (x :: xs) (y :: ys) = add x y :: add xs ys

||| create a input gradient only for a specific input
inject : {auto prf : All Backprop s} -> {i : _} -> (0 _ : IElem i a s) -> a -> HList s
inject {prf = prf :: prfs} Here x = x :: zero
inject {prf = prf :: prfs} (There ptr) x = zero :: inject ptr x

||| get a specific input
get : {i : _} -> (0 _ : IElem i a s) -> HList s -> a
get Here (x :: xs) = x
get (There ptr) (x :: xs) = get ptr xs

mutual
  runs : All Backprop s => {auto prf : All Backprop is} -> HList s
    -> All (BVar s) is
    -> (HList is, All (\b => b -> HList s) is)
  runs ins [] = ([], [])
  runs {prf = prf :: prfs} ins (i :: is) = let (x, y) = run ins i in bimap (x ::) (y ::) (runs ins is)

  adds : All Backprop s => (backs : All (\b => b -> HList s) is) -> HList is -> HList s
  adds [] [] = zero
  adds (back :: backs) (x :: xs) = back x `add` adds backs xs

  ||| input: inputs, output node
  ||| output: (the value, the scaled gradient function of inputs)
  export
  run : All Backprop s => Backprop a => HList s -> BVar s a -> (a, a -> HList s)
  run ins (Input ptr) = (get ptr ins, inject ptr)
  run ins (Const x) = (x, const zero)
  run ins (Oper op is) =
    let
      (is, backs) = runs ins is
      (forth, back) = do_op op is
    in
      (forth, adds backs . back)

||| input: inputs, output node
||| output: (the value, the gradient of inputs)
export
backprop : (Backprop a, All Backprop s) => HList s -> BVar s a -> (a, HList s)
backprop ins x = let (y, back) = run ins x in (y, back one)

||| `backprop` but discards output value
export
grad : (Backprop a, All Backprop s) => HList s -> BVar s a -> HList s
grad ins x = snd $ backprop ins x

mutual
  evals : HList s -> All (BVar s) is -> HList is
  evals ins [] = []
  evals ins (i :: is) = eval ins i :: evals ins is

  ||| evaluates a `BVar`, more efficient than `run` as gradient calculations are skipped
  |||
  ||| input: inputs, output node
  ||| output: output value
  export
  eval : HList s -> BVar s a -> a
  eval ins (Input ptr) = get ptr ins
  eval ins (Const x) = x
  eval ins (Oper op is) = fst $ do_op op (evals ins is)

||| get all inputs under `s`
export
inputs : {s : _} -> All (\b => BVar s b) s
inputs {s = []} = []
inputs {s = a :: as} = Input Here :: mapProperty (insert {left = [], new = [a]}) (inputs {s = as})

||| runs a function which takes all inputs, useful for writing equations without spamming `at`
|||
||| example:
|||   f = the (BVar [Double, Double] _) $ scope $ \[x, y] => sigmoid x * sigmoid y
export
scope : {s : _} -> (All (\a => BVar s a) s -> BVar s b) -> BVar s b
scope f = f inputs
