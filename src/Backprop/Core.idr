module Backprop.Core

import public Data.List.Quantifiers
import Backprop.Op

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
Num a => Backprop a where
  one = 1
  zero = 0
  add = (+)

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

(Backprop a, Num a) => Backprop (BVar s a) where
  zero = lift zero
  one = lift one
  add = (+)

zeros : {auto prf : All Backprop s} -> HList s
zeros {prf = []} = []
zeros {prf = prf :: prfs} = zero :: zeros

||| create a input gradient only for a specific input
inject : {auto prf : All Backprop s} -> {i : _} -> (0 _ : IElem i a s) -> a -> HList s
inject {prf = prf :: prfs} Here x = x :: zeros
inject {prf = prf :: prfs} (There ptr) x = zero :: inject ptr x

||| combine two input gradients together by adding them pairwise
combine : {auto prf : All Backprop s} -> HList s -> HList s -> HList s
combine {prf = []} [] [] = []
combine {prf = prf :: prfs} (x :: xs) (y :: ys) = add x y :: combine xs ys

||| get a specific input
get : {i : _} -> (0 _ : IElem i a s) -> HList s -> a
get Here (x :: xs) = x
get (There ptr) (x :: xs) = get ptr xs

mutual
  runs : All Backprop s => {auto prf : All Backprop is} -> HList s
    -> All (BVar s) is
    -> (HList is, All (\b => b -> HList s) is)
    -- -> All (\b => (b, b -> HList s)) is
  runs ins [] = ([], [])
  runs {prf = prf :: prfs} ins (i :: is) = let (x, y) = run ins i in bimap (x ::) (y ::) (runs ins is)

  combines : All Backprop s => (backs : All (\b => b -> HList s) is) -> HList is -> HList s
  combines [] [] = zeros
  combines (back :: backs) (x :: xs) = back x `combine` combines backs xs

  ||| input: inputs, output node
  ||| output: (the value, the scaled gradient function of inputs)
  export
  run : All Backprop s => Backprop a => HList s -> BVar s a -> (a, a -> HList s)
  run ins (Input ptr) = (get ptr ins, inject ptr)
  run ins (Const x) = (x, const zeros)
  run ins (Oper op is) =
    let
      (is, backs) = runs ins is
      (forth, back) = do_op op is
    in
      (forth, combines backs . back)

||| input: inputs, output node
||| output: (the value, the gradient of inputs)
export
backprop : {s : _} -> (Backprop a, All Backprop s) => HList s -> BVar s a -> (a, HList s)
backprop ins x = let (y, back) = run ins x in (y, back one)

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
