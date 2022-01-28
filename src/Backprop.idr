module Backprop

import public Data.List.Quantifiers
import Backprop.Op

public export
data IElem : Nat -> a -> List a -> Type where
  Here : IElem Z x (x :: xs)
  There : IElem i x xs -> IElem (S i) x (x' :: xs)

public export
Uninhabited (IElem i x []) where
  uninhabited _ impossible

-- backprop

public export
interface Backprop a where
  one : a
  zero : a
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
    ||| a operation
    Oper : All Backprop is => Op is o -> All (BVar s) is -> BVar s o

export
at : {i : _} -> (0 _ : IElem i a s) -> BVar s a
at = Input

export
FromDouble a => FromDouble (BVar s a) where
  fromDouble = Const . fromDouble

export
(Backprop a, Num a) => Num (BVar s a) where
  a + b = Oper op_add [a, b]
  a * b = Oper op_mul [a, b]
  fromInteger = Const . fromInteger

export
(Backprop a, Neg a) => Neg (BVar s a) where
  a - b = Oper op_sub [a, b]
  negate a = Oper op_negate [a]

export
(Backprop a, Neg a, Fractional a) => Fractional (BVar s a) where
  a / b = Oper op_div [a, b]
  recip a = Oper op_recip [a]

export
(Backprop a, Abs a) => Abs (BVar s a) where
  abs a = Oper op_abs [a]

export
sin : BVar s Double -> BVar s Double
sin a = Oper op_sin [a]

export
exp : BVar s Double -> BVar s Double
exp a = Oper op_exp [a]

export
sigmoid : BVar s Double -> BVar s Double
sigmoid x = 1 / (1 + exp (-x))

get : {i : _} -> (0 _ : IElem i a s) -> HList s -> a
get Here (x :: xs) = x
get (There ptr) (x :: xs) = get ptr xs

zeros : {auto prf : All Backprop s} -> HList s
zeros {prf = []} = []
zeros {prf = prf :: prfs} = zero :: zeros

inject : {auto prf : All Backprop s} -> {i : _} -> (0 _ : IElem i a s) -> a -> HList s
inject {prf = prf :: prfs} Here x = x :: zeros
inject {prf = prf :: prfs} (There ptr) x = zero :: inject ptr x

combine : {auto prf : All Backprop s} -> HList s -> HList s -> HList s
combine {prf = []} [] [] = []
combine {prf = prf :: prfs} (x :: xs) (y :: ys) = add x y :: combine xs ys

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

export
backprop : {s : _} -> (Backprop a, All Backprop s) => HList s -> BVar s a -> (a, HList s)
backprop ins x = let (y, back) = run ins x in (y, back one)
