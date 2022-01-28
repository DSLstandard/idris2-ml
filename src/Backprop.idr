module Backprop

||| `D a` means its related to gradients or derivatives
public export
D : Type -> Type
D a = a

record Op1 i o where
  constructor MkOp1
  run_op1 : i -> (o, D o -> D i)

record Op2 i1 i2 o where
  constructor MkOp2
  run_op2 : i1 -> i2 -> (o, D o -> (D i1, D i2))

op_square : Num a => Op1 a a
op_square = MkOp1 $ \x => (x * x, \d => d * 2 * x)

op_sin : Op1 Double Double
op_sin = MkOp1 $ \x => (sin x, \d => d * cos x)

op_add : Num a => Op2 a a a
op_add = MkOp2 $ \x, y => (x + y, \d => (d, d))

op_sub : Neg a => Op2 a a a
op_sub = MkOp2 $ \x, y => (x - y, \d => (d, -d))

op_mul : Num a => Op2 a a a
op_mul = MkOp2 $ \x, y => (x * y, \d => (d * y, x * d))

op_exp : Op1 Double Double
op_exp = MkOp1 $ \i => (exp i, \d => d * exp i)

op_div : (Neg a, Fractional a) => Op2 a a a
op_div = MkOp2 $ \x, y => (x / y, \d => (d / y, -d * x / (y * y)))

op_recip : (Neg a, Fractional a) => Op1 a a
op_recip = MkOp1 $ \x => (recip x, \d => -d / (x * x))

op_negate : Neg a => Op1 a a
op_negate = MkOp1 $ \x => (-x, \g => -g)

op_abs : Abs a => Op1 a a
op_abs = MkOp1 $ \x => (abs x, ?signum)

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

public export
Backprops : List Type -> Type
Backprops [] = ()
Backprops (x :: xs) = (Backprop x, Backprops xs)

-- graph

||| inputs: a list of the types of the parameters
export
data BVar : (inputs : List Type) -> (a : Type) -> Type where
  Input : {i : _} -> (0 _ : IElem i a s) -> BVar s a
  Const : a -> BVar s a
  Oper1 : Backprop i => Backprop o => Op1 i o -> BVar s i -> BVar s o
  Oper2 : Backprop i1 => Backprop i2 => Backprop o => Op2 i1 i2 o -> BVar s i1 -> BVar s i2 -> BVar s o

export
at : {i : _} -> (0 _ : IElem i a s) -> BVar s a
at = Input

export
FromDouble a => FromDouble (BVar s a) where
  fromDouble = Const . fromDouble

export
(Backprop a, Num a) => Num (BVar s a) where
  (+) = Oper2 op_add
  (*) = Oper2 op_mul
  fromInteger = Const . fromInteger

export
(Backprop a, Neg a) => Neg (BVar s a) where
  negate = Oper1 op_negate
  (-) = Oper2 op_sub

export
(Backprop a, Neg a, Fractional a) => Fractional (BVar s a) where
  (/) = Oper2 op_div
  recip = Oper1 op_recip

export
(Backprop a, Abs a) => Abs (BVar s a) where
  abs = Oper1 op_abs

export
sin : BVar s Double -> BVar s Double
sin = Oper1 op_sin

export
exp : BVar s Double -> BVar s Double
exp = Oper1 op_exp

export
sigmoid : BVar s Double -> BVar s Double
sigmoid x = 1 / (1 + exp (-x))

public export
In : List Type -> Type
In [] = ()
In (x :: xs) = Pair x (In xs)

get : {i : _} -> (0 _ : IElem i a s) -> In s -> a
get Here (x, xs) = x
get (There ptr) (x, xs) = get ptr xs

zeros : {s : _} -> Backprops s => In s
zeros {s = []} = ()
zeros {s = a :: as} = (zero, zeros)

inject : {s : _} -> Backprops s => {i : _} -> (0 _ : IElem i a s) -> a -> In s
inject Here x = (x, zeros)
inject (There ptr) x = (zero, inject ptr x)

combine : {s : _} -> Backprops s => In s -> In s -> In s
combine {s = []} () () = ()
combine {s = a :: as} (x, xs) (y, ys) = (add x y, combine xs ys)

export
run : {s : _} -> (Backprop a, Backprops s) => In s -> BVar s a -> (a, D a -> D (In s))
run ins (Input ptr) = (get ptr ins, inject ptr)
run ins (Const x) = (x, const zeros)
run ins (Oper1 op i) =
  let
    (i, back1) = run ins i
    (forth, back) = run_op1 op i
  in
    (forth, back1 . back)
run ins (Oper2 op i1 i2) =
  let
    (i1, back1) = run ins i1
    (i2, back2) = run ins i2
    (forth, back) = run_op2 op i1 i2
  in
    (forth, uncurry combine . bimap back1 back2 . back)

export
backprop : {s : _} -> (Backprop a, Backprops s) => In s -> BVar s a -> (a, D (In s))
backprop ins x = let (y, back) = run ins x in (y, back one)
