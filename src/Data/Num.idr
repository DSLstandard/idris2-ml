module Data.Num

||| integral power
export
power : Num a => a -> Nat -> a
power a Z = 1
power a (S i) = a * power a i

export
square : Num a => a -> a
square x = power x 2

export
cube : Num a => a -> a
cube x = power x 3
