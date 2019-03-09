module TotalOrder

%default total

public export
data TotalOrder : (a : Type) -> (a -> a -> Type) -> Type where
    TotalOrderInst :
        (a : Type)
        -> (lte : a -> a -> Type) -- <=
        -> ((x, y : a) -> Dec (lte x y)) -- isLTE
        -> ({x, y, z : a} -> lte x y -> lte y z -> lte x z) -- transitivity
        -> ({x, y : a} -> Not (lte x y) -> lte y x) -- antisymmetry
        -> TotalOrder a lte
