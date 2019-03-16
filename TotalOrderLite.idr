module TotalOrderLite

import TotalOrder

%default total

public export
data TotalOrderLite : (a : Type) -> (a -> a -> Type) -> Type where
    TotalOrderInst :
        (a : Type)
        -> (lte : a -> a -> Type) -- <=
        -> ((x, y : a) -> Dec (lte x y)) -- isLTE
        -> ({x, y, z : a} -> lte x y -> lte y z -> lte x z) -- transitivity
        -> ({x, y : a} -> Not (lte x y) -> lte y x) -- antisymmetry
        -> TotalOrderLite a lte

export
totalOrderLiteFromFull : (t : TotalOrder a) -> TotalOrderLite a (CmpLTE t)
totalOrderLiteFromFull {a} t = TotalOrderInst a (CmpLTE t) cmpLTE_isLTE lte_trans not_lte_implies_gte
