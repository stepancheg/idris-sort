module TotalOrderLite

import TotalOrder

%default total

public export
record TotalOrderLite (a : Type) where
    constructor TotalOrderLite_mk
    lte : a -> a -> Type -- <=
    isLTE : (x, y : a) -> Dec (lte x y)
    lte_trans : {x, y, z : a} -> lte x y -> lte y z -> lte x z -- transitivity
    not_lte_implies_gte : {x, y : a} -> Not (lte x y) -> lte y x -- antisymmetry

public export
totalOrderLiteFromFull : TotalOrder a -> TotalOrderLite a
totalOrderLiteFromFull t = TotalOrderLite_mk (CmpLTE t) cmpLTE_isLTE lte_trans not_lte_implies_gte

public export
interface TotalOrderLiteInterface a where
    totalOrderLite : TotalOrderLite a
