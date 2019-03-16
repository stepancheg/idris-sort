module TotalOrderLite

import TotalOrder

%default total

public export
record TotalOrderLiteImpl (a : Type) where
    constructor TotalOrderLiteImpl_mk
    lte : a -> a -> Type -- <=
    isLTE : (x, y : a) -> Dec (lte x y)
    lte_trans : {x, y, z : a} -> lte x y -> lte y z -> lte x z -- transitivity
    not_lte_implies_gte : {x, y : a} -> Not (lte x y) -> lte y x -- antisymmetry

public export
totalOrderLiteFromFull : TotalOrder a -> TotalOrderLiteImpl a
totalOrderLiteFromFull t = TotalOrderLiteImpl_mk (CmpLTE t) cmpLTE_isLTE lte_trans not_lte_implies_gte

public export
interface TotalOrderLite a where
    totalOrderLite : TotalOrderLiteImpl a

public export
totalOrderLiteRev : TotalOrderLiteImpl a -> TotalOrderLiteImpl a
totalOrderLiteRev t = TotalOrderLiteImpl_mk
    (flip $ lte t)
    (\x, y => isLTE t y x)
    (flip $ lte_trans t)
    (not_lte_implies_gte t)
