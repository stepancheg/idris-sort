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

data FullLTE : TotalOrderImpl a -> a -> a -> Type where
    FullLT : lt t x y -> FullLTE t x y
    FullEq : eq t x y -> FullLTE t x y

gt_implies_not_lte : lt t y x -> Not (FullLTE t x y)
gt_implies_not_lte gt (FullLT lt) = lt_implies_not_gt _ gt lt
gt_implies_not_lte gt (FullEq eq) = lt_implies_not_eq _ gt (eq_symm _ eq)

cmpLTE_isLTE : (x, y : a) -> Dec (FullLTE t x y)
cmpLTE_isLTE {t} x y with (cmp t x y)
    cmpLTE_isLTE x y | (XLT lt) = Yes (FullLT lt)
    cmpLTE_isLTE x y | (XEQ eq) = Yes (FullEq eq)
    cmpLTE_isLTE {t} x y | (XGT gt) = No (gt_implies_not_lte gt)

full_lte_trans : FullLTE t x y -> FullLTE t y z -> FullLTE t x z
full_lte_trans (FullLT lt_x_y) (FullLT lt_y_z) = FullLT (lt_trans t lt_x_y lt_y_z)
full_lte_trans (FullEq eq_x_y) (FullEq eq_y_z) = FullEq (eq_trans t eq_x_y eq_y_z)
full_lte_trans (FullLT lt_x_y) (FullEq eq_y_z) = FullLT (lt_eq_implies_lt t lt_x_y eq_y_z)
full_lte_trans (FullEq eq_x_y) (FullLT lt_y_z) = FullLT (eq_lt_implies_lt t eq_x_y lt_y_z)

full_not_lte_implies_gte : Not (FullLTE t x y) -> FullLTE t y x
full_not_lte_implies_gte {t} {x} {y} not_lte with (cmp t x y)
    full_not_lte_implies_gte {t} {x} {y} not_lte | (XLT lt) = absurd $ not_lte (FullLT lt)
    full_not_lte_implies_gte {t} {x} {y} not_lte | (XEQ eq) = absurd $ not_lte (FullEq eq)
    full_not_lte_implies_gte {t} {x} {y} not_lte | (XGT gt) = FullLT gt

export
totalOrderLiteFromFull : TotalOrderImpl a -> TotalOrderLiteImpl a
totalOrderLiteFromFull t = TotalOrderLiteImpl_mk
    (FullLTE t)
    cmpLTE_isLTE
    full_lte_trans
    full_not_lte_implies_gte

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
