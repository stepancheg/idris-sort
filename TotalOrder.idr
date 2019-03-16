module TotalOrder

%default total

-- Result of comparison
public export
data OrderingX : lt -> eq -> gt -> Type where
    XLT : {lt, eq, gt : Type} -> lt -> OrderingX lt eq gt
    XEQ : {lt, eq, gt : Type} -> eq -> OrderingX lt eq gt
    XGT : {lt, eq, gt : Type} -> gt -> OrderingX lt eq gt

public export
record TotalOrder (a : Type) where
    constructor TotalOrder_mk
    -- <
    lt : a -> a -> Type
    -- =
    eq : a -> a -> Type
    -- compare x and y
    cmp : (x, y : a) -> OrderingX (lt x y) (eq x y) (lt y x)
    -- < must be transitive
    lt_trans : {x, y, z : a} -> lt x y -> lt y z -> lt x z
    -- = must be transitive
    eq_trans : {x, y, z : a} -> eq x y -> eq y z -> eq x z
    -- = must be symmetric
    eq_symm : {x, y : a} -> eq x y -> eq y x
    lt_implies_not_eq : {x, y : a} -> lt x y -> Not (eq x y)
    lt_implies_not_gt : {x, y : a} -> lt x y -> Not (lt y x)
    eq_implies_not_lt : {x, y : a} -> eq x y -> Not (lt x y)
    lt_eq_implies_lt : {x, y, z : a} -> lt x y -> eq y z -> lt x z
    eq_lt_implies_lt : {x, y, z : a} -> eq x y -> lt y z -> lt x z

gt : (t : TotalOrder a) -> a -> a -> Type
gt t x y = lt t y x

export
cmpTypes_rev : TotalOrder a -> TotalOrder a
cmpTypes_rev t = TotalOrder_mk
    (\x, y => lt t y x)
    (\x, y => eq t y x)
    (\x, y => case cmp t x y of
        XLT lt => XGT lt
        XEQ eq => XEQ ((eq_symm t) eq)
        XGT gt => XLT gt
    )
    (flip $ lt_trans t)
    (flip $ eq_trans t)
    (eq_symm t)
    (lt_implies_not_eq t)
    (lt_implies_not_gt t)
    (eq_implies_not_lt t)
    (flip $ eq_lt_implies_lt t)
    (flip $ lt_eq_implies_lt t)

export
data CmpLTE : TotalOrder a -> a -> a -> Type where
    LTELT : lt t x y -> CmpLTE t x y
    LTEEQ : eq t x y -> CmpLTE t x y

gt_implies_not_lte : lt t y x -> Not (CmpLTE t x y)
gt_implies_not_lte gt (LTELT lt) = lt_implies_not_gt _ gt lt
gt_implies_not_lte gt (LTEEQ eq) = lt_implies_not_eq _ gt (eq_symm _ eq)

export
lte_trans : CmpLTE t x y -> CmpLTE t y z -> CmpLTE t x z
lte_trans (LTELT lt_x_y) (LTELT lt_y_z) = LTELT (lt_trans t lt_x_y lt_y_z)
lte_trans (LTEEQ eq_x_y) (LTEEQ eq_y_z) = LTEEQ (eq_trans t eq_x_y eq_y_z)
lte_trans (LTELT lt_x_y) (LTEEQ eq_y_z) = LTELT (lt_eq_implies_lt t lt_x_y eq_y_z)
lte_trans (LTEEQ eq_x_y) (LTELT lt_y_z) = LTELT (eq_lt_implies_lt t eq_x_y lt_y_z)

export
not_lte_implies_gte : Not (CmpLTE t x y) -> CmpLTE t y x
not_lte_implies_gte {t} {x} {y} not_lte with (cmp t x y)
    not_lte_implies_gte {t} {x} {y} not_lte | (XLT lt) = absurd $ not_lte (LTELT lt)
    not_lte_implies_gte {t} {x} {y} not_lte | (XEQ eq) = absurd $ not_lte (LTEEQ eq)
    not_lte_implies_gte {t} {x} {y} not_lte | (XGT gt) = LTELT gt

export
cmpLTE_isLTE : (x, y : a) -> Dec (CmpLTE t x y)
cmpLTE_isLTE {t} x y with (cmp t x y)
    cmpLTE_isLTE x y | (XLT lt) = Yes (LTELT lt)
    cmpLTE_isLTE x y | (XEQ eq) = Yes (LTEEQ eq)
    cmpLTE_isLTE {t} x y | (XGT gt) = No (gt_implies_not_lte gt)
