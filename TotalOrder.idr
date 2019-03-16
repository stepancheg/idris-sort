module TotalOrder

%default total
%access public export

-- Result of comparison
public export
data OrderingX : lt -> eq -> gt -> Type where
    XLT : {lt, eq, gt : Type} -> lt -> OrderingX lt eq gt
    XEQ : {lt, eq, gt : Type} -> eq -> OrderingX lt eq gt
    XGT : {lt, eq, gt : Type} -> gt -> OrderingX lt eq gt

public export
record TotalOrderImpl (a : Type) where
    constructor TotalOrderImpl_mk
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

public export
gt : (t : TotalOrderImpl a) -> a -> a -> Type
gt t x y = lt t y x

public export
isLT : (t : TotalOrderImpl a) -> (x, y : a) -> Dec (lt t x y)
isLT t x y with (cmp t x y)
    isLT t x y | (XLT lt_x_y) = Yes lt_x_y
    isLT t x y | (XEQ eq_x_y) = No (\lt_x_y => lt_implies_not_eq t lt_x_y eq_x_y)
    isLT t x y | (XGT gt_x_y) = No (\lt_x_y => lt_implies_not_gt t lt_x_y gt_x_y)

-- Construct reverse total order
public export
totalOrderRev : TotalOrderImpl a -> TotalOrderImpl a
totalOrderRev t = TotalOrderImpl_mk
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
