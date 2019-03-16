-- Nat extensions
module Natx

import TotalOrder

%default total

public export
lteAntisymmetric : {a, b : Nat} -> Not (LTE a b) -> LTE b a
lteAntisymmetric {a = Z} notLTE = absurd (notLTE LTEZero)
lteAntisymmetric {a = S k} {b = Z} notLTE = LTEZero
lteAntisymmetric {a = S k} {b = S j} notLTE = LTESucc (lteAntisymmetric {a=k} {b=j} (notLTE . LTESucc))

public export
gteAntisymmetric : {a, b : Nat} -> Not (GTE a b) -> GTE b a
gteAntisymmetric {a} {b} notGTE = lteAntisymmetric {a=b} {b=a} notGTE

public export
isGTE : (m, n : Nat) -> Dec (GTE m n)
isGTE m n = isLTE n m

public export
gteTransitive : GTE n m -> GTE m p -> GTE n p
gteTransitive = flip lteTransitive

nat_cmp_type : Ordering -> Nat -> Nat -> Type
nat_cmp_type LT = Nat.LT
nat_cmp_type EQ = \x, y => x = y
nat_cmp_type GT = Nat.GT

nat_cmp : (x, y : Nat) -> OrderingX (LT x y) (x = y) (LT y x)
nat_cmp Z Z = XEQ (the (Z = Z) Refl)
nat_cmp (S _) Z = XGT (LTESucc LTEZero)
nat_cmp Z (S _) = XLT (LTESucc LTEZero)
nat_cmp (S x) (S y) with (nat_cmp x y)
    nat_cmp (S x) (S y) | (XEQ x_eq_y) = XEQ (cong x_eq_y)
    nat_cmp (S x) (S y) | (XLT x_lt_y) = XLT (LTESucc x_lt_y)
    nat_cmp (S x) (S y) | (XGT x_gt_y) = XGT (LTESucc x_gt_y)

export
nat_lt_trans : LT x y -> LT y z -> LT x z
nat_lt_trans lt_x_y lt_y_z = lteTransitive (lteSuccRight lt_x_y) lt_y_z

nat_eq_trans : x = y -> y = z -> x = z
nat_eq_trans Refl Refl = Refl

nat_eq_symm : x = y -> y = x
nat_eq_symm Refl = Refl

export
nat_refl_pred : S x = S y -> x = y
nat_refl_pred Refl = Refl

nat_lt_implies_not_eq : LT x y -> Not (x = y)
nat_lt_implies_not_eq LTEZero _ impossible
nat_lt_implies_not_eq {x=Z} {y=Z} _ _ impossible
nat_lt_implies_not_eq {x=S _} {y=Z} _ _ impossible
nat_lt_implies_not_eq {x=Z} {y=S y} _ rf = absurd rf
nat_lt_implies_not_eq {x=S x} {y=S y} (LTESucc prev) rf = nat_lt_implies_not_eq prev (nat_refl_pred rf)

export
nat_lt_implies_not_gt : LT x y -> Not (LT y x)
nat_lt_implies_not_gt LTEZero _ impossible
nat_lt_implies_not_gt _ LTEZero impossible
nat_lt_implies_not_gt (LTESucc lt_x_y) (LTESucc lt_y_x) = nat_lt_implies_not_gt lt_x_y lt_y_x

export
nat_eq_implies_not_lt : x = y -> Not (LT x y)
nat_eq_implies_not_lt _ LTEZero impossible
nat_eq_implies_not_lt {x = Z} {y = Z} _ _ impossible
nat_eq_implies_not_lt {x = Z} {y = S y} rf _ = absurd rf
nat_eq_implies_not_lt {x = S x} {y = Z} rf _ = absurd rf
nat_eq_implies_not_lt {x = S x} {y = S y} rf (LTESucc lt_x_y) =
    nat_eq_implies_not_lt (nat_refl_pred rf) lt_x_y

nat_lt_eq_implies_lt : LT x y -> y = z -> LT x z
nat_lt_eq_implies_lt lt_x_y Refl = lt_x_y

nat_eq_lt_implies_lt : x = y -> LT y z -> LT x z
nat_eq_lt_implies_lt Refl lt = lt

export
nat_cmp_types : CmpTypes Nat
nat_cmp_types =
    CmpTypes_mk
        LT
        (=)
        nat_cmp
        nat_lt_trans
        nat_eq_trans
        nat_eq_symm
        nat_lt_implies_not_eq
        nat_lt_implies_not_gt
        nat_eq_implies_not_lt
        nat_lt_eq_implies_lt
        nat_eq_lt_implies_lt

export
nat_cmp_types_rev : CmpTypes Nat
nat_cmp_types_rev = cmpTypes_rev nat_cmp_types

export
LTEX : Nat -> Nat -> Type
LTEX = CmpLTE Natx.nat_cmp_types

export
Rev_LTEX : Nat -> Nat -> Type
Rev_LTEX = CmpLTE Natx.nat_cmp_types_rev

export
LTX : Nat -> Nat -> Type
LTX = lt nat_cmp_types

export
totalOrderNat : TotalOrder Nat LTEX
totalOrderNat = totalOrderFromCmpTypes Natx.nat_cmp_types

export
totalOrderNatRev : TotalOrder Nat Rev_LTEX
totalOrderNatRev = totalOrderFromCmpTypes Natx.nat_cmp_types_rev
