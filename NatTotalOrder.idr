-- Implementation of TotalOrder and TotalOrderLite for Nat
module NatTotalOrder

import TotalOrder
import TotalOrderLite

%default total

nat_cmp : (x, y : Nat) -> OrderingX (LT x y) (x = y) (LT y x)
nat_cmp Z Z = XEQ (the (Z = Z) Refl)
nat_cmp (S _) Z = XGT (LTESucc LTEZero)
nat_cmp Z (S _) = XLT (LTESucc LTEZero)
nat_cmp (S x) (S y) with (nat_cmp x y)
    nat_cmp (S x) (S y) | (XEQ x_eq_y) = XEQ (cong x_eq_y)
    nat_cmp (S x) (S y) | (XLT x_lt_y) = XLT (LTESucc x_lt_y)
    nat_cmp (S x) (S y) | (XGT x_gt_y) = XGT (LTESucc x_gt_y)

nat_lt_trans : LT x y -> LT y z -> LT x z
nat_lt_trans lt_x_y lt_y_z = lteTransitive (lteSuccRight lt_x_y) lt_y_z

nat_eq_trans : x = y -> y = z -> x = z
nat_eq_trans Refl Refl = Refl

nat_eq_symm : x = y -> y = x
nat_eq_symm Refl = Refl

nat_refl_pred : S x = S y -> x = y
nat_refl_pred Refl = Refl

nat_lt_implies_not_eq : LT x y -> Not (x = y)
nat_lt_implies_not_eq LTEZero _ impossible
nat_lt_implies_not_eq {x=Z} {y=Z} _ _ impossible
nat_lt_implies_not_eq {x=S _} {y=Z} _ _ impossible
nat_lt_implies_not_eq {x=Z} {y=S y} _ rf = absurd rf
nat_lt_implies_not_eq {x=S x} {y=S y} (LTESucc prev) rf = nat_lt_implies_not_eq prev (nat_refl_pred rf)

nat_lt_implies_not_gt : LT x y -> Not (LT y x)
nat_lt_implies_not_gt LTEZero _ impossible
nat_lt_implies_not_gt _ LTEZero impossible
nat_lt_implies_not_gt (LTESucc lt_x_y) (LTESucc lt_y_x) = nat_lt_implies_not_gt lt_x_y lt_y_x

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
totalOrderNat : TotalOrderImpl Nat
totalOrderNat =
    TotalOrderImpl_mk
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
totalOrderNat_rev : TotalOrderImpl Nat
totalOrderNat_rev = totalOrderRev totalOrderNat

export
totalOrderLiteNat : TotalOrderLiteImpl Nat
totalOrderLiteNat = totalOrderLiteFromFull totalOrderNat

export
totalOrderLiteNatRev : TotalOrderLiteImpl Nat
totalOrderLiteNatRev = totalOrderLiteFromFull totalOrderNat_rev

export
implementation TotalOrderLite Nat where
    totalOrderLite = totalOrderLiteNat
