module Listx

import TotalOrder
import TotalOrderLite
import Natx

%default total

-- TODO: temp
t : TotalOrder Nat
t = totalOrderNat

export
data LTEListNat : (xs, ys : List Nat) -> Type where
    LTEListNatZero : LTEListNat [] right
    LTEListNatRec : TotalOrder.eq Listx.t x y -> LTEListNat xs ys -> LTEListNat (x :: xs) (y :: ys)
    LTEListNatLT : TotalOrder.lt Listx.t x y -> LTEListNat (x :: xs) (y :: ys)

gtFirstNotLTE : TotalOrder.gt Listx.t x y -> Not (LTEListNat (x :: xs) (y :: ys))
gtFirstNotLTE gt_x_y LTEListNatZero impossible
gtFirstNotLTE gt_x_y (LTEListNatLT lt_x_y) = lt_implies_not_gt t gt_x_y lt_x_y
gtFirstNotLTE gt_x_y (LTEListNatRec eq_x_y lte_xs_ys) = lt_implies_not_eq t gt_x_y (eq_symm t eq_x_y)

Uninhabited (LTEListNat (x :: xs) []) where
    uninhabited LTEListNatZero impossible
    uninhabited LTEListNatRec impossible
    uninhabited LTEListNatLT impossible

fromLTERecEq : (x = y) -> (LTEListNat (x :: xs) (y :: ys)) -> LTEListNat xs ys
fromLTERecEq _ LTEListNatZero impossible
fromLTERecEq eq_x_y (LTEListNatLT lt_z_z) = absurd (nat_eq_implies_not_lt eq_x_y lt_z_z)
fromLTERecEq _ (LTEListNatRec _ l) = l

export
isLTEListNat : (xs, ys : List Nat) -> Dec (LTEListNat xs ys)
isLTEListNat [] _ = Yes LTEListNatZero
isLTEListNat (x :: xs) [] = No absurd
isLTEListNat (x :: xs) (y :: ys) with (cmp t x y)
    isLTEListNat (x :: xs) (y :: ys) | (XLT lt) = Yes (LTEListNatLT lt)
    isLTEListNat (x :: xs) (y :: ys) | (XGT gt) = No (gtFirstNotLTE gt)
    isLTEListNat (x :: xs) (y :: ys) | (XEQ eq) = case isLTEListNat xs ys of
        Yes prf => Yes $ LTEListNatRec eq prf
        No contra => No $ contra . fromLTERecEq eq

lteEmptyImpliesEmpty : LTEListNat xs [] -> xs = []
lteEmptyImpliesEmpty LTEListNatZero = Refl
lteEmptyImpliesEmpty (LTEListNatRec z xs_ys) impossible
lteEmptyImpliesEmpty (LTEListNatLT x_y) impossible

lteListNatTransitive : LTEListNat xs ys -> LTEListNat ys zs -> LTEListNat xs zs
lteListNatTransitive LTEListNatZero _ =
    LTEListNatZero
lteListNatTransitive lte_xs_ys LTEListNatZero =
    rewrite (lteEmptyImpliesEmpty lte_xs_ys) in LTEListNatZero
lteListNatTransitive (LTEListNatLT lt_x_y) (LTEListNatLT lt_y_z) =
    LTEListNatLT (lt_trans t lt_x_y lt_y_z)
lteListNatTransitive (LTEListNatRec eq_x_y xs_ys) (LTEListNatRec eq_y_z ys_zs) =
    LTEListNatRec (eq_trans _ eq_x_y eq_y_z) (lteListNatTransitive xs_ys ys_zs)
lteListNatTransitive (LTEListNatLT lt_x_y) (LTEListNatRec eq_y_z lte_ys_zs) =
    LTEListNatLT (lt_eq_implies_lt _ lt_x_y eq_y_z)
lteListNatTransitive (LTEListNatRec eq_x_y lte_xs_ys) (LTEListNatLT lt_y_z) =
    LTEListNatLT (eq_lt_implies_lt _ eq_x_y lt_y_z)

private
flipPlus : {a, b, c : Nat} -> a + b = c -> b + a = c
flipPlus {a} {b} Refl = rewrite (plusCommutative a b) in Refl

private
unnat : S x + S y = S (S z) -> x + y = z
unnat {x} {y} {z} rf =
    let xx = succInjective _ _ rf in
    let yy = flipPlus xx in
    let zz = succInjective _ _ yy in
    let ww = flipPlus zz in
    ww

private
unlength : length (x :: xs) + length (y :: ys) = S (S l) -> length ys + length xs = l
unlength {xs} {ys} rf =
    rewrite plusCommutative (length ys) (length xs) in unnat rf

unlength0 : Not (length (x :: xs) + length (y :: ys) = Z)
unlength0 Refl impossible

sumZeroImpliesLeftZero : a + b = Z -> a = Z
sumZeroImpliesLeftZero {a = Z} _ = Refl
sumZeroImpliesLeftZero {a = S x} rf = absurd rf

sumZeroImpliesRightZero : a + b = Z -> b = Z
sumZeroImpliesRightZero rf = sumZeroImpliesLeftZero $ flipPlus rf

unlength1 : Not (length (x :: xs) + length (y :: ys) = S Z)
unlength1 {xs} {ys} rr =
    let qq = the (S (length xs) + S (length ys) = S Z) rr in
    let qw = the ((length xs) + S (length ys) = Z) (succInjective _ _ qq) in
    absurd $ sumZeroImpliesRightZero qw

lteListNatAntisymmetricHelp : Not (LTEListNat xs ys)
    -> {l : Nat}
    -> {auto ok : length xs + length ys = l}
    -> LTEListNat ys xs
lteListNatAntisymmetricHelp {ys = []} not_lte = LTEListNatZero
lteListNatAntisymmetricHelp {xs = []} not_lte = absurd $ not_lte LTEListNatZero
lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} {l = S (S l)} {ok} not_lte with (cmp t x y)
    lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys}                    not_lte | (XLT lt_x_y) =
        absurd $ not_lte (LTEListNatLT lt_x_y)
    lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys}                    not_lte | (XGT gt_x_y) =
        LTEListNatLT gt_x_y
    lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} {l = S (S l)} {ok} not_lte | (XEQ eq_x_y) = case isLTEListNat ys xs of
        (Yes prf) => LTEListNatRec (eq_symm t eq_x_y) prf
        (No contra) => let xx = lteListNatAntisymmetricHelp {l} {ok = unlength {x} {y} ok} contra in absurd $ not_lte (LTEListNatRec eq_x_y xx)
lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} {l = Z} {ok} _ = absurd (unlength0 {x} {y} ok)
lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} {l = S Z} {ok} _ = absurd (unlength1 {x} {y} ok)

export
lteListNatAntisymmetric : Not (LTEListNat xs ys) -> LTEListNat ys xs
lteListNatAntisymmetric not_lte = lteListNatAntisymmetricHelp not_lte

export
totalOrderListLte : TotalOrderLite (List Nat)
totalOrderListLte =
    TotalOrderLite_mk LTEListNat isLTEListNat lteListNatTransitive lteListNatAntisymmetric
