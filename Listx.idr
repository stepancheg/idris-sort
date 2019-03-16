module Listx

import TotalOrder
import TotalOrderLite
import Natx

%default total
%access public export

-- TODO: temp
t : TotalOrder Nat
t = totalOrderNat

data LTEListNat : TotalOrder Nat -> (xs, ys : List Nat) -> Type where
    LTEListNatZero : {t : TotalOrder Nat} -> LTEListNat t [] right
    LTEListNatRec : {t : TotalOrder Nat} -> TotalOrder.eq t x y -> LTEListNat t xs ys -> LTEListNat t (x :: xs) (y :: ys)
    LTEListNatLT : {t : TotalOrder Nat} -> TotalOrder.lt t x y -> LTEListNat t (x :: xs) (y :: ys)

export
gtFirstNotLTE : TotalOrder.gt Listx.t x y -> Not (LTEListNat Listx.t (x :: xs) (y :: ys))
gtFirstNotLTE gt_x_y LTEListNatZero impossible
gtFirstNotLTE gt_x_y (LTEListNatLT lt_x_y) = lt_implies_not_gt t gt_x_y lt_x_y
gtFirstNotLTE gt_x_y (LTEListNatRec eq_x_y lte_xs_ys) = lt_implies_not_eq t gt_x_y (eq_symm t eq_x_y)

notGteNotEmptyEmpty : Not (LTEListNat Listx.t (x :: xs) [])
notGteNotEmptyEmpty LTEListNatZero impossible
notGteNotEmptyEmpty LTEListNatRec impossible
notGteNotEmptyEmpty LTEListNatLT impossible

fromLTERecEq : (x = y) -> (LTEListNat Listx.t (x :: xs) (y :: ys)) -> LTEListNat Listx.t xs ys
fromLTERecEq _ LTEListNatZero impossible
fromLTERecEq eq_x_y (LTEListNatLT lt_z_z) = absurd (nat_eq_implies_not_lt eq_x_y lt_z_z)
fromLTERecEq _ (LTEListNatRec _ l) = l

isLTEListNat : (xs, ys : List Nat) -> Dec (LTEListNat Listx.t xs ys)
isLTEListNat [] _ = Yes LTEListNatZero
isLTEListNat (x :: xs) [] = No notGteNotEmptyEmpty
isLTEListNat (x :: xs) (y :: ys) with (cmp t x y)
    isLTEListNat (x :: xs) (y :: ys) | (XLT lt) = Yes (LTEListNatLT lt)
    isLTEListNat (x :: xs) (y :: ys) | (XGT gt) = No (gtFirstNotLTE gt)
    isLTEListNat (x :: xs) (y :: ys) | (XEQ eq) = case isLTEListNat xs ys of
        Yes prf => Yes $ LTEListNatRec eq prf
        No contra => No $ contra . fromLTERecEq eq

lteEmptyImpliesEmpty : {t : TotalOrder Nat} -> LTEListNat t xs [] -> xs = []
lteEmptyImpliesEmpty LTEListNatZero = Refl
lteEmptyImpliesEmpty (LTEListNatRec eq_x_y xs_ys) impossible
lteEmptyImpliesEmpty (LTEListNatLT lt_x_y) impossible

private
lteListNatTransitiveHelp : xs = [] -> LTEListNat Listx.t xs []
lteListNatTransitiveHelp Refl = LTEListNatZero

private
lteListNatTransitive : LTEListNat Listx.t xs ys -> LTEListNat Listx.t ys zs -> LTEListNat Listx.t xs zs
lteListNatTransitive LTEListNatZero _ =
    LTEListNatZero
lteListNatTransitive {xs} {zs = []} lte_xs_ys LTEListNatZero =
    let refl : (xs = []) = lteEmptyImpliesEmpty lte_xs_ys in
    lteListNatTransitiveHelp refl
lteListNatTransitive (LTEListNatLT lt_x_y) (LTEListNatLT lt_y_z) =
    LTEListNatLT (lt_trans t lt_x_y lt_y_z)
lteListNatTransitive (LTEListNatRec eq_x_y xs_ys) (LTEListNatRec eq_y_z ys_zs) =
    LTEListNatRec (eq_trans _ eq_x_y eq_y_z) (lteListNatTransitive xs_ys ys_zs)
lteListNatTransitive (LTEListNatLT lt_x_y) (LTEListNatRec eq_y_z lte_ys_zs) =
    LTEListNatLT (lt_eq_implies_lt _ lt_x_y eq_y_z)
lteListNatTransitive (LTEListNatRec eq_x_y lte_xs_ys) (LTEListNatLT lt_y_z) =
    LTEListNatLT (eq_lt_implies_lt _ eq_x_y lt_y_z)
--lteListNatTransitive _ _ = ?help

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

private
unlength0 : Not (length (x :: xs) + length (y :: ys) = Z)
unlength0 Refl impossible

private
sumZeroImpliesLeftZero : a + b = Z -> a = Z
sumZeroImpliesLeftZero {a = Z} _ = Refl
sumZeroImpliesLeftZero {a = S x} rf = absurd rf

private
sumZeroImpliesRightZero : a + b = Z -> b = Z
sumZeroImpliesRightZero rf = sumZeroImpliesLeftZero $ flipPlus rf

private
unlength1 : Not (length (x :: xs) + length (y :: ys) = S Z)
unlength1 {xs} {ys} rr =
    let qq = the (S (length xs) + S (length ys) = S Z) rr in
    let qw = the ((length xs) + S (length ys) = Z) (succInjective _ _ qq) in
    absurd $ sumZeroImpliesRightZero qw

private
lteListNatAntisymmetricHelp : Not (LTEListNat Listx.t xs ys)
    -> {l : Nat}
    -> {auto ok : length xs + length ys = l}
    -> LTEListNat Listx.t ys xs
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

private
lteListNatAntisymmetric : Not (LTEListNat Listx.t xs ys) -> LTEListNat Listx.t ys xs
lteListNatAntisymmetric not_lte = lteListNatAntisymmetricHelp not_lte

export
totalOrderListLte : TotalOrderLite (List Nat)
totalOrderListLte =
    TotalOrderLite_mk (LTEListNat Listx.t) isLTEListNat lteListNatTransitive lteListNatAntisymmetric
