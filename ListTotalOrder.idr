-- Implementation of TotalOrderLite for List
module ListTotalOrder

import TotalOrder
import TotalOrderLite
import NatTotalOrder

%default total
%access export

data LTEList : TotalOrderImpl a -> (xs, ys : List a) -> Type where
    LTEListZero : {t : TotalOrderImpl a} -> LTEList t [] right
    LTEListRec : {t : TotalOrderImpl a} -> eq t x y -> LTEList t xs ys -> LTEList t (x :: xs) (y :: ys)
    LTEListLT : {t : TotalOrderImpl a} -> lt t x y -> LTEList t (x :: xs) (y :: ys)

export
gtFirstNotLTE : {t : TotalOrderImpl a} -> gt t x y -> Not (LTEList t (x :: xs) (y :: ys))
gtFirstNotLTE {t} gt_x_y LTEListZero impossible
gtFirstNotLTE {t} gt_x_y (LTEListLT lt_x_y) = lt_implies_not_gt t gt_x_y lt_x_y
gtFirstNotLTE {t} gt_x_y (LTEListRec eq_x_y lte_xs_ys) = lt_implies_not_eq t gt_x_y (eq_symm t eq_x_y)

private
notLteNotEmptyEmpty : {t : TotalOrderImpl a} -> Not (LTEList t (x :: xs) [])
notLteNotEmptyEmpty LTEListZero impossible
notLteNotEmptyEmpty LTEListRec impossible
notLteNotEmptyEmpty LTEListLT impossible

private
fromLTERecEq : {t : TotalOrderImpl a} -> eq t x y -> (LTEList t (x :: xs) (y :: ys)) -> LTEList t xs ys
fromLTERecEq _ LTEListZero impossible
fromLTERecEq {t} eq_x_y (LTEListLT lt_z_z) = absurd (eq_implies_not_lt t eq_x_y lt_z_z)
fromLTERecEq _ (LTEListRec _ l) = l

isLTEList : {t : TotalOrderImpl a} -> (xs, ys : List a) -> Dec (LTEList t xs ys)
isLTEList [] _ = Yes LTEListZero
isLTEList (x :: xs) [] = No notLteNotEmptyEmpty
isLTEList {t} (x :: xs) (y :: ys) with (cmp t x y)
    isLTEList {t} (x :: xs) (y :: ys) | (XLT lt) = Yes (LTEListLT lt)
    isLTEList {t} (x :: xs) (y :: ys) | (XGT gt) = No (gtFirstNotLTE gt)
    isLTEList {t} (x :: xs) (y :: ys) | (XEQ eq) = case isLTEList {t} xs ys of
        Yes prf => Yes $ LTEListRec {t} eq prf
        No contra => No $ contra . fromLTERecEq eq

lteEmptyImpliesEmpty : {t : TotalOrderImpl a} -> LTEList t xs [] -> xs = []
lteEmptyImpliesEmpty LTEListZero = Refl
lteEmptyImpliesEmpty (LTEListRec eq_x_y xs_ys) impossible
lteEmptyImpliesEmpty (LTEListLT lt_x_y) impossible

private
lteListNatTransitiveHelp : {t : TotalOrderImpl a} -> xs = [] -> LTEList t xs []
lteListNatTransitiveHelp Refl = LTEListZero

private
lteListNatTransitive : {t : TotalOrderImpl a} -> LTEList t xs ys -> LTEList t ys zs -> LTEList t xs zs
lteListNatTransitive LTEListZero _ =
    LTEListZero
lteListNatTransitive {xs} {zs = []} lte_xs_ys LTEListZero =
    let refl : (xs = []) = lteEmptyImpliesEmpty lte_xs_ys in
    lteListNatTransitiveHelp refl
lteListNatTransitive (LTEListLT lt_x_y) (LTEListLT lt_y_z) =
    LTEListLT (lt_trans t lt_x_y lt_y_z)
lteListNatTransitive (LTEListRec eq_x_y xs_ys) (LTEListRec eq_y_z ys_zs) =
    LTEListRec (eq_trans _ eq_x_y eq_y_z) (lteListNatTransitive xs_ys ys_zs)
lteListNatTransitive (LTEListLT lt_x_y) (LTEListRec eq_y_z lte_ys_zs) =
    LTEListLT (lt_eq_implies_lt _ lt_x_y eq_y_z)
lteListNatTransitive (LTEListRec eq_x_y lte_xs_ys) (LTEListLT lt_y_z) =
    LTEListLT (eq_lt_implies_lt _ eq_x_y lt_y_z)

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
lteListNatAntisymmetricHelp : {t : TotalOrderImpl a}
    -> Not (LTEList t xs ys)
    -> {l : Nat}
    -> {auto ok : length xs + length ys = l}
    -> LTEList t ys xs
lteListNatAntisymmetricHelp {ys = []} not_lte = LTEListZero
lteListNatAntisymmetricHelp {xs = []} not_lte = absurd $ not_lte LTEListZero
lteListNatAntisymmetricHelp {t} {xs = x :: xs} {ys = y :: ys} {l = S (S l)} {ok} not_lte with (cmp t x y)
    lteListNatAntisymmetricHelp {t} {xs = x :: xs} {ys = y :: ys}                    not_lte | (XLT lt_x_y) =
        absurd $ not_lte (LTEListLT lt_x_y)
    lteListNatAntisymmetricHelp {t} {xs = x :: xs} {ys = y :: ys}                    not_lte | (XGT gt_x_y) =
        LTEListLT gt_x_y
    lteListNatAntisymmetricHelp {t} {xs = x :: xs} {ys = y :: ys} {l = S (S l)} {ok} not_lte | (XEQ eq_x_y) = case isLTEList {t} ys xs of
        Yes prf => LTEListRec {t} (eq_symm t eq_x_y) prf
        No contra =>
            let xx = lteListNatAntisymmetricHelp {t} {l} {ok = unlength {x} {y} ok} contra in
            absurd $ not_lte (LTEListRec {t} eq_x_y xx)
lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} {l = Z} {ok} _ = absurd (unlength0 {x} {y} ok)
lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} {l = S Z} {ok} _ = absurd (unlength1 {x} {y} ok)

private
lteListNatAntisymmetric : {t : TotalOrderImpl a} -> Not (LTEList t xs ys) -> LTEList t ys xs
lteListNatAntisymmetric not_lte = lteListNatAntisymmetricHelp not_lte

export
totalOrderList : TotalOrderImpl a -> TotalOrderLiteImpl (List a)
totalOrderList t =
    TotalOrderLiteImpl_mk (LTEList t) isLTEList lteListNatTransitive lteListNatAntisymmetric

export
totalOrderListLte : TotalOrderLiteImpl (List Nat)
totalOrderListLte = totalOrderList totalOrderNat
