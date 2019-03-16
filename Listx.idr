module Listx

import TotalOrder
import Natx

%default total

data NatCmp : Nat -> Nat -> Type where
    NatLt : LT a b -> NatCmp a b
    NatGt : GT a b -> NatCmp a b
    NatEq : NatCmp a a

natCmpSucc : NatCmp x y -> NatCmp (S x) (S y)
natCmpSucc (NatLt lt) = NatLt $ LTESucc lt
natCmpSucc (NatGt gt) = NatGt $ LTESucc gt
natCmpSucc NatEq = NatEq

natCmp : (a, b : Nat) -> NatCmp a b
natCmp Z Z = NatEq
natCmp (S a) (S b) = natCmpSucc (natCmp a b)
natCmp Z (S b) = NatLt $ LTESucc LTEZero
natCmp (S a) Z = NatGt $ LTESucc LTEZero

natCmpMirror : NatCmp a b -> NatCmp b a
natCmpMirror (NatLt lt) = NatGt lt
natCmpMirror (NatGt gt) = NatLt gt
natCmpMirror NatEq = NatEq

export
data LTEListNat : (xs, ys : List Nat) -> Type where
    LTEListNatZero : LTEListNat [] right
    LTEListNatRec : (z : Nat) -> LTEListNat xs ys -> LTEListNat (z :: xs) (z :: ys)
    LTEListNatLT : LT x y -> LTEListNat (x :: xs) (y :: ys)

notGtSelf : (x : Nat) -> Not (GT x x)
notGtSelf x = nat_eq_implies_not_lt Refl

notLtSelf : (x : Nat) -> Not (LT x x)
notLtSelf x = nat_eq_implies_not_lt Refl

gtFirstNotLTE : GT x y -> Not (LTEListNat (x :: xs) (y :: ys))
gtFirstNotLTE gt_x_y LTEListNatZero impossible
gtFirstNotLTE gt_x_y (LTEListNatLT lt_x_y) = nat_lt_implies_not_gt gt_x_y lt_x_y
gtFirstNotLTE gt_x_y (LTEListNatRec z lte_xs_ys) = notGtSelf z gt_x_y

lteListNatSucc : LTEListNat (x :: xs) (y :: ys) -> LTEListNat ((S x) :: xs) ((S y) :: ys)
lteListNatSucc LTEListNatZero impossible
lteListNatSucc (LTEListNatLT lt_x_y) = LTEListNatLT $ LTESucc lt_x_y
lteListNatSucc (LTEListNatRec z lte_xs_ys) = LTEListNatRec (S z) lte_xs_ys

Uninhabited (LTEListNat (x :: xs) []) where
    uninhabited LTEListNatZero impossible
    uninhabited LTEListNatRec impossible
    uninhabited LTEListNatLT impossible

fromLTERec : (LTEListNat (z :: xs) (z :: ys)) -> LTEListNat xs ys
fromLTERec LTEListNatZero impossible
fromLTERec (LTEListNatLT lt_z_z) = absurd (notLtSelf _ $ lt_z_z)
fromLTERec (LTEListNatRec z l) = l

fromLTESucc : (LTEListNat (S x :: xs) (S y :: ys)) -> LTEListNat (x :: xs) (y :: ys)
fromLTESucc LTEListNatZero impossible
fromLTESucc (LTEListNatLT lt_sx_sy) = LTEListNatLT $ fromLteSucc lt_sx_sy
fromLTESucc (LTEListNatRec (S z) lte) = LTEListNatRec z lte

export
data ListDec : List Nat -> Type where
    ListDecNil : ListDec []
    ListDecZ : ListDec xs -> ListDec (Z :: xs)
    ListDecS : (x : Nat) -> ListDec (x :: xs) -> ListDec (S x :: xs)

isLT : (m, n : Nat) -> Dec (LT m n)
isLT m n = isLTE (S m) n

listNatWeight : List Nat -> Nat
listNatWeight [] = Z
listNatWeight (x :: xs) = 1 + x + listNatWeight xs

listNatWeightUnS : listNatWeight (S x :: xs) = S w -> listNatWeight (x :: xs) = w
listNatWeightUnS = nat_refl_pred

listNatWeightUnZ : listNatWeight (Z :: xs) = S w -> listNatWeight xs = w
listNatWeightUnZ = nat_refl_pred

notEmptyListWeightNotZ : Not (listNatWeight (x :: xs) = Z)
notEmptyListWeightNotZ Refl impossible

listNatToListDec : (xs : List Nat) -> {w : Nat} -> {auto ok : listNatWeight xs = w} -> ListDec xs
listNatToListDec [] = ListDecNil
listNatToListDec {ok} {w = S w} (Z :: xs) = ListDecZ (listNatToListDec {w} {ok = listNatWeightUnZ ok} xs)
listNatToListDec {ok} {w = S w} (S x :: xs) = ListDecS x (listNatToListDec {w} {ok = listNatWeightUnS ok} (x :: xs))
listNatToListDec {ok} {w = Z} (x :: xs) = absurd $ notEmptyListWeightNotZ ok

export
isLTEListNat1 : (xs_list_dec : ListDec xs) -> (ys_list_dec : ListDec ys) -> Dec (LTEListNat xs ys)
isLTEListNat1 ListDecNil _ = Yes LTEListNatZero
isLTEListNat1 {xs = x :: xs} _ ListDecNil = No absurd
isLTEListNat1 (ListDecZ xs) (ListDecZ ys) with (isLTEListNat1 xs ys)
    isLTEListNat1 (ListDecZ xs) (ListDecZ ys) | (Yes prf) = Yes (LTEListNatRec Z prf)
    isLTEListNat1 (ListDecZ xs) (ListDecZ ys) | (No contra) = No (contra . fromLTERec)
isLTEListNat1 (ListDecS x xxs) (ListDecS y yys) with (isLTEListNat1 xxs yys)
    isLTEListNat1 (ListDecS x xxs) (ListDecS y yys) | (Yes prf) = Yes (lteListNatSucc prf)
    isLTEListNat1 (ListDecS x xxs) (ListDecS y yys) | (No contra) = No (contra . fromLTESucc)
isLTEListNat1 (ListDecZ xs) (ListDecS y ys) = Yes (LTEListNatLT $ LTESucc LTEZero)
isLTEListNat1 (ListDecS x xs) (ListDecZ ys) = No (gtFirstNotLTE $ LTESucc LTEZero)

export
isLTEListNat : (xs, ys : List Nat) -> Dec (LTEListNat xs ys)
isLTEListNat xs ys = isLTEListNat1 (listNatToListDec xs) (listNatToListDec ys)

lteEmptyImpliesEmpty : LTEListNat xs [] -> xs = []
lteEmptyImpliesEmpty LTEListNatZero = Refl
lteEmptyImpliesEmpty (LTEListNatRec z xs_ys) impossible
lteEmptyImpliesEmpty (LTEListNatLT x_y) impossible

lteListNatTransitive : LTEListNat xs ys -> LTEListNat ys zs -> LTEListNat xs zs
lteListNatTransitive LTEListNatZero _ = LTEListNatZero
lteListNatTransitive lte_xs_ys LTEListNatZero = rewrite (lteEmptyImpliesEmpty lte_xs_ys) in LTEListNatZero
lteListNatTransitive (LTEListNatLT lt_x_y) (LTEListNatLT lt_y_z) = LTEListNatLT (nat_lt_trans lt_x_y lt_y_z)
lteListNatTransitive (LTEListNatRec z xs_ys) (LTEListNatRec z ys_zs) =
    LTEListNatRec z (lteListNatTransitive xs_ys ys_zs)
lteListNatTransitive (LTEListNatLT lt_x_y) (LTEListNatRec w lte_ys_zs) = LTEListNatLT lt_x_y
lteListNatTransitive (LTEListNatRec w lte_xs_ys) (LTEListNatLT lt_y_z) = LTEListNatLT lt_y_z

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

lteListNatAntisymmetricHelp : Not (LTEListNat xs ys) -> {l : Nat} -> {auto ok : length xs + length ys = l} -> LTEListNat ys xs
lteListNatAntisymmetricHelp {ys = []} not_lte = LTEListNatZero
lteListNatAntisymmetricHelp {xs = []} not_lte = absurd $ not_lte LTEListNatZero
lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} {l = S (S l)} {ok} not_lte with (natCmp x y)
    lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} not_lte | (NatLt lt_x_y) =
        absurd $ not_lte (LTEListNatLT lt_x_y)
    lteListNatAntisymmetricHelp {xs = z :: xs} {ys = z :: ys} {l = S (S l)} {ok} not_lte | NatEq = case isLTEListNat ys xs of
        (Yes prf) => LTEListNatRec z prf
        (No contra) => let xx = lteListNatAntisymmetricHelp {l} {ok = unlength {x = z} {y = z} ok} contra in absurd $ not_lte (LTEListNatRec z xx)
    lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} not_lte | (NatGt gt_x_y) = LTEListNatLT gt_x_y
lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} {l = Z} {ok} _ = absurd (unlength0 {x} {y} ok)
lteListNatAntisymmetricHelp {xs = x :: xs} {ys = y :: ys} {l = S Z} {ok} _ = absurd (unlength1 {x} {y} ok)

export
lteListNatAntisymmetric : Not (LTEListNat xs ys) -> LTEListNat ys xs
lteListNatAntisymmetric not_lte = lteListNatAntisymmetricHelp not_lte

export
totalOrderListLte : TotalOrder (List Nat) LTEListNat
totalOrderListLte =
    TotalOrderInst (List Nat) LTEListNat isLTEListNat lteListNatTransitive lteListNatAntisymmetric
