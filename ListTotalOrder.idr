-- Implementation of TotalOrderLite for List
module ListTotalOrder

import TotalOrder
import TotalOrderLite
import NatTotalOrder

%default total
%access export

data ListEq : TotalOrderImpl a -> (xs, ys : List a) -> Type where
    ListEqEmpty : ListEq t [] []
    ListEqRec : eq t x y -> ListEq t xs ys -> ListEq t (x :: xs) (y :: ys)

data ListLt : TotalOrderImpl a -> (xs, ys : List a) -> Type where
    ListLtEmpty : ListLt t [] (y :: ys)
    ListLtFirst : lt t x y -> ListLt t (x :: xs) (y :: ys)
    ListLtRec : eq t x y -> ListLt t xs ys -> ListLt t (x :: xs) (y :: ys)

list_lt_trans : {t : TotalOrderImpl a} -> ListLt t xs ys -> ListLt t ys zs -> ListLt t xs zs
list_lt_trans {zs = z :: zs} ListLtEmpty lt_ys_zs = ListLtEmpty
list_lt_trans lt_xs_ys ListLtEmpty impossible
list_lt_trans (ListLtFirst lt_x_y) (ListLtFirst lt_y_z) =
    ListLtFirst (lt_trans _ lt_x_y lt_y_z)
list_lt_trans (ListLtFirst lt_x_y) (ListLtRec eq_y_z lt_ys_zs) =
    ListLtFirst (lt_eq_implies_lt _ lt_x_y eq_y_z)
list_lt_trans (ListLtRec eq_x_y lt_xs_ys) (ListLtFirst lt_y_z) =
    ListLtFirst (eq_lt_implies_lt _ eq_x_y lt_y_z)
list_lt_trans (ListLtRec eq_x_y lt_xs_ys) (ListLtRec eq_y_z lt_ys_zs) =
    ListLtRec (eq_trans _ eq_x_y eq_y_z) (list_lt_trans lt_xs_ys lt_ys_zs)

list_eq_trans : {t : TotalOrderImpl a} -> ListEq t xs ys -> ListEq t ys zs -> ListEq t xs zs
list_eq_trans ListEqEmpty eq_ys_zs = eq_ys_zs
list_eq_trans eq_xs_ys ListEqEmpty = eq_xs_ys
list_eq_trans (ListEqRec eq_x_y eq_xs_ys) (ListEqRec eq_y_z eq_ys_zs) =
    ListEqRec (eq_trans _ eq_x_y eq_y_z) (list_eq_trans eq_xs_ys eq_ys_zs)

list_eq_symm : {t : TotalOrderImpl a} -> ListEq t xs ys -> ListEq t ys xs
list_eq_symm ListEqEmpty = ListEqEmpty
list_eq_symm (ListEqRec eq_x_y eq_xs_ys) = ListEqRec (eq_symm t eq_x_y) (list_eq_symm eq_xs_ys)

list_lt_implies_not_eq : {t : TotalOrderImpl a} -> ListLt t xs ys -> Not (ListEq t xs ys)
list_lt_implies_not_eq ListLtEmpty _ impossible
list_lt_implies_not_eq _ ListEqEmpty impossible
list_lt_implies_not_eq (ListLtFirst lt_x_y) (ListEqRec eq_x_y _) =
    lt_implies_not_eq t lt_x_y eq_x_y
list_lt_implies_not_eq (ListLtRec _ lt_xs_ys) (ListEqRec _ eq_xs_ys) =
    list_lt_implies_not_eq lt_xs_ys eq_xs_ys

list_lt_implies_not_gt : {t : TotalOrderImpl a} -> ListLt t xs ys -> Not (ListLt t ys xs)
list_lt_implies_not_gt ListLtEmpty _ impossible
list_lt_implies_not_gt _ ListLtEmpty impossible
list_lt_implies_not_gt (ListLtFirst lt_x_y) (ListLtFirst lt_y_x) =
    lt_implies_not_gt _ lt_x_y lt_y_x
list_lt_implies_not_gt (ListLtFirst lt_x_y) (ListLtRec eq_y_x _) =
    lt_implies_not_eq _ lt_x_y (eq_symm _ eq_y_x)
list_lt_implies_not_gt (ListLtRec eq_x_y _) (ListLtFirst lt_y_x) =
    lt_implies_not_eq _ lt_y_x (eq_symm _ eq_x_y)
list_lt_implies_not_gt (ListLtRec eq_x_y lt_xs_ys) (ListLtRec eq_y_x lt_ys_xs) =
    list_lt_implies_not_gt lt_xs_ys lt_ys_xs

list_eq_implies_not_lt : {t : TotalOrderImpl a} -> ListEq t xs ys -> Not (ListLt t xs ys)
list_eq_implies_not_lt ListEqEmpty _ impossible
list_eq_implies_not_lt _ ListLtEmpty impossible
list_eq_implies_not_lt (ListEqRec eq_x_y eq_xs_ys) (ListLtFirst lt_x_y) =
    eq_implies_not_lt _ eq_x_y lt_x_y
list_eq_implies_not_lt (ListEqRec _ eq_xs_ys) (ListLtRec _ lt_xs_ys) =
    list_eq_implies_not_lt eq_xs_ys lt_xs_ys

list_lt_eq_implies_lt : {t : TotalOrderImpl a} -> ListLt t xs ys -> ListEq t ys zs -> ListLt t xs zs
list_lt_eq_implies_lt {zs = z :: zs} ListLtEmpty eq_xs_ys = ListLtEmpty
list_lt_eq_implies_lt lt_xs_ys ListEqEmpty impossible
list_lt_eq_implies_lt (ListLtFirst lt_x_y) (ListEqRec eq_y_z eq_ys_zs) =
    ListLtFirst (lt_eq_implies_lt _ lt_x_y eq_y_z)
list_lt_eq_implies_lt (ListLtRec eq_x_y lt_xs_ys) (ListEqRec eq_y_z eq_ys_zs) =
    ListLtRec (eq_trans _ eq_x_y eq_y_z) (list_lt_eq_implies_lt lt_xs_ys eq_ys_zs)

list_eq_lt_implies_lt : {t : TotalOrderImpl a} -> ListEq t xs ys -> ListLt t ys zs -> ListLt t xs zs
list_eq_lt_implies_lt ListEqEmpty lt_ys_zs = lt_ys_zs
list_eq_lt_implies_lt (ListEqRec eq_x_y eq_xs_ys) ListLtEmpty impossible
list_eq_lt_implies_lt (ListEqRec eq_x_y eq_xs_ys) (ListLtFirst lt_y_z) =
    ListLtFirst (eq_lt_implies_lt _ eq_x_y lt_y_z)
list_eq_lt_implies_lt (ListEqRec eq_x_y eq_xs_ys) (ListLtRec eq_y_z lt_ys_zs) =
    ListLtRec (eq_trans _ eq_x_y eq_y_z) (list_eq_lt_implies_lt eq_xs_ys lt_ys_zs)

list_cmp : {t : TotalOrderImpl a}
    -> (xs, ys : List a)
    -> OrderingX (ListLt t xs ys) (ListEq t xs ys) (ListLt t ys xs)
list_cmp [] [] = XEQ ListEqEmpty
list_cmp (x :: xs) [] = XGT ListLtEmpty
list_cmp [] (y :: ys) = XLT ListLtEmpty
list_cmp {t} (x :: xs) (y :: ys) with (cmp t x y)
    list_cmp (x :: xs) (y :: ys) | (XLT lt_x_y) = XLT $ ListLtFirst lt_x_y
    list_cmp (x :: xs) (y :: ys) | (XGT gt_x_y) = XGT $ ListLtFirst gt_x_y
    list_cmp {t} (x :: xs) (y :: ys) | (XEQ eq_x_y) = case list_cmp {t} xs ys of
        XLT lt_xs_ys => XLT $ ListLtRec eq_x_y lt_xs_ys
        XEQ eq_xs_ys => XEQ $ ListEqRec eq_x_y eq_xs_ys
        XGT gt_xs_ys => XGT $ ListLtRec (eq_symm t eq_x_y) gt_xs_ys

export
totalOrderFullList : TotalOrderImpl a -> TotalOrderImpl (List a)
totalOrderFullList t =
    TotalOrderImpl_mk
        (ListLt t)
        (ListEq t)
        list_cmp
        list_lt_trans
        list_eq_trans
        list_eq_symm
        list_lt_implies_not_eq
        list_lt_implies_not_gt
        list_eq_implies_not_lt
        list_lt_eq_implies_lt
        list_eq_lt_implies_lt

export
totalOrderList : TotalOrderImpl a -> TotalOrderLiteImpl (List a)
totalOrderList = totalOrderLiteFromFull . totalOrderFullList

export
totalOrderListLte : TotalOrderLiteImpl (List Nat)
totalOrderListLte = totalOrderList totalOrderNat
