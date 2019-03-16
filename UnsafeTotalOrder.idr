module UnsafeTotalOrder

import TotalOrder
import TotalOrderLite

%default total

data UnsafeLT : a -> a -> Type where
    UnsafeLT_mk : (x, y : a) -> UnsafeLT x y

data UnsafeEQ : a -> a -> Type where
    UnsafeEQ_mk : (x, y : a) -> UnsafeEQ x y

unsafe_cmp : Ord a => (x, y : a) -> OrderingX (UnsafeLT x y) (UnsafeEQ x y) (UnsafeLT y x)
unsafe_cmp x y with (compare x y)
    unsafe_cmp x y | LT = XLT $ UnsafeLT_mk x y
    unsafe_cmp x y | EQ = XEQ $ UnsafeEQ_mk x y
    unsafe_cmp x y | GT = XGT $ UnsafeLT_mk y x

unsafe_lt_trans : UnsafeLT x y -> UnsafeLT y z -> UnsafeLT x z
unsafe_lt_trans _ _ = UnsafeLT_mk _ _

unsafe_eq_trans : UnsafeEQ x y -> UnsafeEQ y z -> UnsafeEQ x z
unsafe_eq_trans _ _ = UnsafeEQ_mk _ _

unsafe_eq_symm : UnsafeEQ x y -> UnsafeEQ y x
unsafe_eq_symm _ = UnsafeEQ_mk _ _

unsafe_lt_implies_not_eq : UnsafeLT x y -> Not (UnsafeEQ x y)
unsafe_lt_implies_not_eq _ _ = void assert_unreachable

unsafe_lt_implies_not_gt : UnsafeLT x y -> Not (UnsafeLT y x)
unsafe_lt_implies_not_gt _ _ = void assert_unreachable

unsafe_eq_implies_not_lt : UnsafeEQ x y -> Not (UnsafeLT x y)
unsafe_eq_implies_not_lt _ _ = void assert_unreachable

unsafe_lt_eq_implies_lt : UnsafeLT x y -> UnsafeEQ y z -> UnsafeLT x z
unsafe_lt_eq_implies_lt _ _ = UnsafeLT_mk _ _

unsafe_eq_lt_implies_lt : UnsafeEQ x y -> UnsafeLT y z -> UnsafeLT x z
unsafe_eq_lt_implies_lt _ _ = UnsafeLT_mk _ _

export
unsafeTotalOrderForOrd : Ord a => TotalOrderImpl a
unsafeTotalOrderForOrd = TotalOrderImpl_mk
    UnsafeLT
    UnsafeEQ
    unsafe_cmp
    unsafe_lt_trans
    unsafe_eq_trans
    unsafe_eq_symm
    unsafe_lt_implies_not_eq
    unsafe_lt_implies_not_gt
    unsafe_eq_implies_not_lt
    unsafe_lt_eq_implies_lt
    unsafe_eq_lt_implies_lt

export
unsafeTotalOrderLiteForOrd : Ord a => TotalOrderLiteImpl a
unsafeTotalOrderLiteForOrd = totalOrderLiteFromFull unsafeTotalOrderForOrd

export
implementation TotalOrderLite String where
    totalOrderLite = unsafeTotalOrderLiteForOrd

export
implementation TotalOrderLite Int where
    totalOrderLite = unsafeTotalOrderLiteForOrd

export
implementation TotalOrderLite Integer where
    totalOrderLite = unsafeTotalOrderLiteForOrd
