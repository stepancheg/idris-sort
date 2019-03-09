module Sort

import PermSimple
import Sorted
import SortedAlt
import Forall
import PermSimpleForall
import Natx
import TotalOrder

%default total


lteAllSmaller : {lte : a -> a -> Type}
    -> {lteTransitive : {x, y, z : a} -> lte x y -> lte y z -> lte x z}
    -> lte x y
    -> Forall (lte y) zs
    -> Forall (lte x) zs
lteAllSmaller {lteTransitive} lte_x_y = forallMap (\p, lte_y_p => lteTransitive lte_x_y lte_y_p)

lteAllPrepend : {lte : a -> a -> Type}
    -> {lteTransitive : {x, y, z : a} -> lte x y -> lte y z -> lte x z}
    -> lte x y
    -> Forall (lte y) zs
    -> Forall (lte x) (y :: zs)
lteAllPrepend {lteTransitive} lte_x_y fa_lte_y_zs =
    forallConcat (forall1 lte_x_y) (lteAllSmaller {lteTransitive} lte_x_y fa_lte_y_zs)

totalOrderUnpack : {lte : a -> a -> Type}
    -> TotalOrder a lte
    -> (
        ((x, y : a) -> Dec (lte x y)),
        ({x, y, z : a} -> lte x y -> lte y z -> lte x z),
        ({x, y : a} -> Not (lte x y) -> lte y x)
    )
totalOrderUnpack (TotalOrderInst _ _ isLTE lteTransitive lteAntisymmetric) =
    (isLTE, lteTransitive, lteAntisymmetric)

-- Remove min element from a list
removeMinElement : {lte : a -> a -> Type}
    -> TotalOrder a lte
    -> (xxs : List a)
    -> {auto ok : NonEmpty xxs}
    -> (x ** xs ** (PermSimple xxs (x :: xs), Forall (lte x) xs))
removeMinElement _ [x] = (x ** ([] ** (permSimpleFromRefl [x], ForallEmpty)))
removeMinElement to (x :: y :: rem) =
    let (isLTE, lteTransitive, lteAntisymmetric) = totalOrderUnpack to in
    let (yy ** (rrem ** (yy_rrem_perm, lteAll_yy_rrem))) = removeMinElement to (y :: rem) in
    case isLTE x yy of
        Yes lteXYy => (x ** ((yy :: rrem) ** (
            PermSimpleIns {xs = []} {ys = y :: rem} {zs = []} {ws = yy :: rrem} yy_rrem_perm x,
            lteAllPrepend {lteTransitive} lteXYy lteAll_yy_rrem
        )))
        No contra => (yy ** ((x :: rrem) ** (
            PermSimpleIns {xs = []} {ys = y :: rem} {zs = [yy]} {ws = rrem} yy_rrem_perm x,
            forallConcat (forall1 (lteAntisymmetric contra)) lteAll_yy_rrem
        )))

-- Helper function for sort implementation
sort1 : {lte: a -> a -> Type}
    -> TotalOrder a lte
    -> (i : List a)
    -> (l : Nat) -- parameter is only to prove totality
    -> {auto i_length_eq_l : (length i = l)}
    -> (o ** (Sorted lte o, PermSimple i o))
sort1 _ [] _ = ([] ** (SortedEmpty, PermSimpleEmpty))
sort1 {lte} to (x :: xs) (S k) {i_length_eq_l} =
    let (isLTE, lteTransitive, lteAntisymmetric) = totalOrderUnpack to in
    let (v ** vs ** (perm_x_xs_v_vs, v_lte_vs)) = removeMinElement to (x :: xs) in
    let length_v_vs_eq_l : (length (v :: vs) = S k) =
        trans (permSimpleLengthRefl $ permSimpleSym $ perm_x_xs_v_vs) i_length_eq_l in
    let length_vs_eq_k : (length vs = k) = cong length_v_vs_eq_l {f = Nat.pred} in
    let (ws ** (ws_sorted, perm_vs_ws)) = sort1 to vs k in
    let v_lte_ws = forallPermSimple v_lte_vs perm_vs_ws in
    let v_ws = v :: ws in
    let perm_v_vs_v_ws = permSimplePrepend v perm_vs_ws in
    let perm_x_xs_v_ws = permSimpleTrans perm_x_xs_v_vs perm_v_vs_v_ws in
    let v_ws_sorted = sortedPrepend lteTransitive v_lte_ws ws_sorted in
    (v_ws ** (v_ws_sorted, perm_x_xs_v_ws))
sort1 _ (_ :: _) Z {i_length_eq_l} = absurd i_length_eq_l

-- sort implementation
export
sort : {to : TotalOrder a lte} -> (i : List a) -> (o : List a ** (Sorted lte o, PermSimple i o))
sort {to} i = sort1 to i _

-- demo shortcut
export
sortNat : (i : List Nat) -> (o : List Nat ** (Sorted LTE o, PermSimple i o))
sortNat = sort {to = TotalOrderNat}

-- another demo shortcut
export
sortNatRev : (i : List Nat) -> (o : List Nat ** (Sorted GTE o, PermSimple i o))
sortNatRev = sort {to = TotalOrderNatRev}
