module Sort

import PermSimple
import Sorted
import SortedAlt
import Forall
import PermSimpleForall
import Natx
import TotalOrder

%default total


lteAllSmaller : {lte : Nat -> Nat -> Type}
    -> {lteTransitive : {x, y, z : Nat} -> lte x y -> lte y z -> lte x z}
    -> lte a b
    -> Forall (lte b) xs
    -> Forall (lte a) xs
lteAllSmaller {lteTransitive} lte_a_b = forallMap (\x, lte_b_x => lteTransitive lte_a_b lte_b_x)

lteAllPrepend : {lte : Nat -> Nat -> Type}
    -> {lteTransitive : {x, y, z : Nat} -> lte x y -> lte y z -> lte x z}
    -> lte a b
    -> Forall (lte b) xs
    -> Forall (lte a) (b :: xs)
lteAllPrepend {lteTransitive} lte_a_b fa_lte_b_xs =
    forallConcat (forall1 lte_a_b) (lteAllSmaller {lteTransitive} lte_a_b fa_lte_b_xs)

totalOrderUnpack : {lte : Nat -> Nat -> Type}
    -> TotalOrder Nat lte
    -> (
        ((x, y : Nat) -> Dec (lte x y)),
        ({x, y, z : Nat} -> lte x y -> lte y z -> lte x z),
        ({x, y : Nat} -> Not (lte x y) -> lte y x)
    )
totalOrderUnpack (TotalOrderInst _ _ isLTE lteTransitive lteAntisymmetric) =
    (isLTE, lteTransitive, lteAntisymmetric)

-- Remove min element from a list
removeMinElement : {lte : Nat -> Nat -> Type}
    -> TotalOrder Nat lte
    -> (xxs : List Nat)
    -> {auto ok : NonEmpty xxs}
    -> (x ** xs ** (PermSimple xxs (x :: xs), Forall (lte x) xs))
removeMinElement _ [a] = (a ** ([] ** (permSimpleFromRefl [a], ForallEmpty)))
removeMinElement to (a :: b :: rem) =
    let (isLTE, lteTransitive, lteAntisymmetric) = totalOrderUnpack to in
    let (bb ** (rrem ** (bbRremPerm, lteAllBbRrem))) = removeMinElement to (b :: rem) in
    case isLTE a bb of
        Yes lteABb => (a ** ((bb :: rrem) ** (
            PermSimpleIns {xs = []} {ys = b :: rem} {zs = []} {ws = bb :: rrem} bbRremPerm a,
            lteAllPrepend {lteTransitive} lteABb lteAllBbRrem
        )))
        No contra => (bb ** ((a :: rrem) ** (
            PermSimpleIns {xs = []} {ys = b :: rem} {zs = [bb]} {ws = rrem} bbRremPerm a,
            forallConcat (forall1 (lteAntisymmetric contra)) lteAllBbRrem
        )))

-- Helper function for sort implementation
-- `l` parameter exists only to prove totality
sort1 : {lte: Nat -> Nat -> Type}
    -> TotalOrder Nat lte
    -> (i : List Nat)
    -> (l : Nat)
    -> {auto i_length_eq_l : (length i = l)}
    -> (o ** (Sorted lte o, PermSimple i o))
sort1 _ [] _ = ([] ** (SortedEmpty, PermSimpleEmpty))
sort1 {lte} to (a :: as) (S k) {i_length_eq_l} =
    let (isLTE, lteTransitive, lteAntisymmetric) = totalOrderUnpack to in
    let (v ** vs ** (perm_a_as_v_vs, v_lte_vs)) = removeMinElement to (a :: as) in
    let length_v_vs_eq_l : (length (v :: vs) = S k) =
        trans (permSimpleLengthRefl $ permSimpleSym $ perm_a_as_v_vs) i_length_eq_l in
    let length_vs_eq_k : (length vs = k) = cong length_v_vs_eq_l {f = Nat.pred} in
    let (ws ** (ws_sorted, perm_vs_ws)) = sort1 to vs k in
    let v_lte_ws = forallPermSimple v_lte_vs perm_vs_ws in
    let v_ws = v :: ws in
    let perm_v_vs_v_ws = permSimplePrepend v perm_vs_ws in
    let perm_a_as_v_ws = permSimpleTrans perm_a_as_v_vs perm_v_vs_v_ws in
    let v_ws_sorted = sortedPrepend lteTransitive v_lte_ws ws_sorted in
    (v_ws ** (v_ws_sorted, perm_a_as_v_ws))
sort1 _ (a :: as) Z {i_length_eq_l} = absurd i_length_eq_l

-- sort implementation
export
sort : {to : TotalOrder Nat lte} -> (i : List Nat) -> (o : List Nat ** (Sorted lte o, PermSimple i o))
sort {to} i = sort1 to i _

-- demo shortcut
export
sortNat : (i : List Nat) -> (o : List Nat ** (Sorted LTE o, PermSimple i o))
sortNat = sort {to = TotalOrderNat}

-- another demo shortcut
export
sortNatRev : (i : List Nat) -> (o : List Nat ** (Sorted GTE o, PermSimple i o))
sortNatRev = sort {to = TotalOrderNatRev}
