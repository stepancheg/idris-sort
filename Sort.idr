module Sort

import PermSimple
import Sorted
import SortedAlt
import Forall
import PermSimpleForall

%default total


notLTEImpliesRevLTE : Not (LTE a b) -> LTE b a
notLTEImpliesRevLTE {a = Z} notLTE = absurd (notLTE LTEZero)
notLTEImpliesRevLTE {a = S k} {b = Z} notLTE = LTEZero
notLTEImpliesRevLTE {a = S k} {b = S j} notLTE = LTESucc (notLTEImpliesRevLTE (notLTE . LTESucc))


lteAllSmaller : LTE a b -> Forall (LTE b) xs -> Forall (LTE a) xs
lteAllSmaller lte_a_b = forallMap (\x, lte_b_x => lteTransitive lte_a_b lte_b_x)

lteAllPrepend : LTE a b -> Forall (LTE b) xs -> Forall (LTE a) (b :: xs)
lteAllPrepend lte_a_b fa_lte_b_xs =
    forallConcat (forall1 lte_a_b) (lteAllSmaller lte_a_b fa_lte_b_xs)


-- Remove min element from a list
removeMinElement : (xxs : List Nat) -> {auto ok : NonEmpty xxs} ->
    (x ** xs ** (PermSimple xxs (x :: xs), Forall (LTE x) xs))
removeMinElement [a] = (a ** ([] ** (permSimpleFromRefl [a], ForallEmpty)))
removeMinElement (a :: b :: rem) =
    let (bb ** (rrem ** (bbRremPerm, lteAllBbRrem))) = removeMinElement (b :: rem)
    in
    case isLTE a bb of
        Yes lteABb => (a ** ((bb :: rrem) ** (
            PermSimpleIns {xs = []} {ys = b :: rem} {zs = []} {ws = bb :: rrem} bbRremPerm a,
            lteAllPrepend lteABb lteAllBbRrem
        )))
        No contra => (bb ** ((a :: rrem) ** (
            PermSimpleIns {xs = []} {ys = b :: rem} {zs = [bb]} {ws = rrem} bbRremPerm a,
            forallConcat (forall1 (notLTEImpliesRevLTE contra)) lteAllBbRrem
        )))

-- Helper function for sort implementation
-- `l` parameter exists only to prove totality
sort1 : (i : List Nat) -> (l : Nat) -> {auto i_length_eq_l : (length i = l)} ->
    (o ** (Sorted LTE o, PermSimple i o))
sort1 [] _ = ([] ** (SortedEmpty, PermSimpleEmpty))
sort1 (a :: as) (S k) {i_length_eq_l} =
    let (v ** vs ** (perm_a_as_v_vs, v_lte_vs)) = removeMinElement (a :: as) in
    let length_v_vs_eq_l : (length (v :: vs) = S k) =
        trans (permSimpleLengthRefl $ permSimpleSym $ perm_a_as_v_vs) i_length_eq_l in
    let length_vs_eq_k : (length vs = k) = cong length_v_vs_eq_l {f = Nat.pred} in
    let (ws ** (ws_sorted, perm_vs_ws)) = sort1 vs k in
    let v_lte_ws = forallPermSimple v_lte_vs perm_vs_ws in
    let v_ws = v :: ws in
    let perm_v_vs_v_ws = permSimplePrepend v perm_vs_ws in
    let perm_a_as_v_ws = permSimpleTrans perm_a_as_v_vs perm_v_vs_v_ws in
    let v_ws_sorted = sortedPrepend lteTransitive v_lte_ws ws_sorted in
    (v_ws ** (v_ws_sorted, perm_a_as_v_ws))
sort1 (a :: as) Z {i_length_eq_l} = absurd i_length_eq_l

export
sort : (i : List Nat) -> (o : List Nat ** (Sorted LTE o, PermSimple i o))
sort i = sort1 i _
