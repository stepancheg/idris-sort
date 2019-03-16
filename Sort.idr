module Sort

import PermSimple
import Sorted
import SortedAlt
import Forall
import PermSimpleForall
import TotalOrderLite

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

-- Remove min element from a list
removeMinElement :
    (t : TotalOrderLiteImpl a)
    -> (xxs : List a)
    -> {auto ok : NonEmpty xxs}
    -> (x ** xs ** (PermSimple xxs (x :: xs), Forall (lte t x) xs))
removeMinElement _ [x] = (x ** ([] ** (permSimpleFromRefl [x], ForallEmpty)))
removeMinElement t (x :: y :: rem) =
    let (yy ** (rrem ** (yy_rrem_perm, lteAll_yy_rrem))) = removeMinElement t (y :: rem) in
    case isLTE t x yy of
        Yes lteXYy => (x ** ((yy :: rrem) ** (
            PermSimpleIns {xs = []} {ys = y :: rem} {zs = []} {ws = yy :: rrem} yy_rrem_perm x,
            lteAllPrepend {lteTransitive = lte_trans t} lteXYy lteAll_yy_rrem
        )))
        No contra => (yy ** ((x :: rrem) ** (
            PermSimpleIns {xs = []} {ys = y :: rem} {zs = [yy]} {ws = rrem} yy_rrem_perm x,
            forallConcat (forall1 ((not_lte_implies_gte t) contra)) lteAll_yy_rrem
        )))

-- Helper function for sort implementation
sort1 :
    (t : TotalOrderLiteImpl a)
    -> (i : List a)
    -> (l : Nat) -- parameter is only to prove totality
    -> {auto i_length_eq_l : (length i = l)}
    -> (o ** (Sorted (lte t) o, PermSimple i o))
sort1 _ [] _ = ([] ** (SortedEmpty, PermSimpleEmpty))
sort1 t (x :: xs) (S k) {i_length_eq_l} =
    let (v ** vs ** (perm_x_xs_v_vs, v_lte_vs)) = removeMinElement t (x :: xs) in
    let length_v_vs_eq_l : (length (v :: vs) = S k) =
        trans (permSimpleLengthRefl $ permSimpleSym $ perm_x_xs_v_vs) i_length_eq_l in
    let length_vs_eq_k : (length vs = k) = cong length_v_vs_eq_l {f = Nat.pred} in
    let (ws ** (ws_sorted, perm_vs_ws)) = sort1 t vs k in
    let v_lte_ws = forallPermSimple v_lte_vs perm_vs_ws in
    let v_ws = v :: ws in
    let perm_v_vs_v_ws = permSimplePrepend v perm_vs_ws in
    let perm_x_xs_v_ws = permSimpleTrans perm_x_xs_v_vs perm_v_vs_v_ws in
    let v_ws_sorted = sortedPrepend (lte_trans t) v_lte_ws ws_sorted in
    (v_ws ** (v_ws_sorted, perm_x_xs_v_ws))
sort1 _ (_ :: _) Z {i_length_eq_l} = absurd i_length_eq_l

-- sort implementation
export
sortByFull : {t : TotalOrderLiteImpl a} -> (i : List a) -> (o : List a ** (Sorted (lte t) o, PermSimple i o))
sortByFull {t} i = sort1 t i _

export
sortBy : {t : TotalOrderLiteImpl a} -> List a -> List a
sortBy {t} i = fst (sortByFull {t} i)

export
sortFull : TotalOrderLite a =>
    (i : List a)
    -> (o : List a ** (Sorted (lte TotalOrderLite.totalOrderLite) o, PermSimple i o))
sortFull = Sort.sortByFull {t = totalOrderLite}

export
sort : TotalOrderLite a => List a -> List a
sort i = fst (sortFull i)
