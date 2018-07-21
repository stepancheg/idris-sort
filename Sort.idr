module Sort

import PermSimple
import Sorted
import LTEAll

%default total


sortedToLTEAll : Sorted (a :: rem) -> LTEAll a rem
sortedToLTEAll EmptySorted impossible
sortedToLTEAll {a} {rem = []} (OneSorted a) = LTEAllEmpty a
sortedToLTEAll {a} {rem = b :: brem} (RecSorted a b brem lteAB sortedBRem) =
    LTEAllRec a b lteAB (sortedToLTEAll (sortedReplaceFirstSmaller lteAB sortedBRem))

data SortedAlt : List Nat -> Type
    where
        EmptySortedAlt : SortedAlt []
        -- TODO: rem sorted
        RecSortedAlt : (a : Nat) -> (rem : List Nat) ->
            LTEAll a rem -> SortedAlt rem -> SortedAlt (a :: rem)

sortedToAlt : Sorted l -> SortedAlt l
sortedToAlt {l = []} EmptySorted = EmptySortedAlt
sortedToAlt {l = [a]} (OneSorted a) = RecSortedAlt a [] (LTEAllEmpty a) EmptySortedAlt
sortedToAlt {l = (a :: b :: rem)} s @ (RecSorted a b rem lteAB sortedBRem) =
    RecSortedAlt a (b :: rem) (sortedToLTEAll s) (sortedToAlt sortedBRem)

sortedAlt1 : (a : Nat) -> SortedAlt [a]
sortedAlt1 a = RecSortedAlt a [] (LTEAllEmpty a) EmptySortedAlt

notLTEImpliesRevLTE : Not (LTE a b) -> LTE b a
notLTEImpliesRevLTE {a = Z} notLTE = absurd (notLTE LTEZero)
notLTEImpliesRevLTE {a = S k} {b = Z} notLTE = LTEZero
notLTEImpliesRevLTE {a = S k} {b = S j} notLTE = LTESucc (notLTEImpliesRevLTE (notLTE . LTESucc))

removeMinElement : (xxs : List Nat) -> {auto ok : NonEmpty xxs} ->
    (x ** xs ** (PermSimple xxs (x :: xs), LTEAll x xs))
removeMinElement [a] = (a ** ([] ** (permSimpleFromRefl [a], LTEAllEmpty a)))
removeMinElement (a :: b :: rem) =
    let (bb ** (rrem ** (bbRremPerm, lteAllBbRrem))) = removeMinElement (b :: rem)
    in
    case isLTE a bb of
        Yes lteABb => (a ** ((bb :: rrem) ** (
            PermSimpleInsert {v = a} {xs = []} {ys = b :: rem} {zs = []} {ws = bb :: rrem} bbRremPerm,
            lteAllPrepend lteABb lteAllBbRrem
        )))
        No contra => (bb ** ((a :: rrem) ** (
            PermSimpleInsert {v = a} {xs = []} {ys = b :: rem} {zs = [bb]} {ws = rrem} bbRremPerm,
            lteAllConcat (lteAll1 (notLTEImpliesRevLTE contra)) lteAllBbRrem
        )))

sort1 : (i : List Nat) -> (l : Nat) -> {auto i_length_eq_l : (length i = l)} ->
    (o ** (Sorted o, PermSimple i o))
sort1 [] _ = ([] ** (EmptySorted, PermSimpleEmpty))
sort1 (a :: as) (S k) {i_length_eq_l} =
    let (v ** vs ** (perm_a_as_v_vs, v_lte_vs)) = removeMinElement (a :: as) in
    let length_v_vs_eq_l : (length (v :: vs) = S k) =
        trans (permSimpleLengthRefl $ permSimpleSym $ perm_a_as_v_vs) i_length_eq_l in
    let length_vs_eq_k : (length vs = k) = cong length_v_vs_eq_l {f = Nat.pred} in
    let (ws ** (ws_sorted, perm_vs_ws)) = sort1 vs k in
    let v_lte_ws = lteAllTrans v_lte_vs perm_vs_ws in
    let v_ws = v :: ws in
    let perm_v_vs_v_ws = permSimplePrepend {a = v} perm_vs_ws in
    let perm_a_as_v_ws = permSimpleTrans perm_a_as_v_vs perm_v_vs_v_ws in
    let v_ws_sorted = sortedPrepend v_lte_ws ws_sorted in
    (v_ws ** (v_ws_sorted, perm_a_as_v_ws))
sort1 (a :: as) Z {i_length_eq_l} = absurd i_length_eq_l

sort : (i : List Nat) -> (o : List Nat ** (Sorted o, PermSimple i o))
sort i = sort1 i _
