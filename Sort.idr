module Sort

import PermSimple

%default total

-- Definition of what it means for List to be sorted
data Sorted : List Nat -> Type
    where
        -- empty list is always sorted
        EmptySorted : Sorted []
        -- list of one element is always sorted
        OneSorted : (a : Nat) -> Sorted [a]
        -- list of two or more element is sorted iff both are true
        -- * first is less or equal than second
        -- * tail is sorted
        RecSorted : (a : Nat) -> (b : Nat) -> (rem : List Nat)
            -> LTE a b -> Sorted (b :: rem) -> Sorted (a :: b :: rem)

sortedReplaceFirstSmaller : LTE a b -> Sorted (b :: rem) -> Sorted (a :: rem)
sortedReplaceFirstSmaller _ EmptySorted impossible
sortedReplaceFirstSmaller {a} {b} _ (OneSorted b) = OneSorted a
sortedReplaceFirstSmaller {a} {b} lteAB (RecSorted b c rem lteBC sortedCRem) =
    RecSorted a c rem (lteTransitive lteAB lteBC) sortedCRem


-- Element is less or equal than all elements of the list
data LTEAll : Nat -> List Nat -> Type
    where
        LTEAllEmpty : (v : Nat) -> LTEAll v []
        LTEAllRec : (v : Nat) -> (a : Nat) -> LTE v a -> LTEAll v rem -> LTEAll v (a :: rem)

lteAll1 : LTE v x -> LTEAll v [x]
lteAll1 {v} {x} lteVX = LTEAllRec v x lteVX (LTEAllEmpty v)

lteAllConcat : LTEAll v xs -> LTEAll v ys -> LTEAll v (xs ++ ys)
lteAllConcat {v} {xs = []}      {ys = []} (LTEAllEmpty v) (LTEAllEmpty v) = LTEAllEmpty v
lteAllConcat {v} {xs = []}                _ lteAllYs = lteAllYs
lteAllConcat {v} {xs = x :: xs} {ys = []} lteAllXs _ = rewrite appendNilRightNeutral xs in lteAllXs
lteAllConcat {v} {xs = x :: xs} {ys}      (LTEAllRec v  x lteVX lteAllVXs) lteAllVYs =
    LTEAllRec v x lteVX (lteAllConcat lteAllVXs lteAllVYs)

lteAllSmaller : LTE a b -> LTEAll b l -> LTEAll a l
lteAllSmaller {a} {b} {l = []} lteAB (LTEAllEmpty b) = LTEAllEmpty a
lteAllSmaller {a} {b} {l = c :: rem} lteAB (LTEAllRec b c lteBC lteAllBRem) =
    LTEAllRec a c (lteTransitive lteAB lteBC) (lteAllSmaller lteAB lteAllBRem)

lteAllPrepend : LTE a b -> LTEAll b l -> LTEAll a (b :: l)
lteAllPrepend {a} {b} {l} lteAB lteAllBL =
    lteAllConcat (lteAll1 lteAB) (lteAllSmaller lteAB lteAllBL)

lteAllTrans : LTEAll a xs -> PermSimple xs ys -> LTEAll a ys

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

-- Proof that list is not sorted if first element is greater than second
notSortedE1E2 : Not (LTE a b) -> Sorted (a :: b :: rem) -> Void
notSortedE1E2 _ EmptySorted impossible
notSortedE1E2 _ (OneSorted _) impossible
notSortedE1E2 {a} {b} {rem} notLTE (RecSorted a b rem lte _) = notLTE lte

-- Proof that list is not sorted if tail is not sorted
notSortedBRem : Not (Sorted (b :: rem)) -> Sorted (a :: b :: rem) -> Void
notSortedBRem _ EmptySorted impossible
notSortedBRem _ (OneSorted _) impossible
notSortedBRem notSorted (RecSorted _ _ _ _ sorted) = notSorted sorted

isSorted : (v : List Nat) -> Dec (Sorted v)
isSorted [] = Yes EmptySorted
isSorted [a] = Yes $ OneSorted a
isSorted (a :: b :: rem) with (isLTE a b, isSorted (b :: rem))
    -- if first is less or equal then second and tail is sorted, then it is sorted
    isSorted (a :: b :: rem) | (Yes prfLTE, Yes prfSortedBRem) = Yes $ RecSorted a b rem prfLTE prfSortedBRem
    -- otherwise it is not sorted
    isSorted (a :: b :: rem) | (_, No contra) = No $ notSortedBRem contra
    isSorted (a :: b :: rem) | (No contra, _) = No $ notSortedE1E2 contra

-- Non-dependent-types shortcut
isSortedBool : (v : List Nat) -> Bool
isSortedBool v = case isSorted v of
    Yes _ => True
    No _ => False

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

partial -- TODO
sort1 : (i : List Nat) -> (o : List Nat ** (Sorted o, PermSimple i o))
sort1 [] = ([] ** (EmptySorted, PermSimpleEmpty))
sort1 (a :: as) =
    let (v ** vs ** (perm_a_as_v_vs, v_lte_vs)) = removeMinElement (a :: as) in
    let (ws ** (ws_sorted, perm_vs_ws)) = sort1 vs in
    let v_lte_ws = lteAllTrans v_lte_vs perm_vs_ws in
    let v_ws = v :: ws in
    let perm_v_vs_v_ws = permSimplePrepend {a = v} perm_vs_ws in
    let perm_a_as_v_ws = permSimpleTrans perm_a_as_v_vs perm_v_vs_v_ws in
    let v_ws_sorted = ?a in
    (v_ws ** (v_ws_sorted, perm_a_as_v_ws))

main : IO ()
main = putStrLn $ show $ isSortedBool [2, 3, 5]
