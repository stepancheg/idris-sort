module Sorted

import LTEAll
import SortedAlt

%default total

-- Definition of what it means for List to be sorted
public export
data Sorted : List Nat -> Type
    where
        -- empty list is always sorted
        SortedEmpty : Sorted []
        -- list of one element is always sorted
        SortedOne : (a : Nat) -> Sorted [a]
        -- list of two or more element is sorted iff both are true
        -- * first is less or equal than second
        -- * tail is sorted
        SortedRec : (a : Nat) -> (b : Nat) -> (rem : List Nat)
            -> LTE a b -> Sorted (b :: rem) -> Sorted (a :: b :: rem)

-- Proof that list is not sorted if first element is greater than second
notSortedE1E2 : Not (LTE a b) -> Sorted (a :: b :: rem) -> Void
notSortedE1E2 _ SortedEmpty impossible
notSortedE1E2 _ (SortedOne _) impossible
notSortedE1E2 {a} {b} {rem} notLTE (SortedRec a b rem lte _) = notLTE lte

-- Proof that list is not sorted if tail is not sorted
notSortedBRem : Not (Sorted (b :: rem)) -> Sorted (a :: b :: rem) -> Void
notSortedBRem _ SortedEmpty impossible
notSortedBRem _ (SortedOne _) impossible
notSortedBRem notSorted (SortedRec _ _ _ _ sorted) = notSorted sorted

export
isSorted : (v : List Nat) -> Dec (Sorted v)
isSorted [] = Yes SortedEmpty
isSorted [a] = Yes $ SortedOne a
isSorted (a :: b :: rem) with (isLTE a b, isSorted (b :: rem))
    -- if first is less or equal then second and tail is sorted, then it is sorted
    isSorted (a :: b :: rem) | (Yes prfLTE, Yes prfSortedBRem) = Yes $ SortedRec a b rem prfLTE prfSortedBRem
    -- otherwise it is not sorted
    isSorted (a :: b :: rem) | (_, No contra) = No $ notSortedBRem contra
    isSorted (a :: b :: rem) | (No contra, _) = No $ notSortedE1E2 contra

-- Non-dependent-types shortcut
export
isSortedBool : (v : List Nat) -> Bool
isSortedBool v = case isSorted v of
    Yes _ => True
    No _ => False

export
sortedReplaceFirstSmaller : LTE a b -> Sorted (b :: rem) -> Sorted (a :: rem)
sortedReplaceFirstSmaller _ SortedEmpty impossible
sortedReplaceFirstSmaller {a} {b} _ (SortedOne b) = SortedOne a
sortedReplaceFirstSmaller {a} {b} lteAB (SortedRec b c rem lteBC sortedCRem) =
    SortedRec a c rem (lteTransitive lteAB lteBC) sortedCRem

sortedToLTEAll : Sorted (a :: rem) -> LTEAll a rem
sortedToLTEAll SortedEmpty impossible
sortedToLTEAll {a} {rem = []} (SortedOne a) = LTEAllEmpty
sortedToLTEAll {a} {rem = b :: brem} (SortedRec a b brem lteAB sortedBRem) =
    LTEAllRec a b lteAB (sortedToLTEAll (sortedReplaceFirstSmaller lteAB sortedBRem))

sortedToAlt : Sorted l -> SortedAlt l
sortedToAlt {l = []} SortedEmpty = SortedAltEmpty
sortedToAlt {l = [a]} (SortedOne a) = SortedAltRec a [] LTEAllEmpty SortedAltEmpty
sortedToAlt {l = (a :: b :: rem)} s @ (SortedRec a b rem lteAB sortedBRem) =
    SortedAltRec a (b :: rem) (sortedToLTEAll s) (sortedToAlt sortedBRem)

sortedFromAlt : SortedAlt l -> Sorted l
sortedFromAlt SortedAltEmpty = SortedEmpty
sortedFromAlt (SortedAltRec a [] _ _) = SortedOne a
sortedFromAlt (SortedAltRec a (b :: rem) lteAll_a_b_rem sorted_alt_b_rem) =
    case lteAll_a_b_rem of
        LTEAllEmpty impossible
        LTEAllRec _ _ lte_a_b _ =>
            SortedRec a b rem lte_a_b (sortedFromAlt sorted_alt_b_rem)

export
sortedPrepend : LTEAll a xs -> Sorted xs -> Sorted (a :: xs)
sortedPrepend lteAll_a_xs = (sortedFromAlt . (sortedAltPrepend lteAll_a_xs) . sortedToAlt)
