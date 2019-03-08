module Sorted

import Forall
import SortedAlt

%default total

-- Definition of what it means for List to be sorted
public export
data Sorted : (Nat -> Nat -> Type) -> List Nat -> Type
    where
        -- Empty list is always sorted
        SortedEmpty : {lte : Nat -> Nat -> Type} -> Sorted lte []
        -- List of one element is always sorted
        SortedOne : {lte : Nat -> Nat -> Type} -> (a : Nat) -> Sorted lte [a]
        -- List of two or more element is sorted iff both are true
        -- * first is less or equal than second
        -- * tail is sorted
        SortedRec : {lte : Nat -> Nat -> Type}
            -> (a : Nat) -> (b : Nat) -> (rem : List Nat)
            -> lte a b -> Sorted lte (b :: rem)
            -> Sorted lte (a :: b :: rem)

-- Proof that list is not sorted if first element is greater than second
notSortedE1E2 : (lte : Nat -> Nat -> Type) -> Not (lte a b) -> Sorted lte (a :: b :: rem) -> Void
notSortedE1E2 _ _ SortedEmpty impossible
notSortedE1E2 _ _ (SortedOne _) impossible
notSortedE1E2 _ notLTE (SortedRec _ _ _ lte _) = notLTE lte

-- Proof that list is not sorted if tail is not sorted
notSortedBRem : (lte : Nat -> Nat -> Type) -> Not (Sorted lte (b :: rem)) -> Sorted lte (a :: b :: rem) -> Void
notSortedBRem _ _ SortedEmpty impossible
notSortedBRem _ _ (SortedOne _) impossible
notSortedBRem _ notSorted (SortedRec _ _ _ _ sorted) = notSorted sorted

-- Check if list is already sorted
export
isSorted : {lte : Nat -> Nat -> Type} -> (isLTE : (x, y : Nat) -> Dec (lte x y)) -> (v : List Nat) -> Dec (Sorted lte v)
isSorted _ [] = Yes $ SortedEmpty
isSorted _ [a] = Yes $ SortedOne a
isSorted isLTE (a :: b :: rem) with (isLTE a b, isSorted isLTE (b :: rem))
    -- if first is less or equal then second and tail is sorted, then it is sorted
    isSorted _ (a :: b :: rem) | (Yes prfLTE, Yes prfSortedBRem) = Yes $ SortedRec a b rem prfLTE prfSortedBRem
    -- otherwise it is not sorted
    isSorted _ (a :: b :: rem) | (_, No contra) = No $ notSortedBRem _ contra
    isSorted _ (a :: b :: rem) | (No contra, _) = No $ notSortedE1E2 _ contra

-- Non-dependent-types shortcut
-- Just for illustration purposes
export
isSortedBool : {lte : Nat -> Nat -> Type} -> (isLTE : (x, y : Nat) -> Dec (lte x y)) -> (v : List Nat) -> Bool
isSortedBool isLTE v = case isSorted isLTE v of
    Yes _ => True
    No _ => False

-- Replacing list head with smaller value results in sorted list
export
sortedReplaceFirstSmaller : {lte : Nat -> Nat -> Type} -> (lteTransitive : {x, y, z : Nat} -> lte x y -> lte y z -> lte x z) -> lte a b -> Sorted lte (b :: rem) -> Sorted lte (a :: rem)
sortedReplaceFirstSmaller _ _ SortedEmpty impossible
sortedReplaceFirstSmaller {a} {b} _ _ (SortedOne b) = SortedOne a
sortedReplaceFirstSmaller {a} {b} lteTransitive lteAB (SortedRec b c rem lteBC sortedCRem) =
    SortedRec a c rem (lteTransitive lteAB lteBC) sortedCRem

sortedToLTEAll : {lte : Nat -> Nat -> Type} -> (lteTransitive : {x, y, z : Nat} -> lte x y -> lte y z -> lte x z) -> Sorted lte (a :: rem) -> Forall (lte a) rem
sortedToLTEAll _ SortedEmpty impossible
sortedToLTEAll {a} {rem = []} _ (SortedOne a) = ForallEmpty
sortedToLTEAll {a} {rem = b :: brem} lteTransitive (SortedRec a b brem lteAB sortedBRem) =
    ForallRec lteAB (sortedToLTEAll lteTransitive (sortedReplaceFirstSmaller lteTransitive lteAB sortedBRem))

sortedToAlt : {lte : Nat -> Nat -> Type} -> (lteTransitive : {x, y, z : Nat} -> lte x y -> lte y z -> lte x z) -> Sorted lte l -> SortedAlt lte l
sortedToAlt {l = []} _ SortedEmpty = SortedAltEmpty
sortedToAlt {l = [a]} _ (SortedOne a) = SortedAltRec a [] ForallEmpty SortedAltEmpty
sortedToAlt {l = (a :: b :: rem)} lteTransitive s @ (SortedRec a b rem lteAB sortedBRem) =
    SortedAltRec a (b :: rem) (sortedToLTEAll lteTransitive s) (sortedToAlt lteTransitive sortedBRem)

sortedFromAlt : {lte : Nat -> Nat -> Type} -> SortedAlt lte l -> Sorted lte l
sortedFromAlt SortedAltEmpty = SortedEmpty
sortedFromAlt (SortedAltRec a [] _ _) = SortedOne a
sortedFromAlt (SortedAltRec a (b :: rem) lteAll_a_b_rem sorted_alt_b_rem) =
    case lteAll_a_b_rem of
        ForallEmpty impossible
        ForallRec lte_a_b _ =>
            SortedRec a b rem lte_a_b (sortedFromAlt sorted_alt_b_rem)

-- Prepend an element to a sorted list
export
sortedPrepend : {lte : Nat -> Nat -> Type} -> (lteTransitive : {x, y, z : Nat} -> lte x y -> lte y z -> lte x z ) -> Forall (lte a) xs -> Sorted lte xs -> Sorted lte (a :: xs)
sortedPrepend {lte} lteTransitive lteAll_a_xs = sortedFromAlt . (sortedAltPrepend lteAll_a_xs) . (sortedToAlt lteTransitive)
