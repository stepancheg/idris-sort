module Sorted

import Forall
import SortedAlt

%default total

-- Definition of what it means for List to be sorted
public export
data Sorted : (a -> a -> Type) -> List a -> Type
    where
        -- Empty list is always sorted
        SortedEmpty : {lte : a -> a -> Type} -> Sorted lte []
        -- List of one element is always sorted
        SortedOne : {lte : a -> a -> Type} -> (x : a) -> Sorted lte [x]
        -- List of two or more element is sorted iff both are true
        -- * first is less or equal than second
        -- * tail is sorted
        SortedRec : {lte : a -> a -> Type}
            -> (x : a) -> (y : a) -> (rem : List a)
            -> lte x y -> Sorted lte (y :: rem)
            -> Sorted lte (x :: y :: rem)

-- Proof that list is not sorted if first element is greater than second
notSortedE1E2 : {lte : a -> a -> Type} -> Not (lte x y) -> Sorted lte (x :: y :: rem) -> Void
notSortedE1E2 _ SortedEmpty impossible
notSortedE1E2 _ (SortedOne _) impossible
notSortedE1E2 notLTE (SortedRec _ _ _ lte _) = notLTE lte

-- Proof that list is not sorted if tail is not sorted
notSortedBRem : {lte : a -> a -> Type} -> Not (Sorted lte (y :: rem)) -> Sorted lte (x :: y :: rem) -> Void
notSortedBRem _ SortedEmpty impossible
notSortedBRem _ (SortedOne _) impossible
notSortedBRem notSorted (SortedRec _ _ _ _ sorted) = notSorted sorted

-- Check if list is already sorted
export
isSorted : {lte : a -> a -> Type} -> (isLTE : (x, y : a) -> Dec (lte x y)) -> (v : List a) -> Dec (Sorted lte v)
isSorted _ [] = Yes $ SortedEmpty
isSorted _ [x] = Yes $ SortedOne x
isSorted isLTE (x :: y :: rem) with (isLTE x y, isSorted isLTE (y :: rem))
    -- if first is less or equal then second and tail is sorted, then it is sorted
    isSorted _ (x :: y :: rem) | (Yes prfLTE, Yes prfSortedBRem) = Yes $ SortedRec x y rem prfLTE prfSortedBRem
    -- otherwise it is not sorted
    isSorted _ (x :: y :: rem) | (_, No contra) = No $ notSortedBRem contra
    isSorted _ (x :: y :: rem) | (No contra, _) = No $ notSortedE1E2 contra

-- Non-dependent-types shortcut
-- Just for illustration purposes
export
isSortedBool : {lte : a -> a -> Type} -> (isLTE : (x, y : a) -> Dec (lte x y)) -> (v : List a) -> Bool
isSortedBool isLTE v = case isSorted isLTE v of
    Yes _ => True
    No _ => False

-- Replacing list head with smaller value results in sorted list
export
sortedReplaceFirstSmaller : {lte : a -> a -> Type}
    -> (lteTransitive : {x, y, z : a} -> lte x y -> lte y z -> lte x z)
    -> lte x y
    -> Sorted lte (y :: rem)
    -> Sorted lte (x :: rem)
sortedReplaceFirstSmaller _ _ SortedEmpty impossible
sortedReplaceFirstSmaller {x} {y} _ _ (SortedOne y) = SortedOne x
sortedReplaceFirstSmaller {x} {y} lteTransitive lteXY (SortedRec y z rem lteYZ sortedZRem) =
    SortedRec x z rem (lteTransitive lteXY lteYZ) sortedZRem

sortedToLTEAll : {lte : a -> a -> Type} -> (lteTransitive : {x, y, z : a} -> lte x y -> lte y z -> lte x z) -> Sorted lte (x :: rem) -> Forall (lte x) rem
sortedToLTEAll _ SortedEmpty impossible
sortedToLTEAll {x} {rem = []} _ (SortedOne x) = ForallEmpty
sortedToLTEAll {x} {rem = y :: yrem} lteTransitive (SortedRec x y yrem lteXY sortedYRem) =
    ForallRec lteXY (sortedToLTEAll lteTransitive (sortedReplaceFirstSmaller lteTransitive lteXY sortedYRem))

sortedToAlt : {lte : a -> a -> Type}
    -> (lteTransitive : {x, y, z : a} -> lte x y -> lte y z -> lte x z)
    -> Sorted lte l
    -> SortedAlt lte l
sortedToAlt {l = []} _ SortedEmpty = SortedAltEmpty
sortedToAlt {l = [x]} _ (SortedOne x) = SortedAltRec x [] ForallEmpty SortedAltEmpty
sortedToAlt {l = (x :: y :: rem)} lteTransitive s @ (SortedRec x y rem lteXY sortedYRem) =
    SortedAltRec x (y :: rem) (sortedToLTEAll lteTransitive s) (sortedToAlt lteTransitive sortedYRem)

sortedFromAlt : {lte : a -> a -> Type} -> SortedAlt lte l -> Sorted lte l
sortedFromAlt SortedAltEmpty = SortedEmpty
sortedFromAlt (SortedAltRec x [] _ _) = SortedOne x
sortedFromAlt (SortedAltRec x (y :: rem) lteAll_x_y_rem sorted_alt_y_rem) =
    case lteAll_x_y_rem of
        ForallEmpty impossible
        ForallRec lte_x_y _ =>
            SortedRec x y rem lte_x_y (sortedFromAlt sorted_alt_y_rem)

-- Prepend an element to a sorted list
export
sortedPrepend : {lte : a -> a -> Type}
    -> (lteTransitive : {x, y, z : a} -> lte x y -> lte y z -> lte x z )
    -> Forall (lte x) xs
    -> Sorted lte xs
    -> Sorted lte (x :: xs)
sortedPrepend {lte} lteTransitive lteAll_x_xs = sortedFromAlt . (sortedAltPrepend lteAll_x_xs) . (sortedToAlt lteTransitive)
