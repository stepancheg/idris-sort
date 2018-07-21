module Sorted

import LTEAll

%default total

-- Definition of what it means for List to be sorted
public export
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

export
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
export
isSortedBool : (v : List Nat) -> Bool
isSortedBool v = case isSorted v of
    Yes _ => True
    No _ => False

export
sortedReplaceFirstSmaller : LTE a b -> Sorted (b :: rem) -> Sorted (a :: rem)
sortedReplaceFirstSmaller _ EmptySorted impossible
sortedReplaceFirstSmaller {a} {b} _ (OneSorted b) = OneSorted a
sortedReplaceFirstSmaller {a} {b} lteAB (RecSorted b c rem lteBC sortedCRem) =
    RecSorted a c rem (lteTransitive lteAB lteBC) sortedCRem

export
sortedPrepend : LTEAll a xs -> Sorted xs -> Sorted (a :: xs)


