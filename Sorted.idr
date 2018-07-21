module Sorted

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

export
sortedReplaceFirstSmaller : LTE a b -> Sorted (b :: rem) -> Sorted (a :: rem)
sortedReplaceFirstSmaller _ EmptySorted impossible
sortedReplaceFirstSmaller {a} {b} _ (OneSorted b) = OneSorted a
sortedReplaceFirstSmaller {a} {b} lteAB (RecSorted b c rem lteBC sortedCRem) =
    RecSorted a c rem (lteTransitive lteAB lteBC) sortedCRem
