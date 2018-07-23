module SortedAlt

import Forall

%default total

-- Alternative definition of what is a sorted list
public export
data SortedAlt : List Nat -> Type
    where
        -- Empty list is sorted
        SortedAltEmpty : SortedAlt []
        -- Non-empty list is sorted when
        -- * first element is smaller than the rest
        -- * remaining elements form a sorted list
        SortedAltRec : (a : Nat) -> (rem : List Nat) ->
            Forall (LTE a) rem -> SortedAlt rem -> SortedAlt (a :: rem)

-- Proof that single element list is always sorted
sortedAlt1 : (a : Nat) -> SortedAlt [a]
sortedAlt1 a = SortedAltRec a [] ForallEmpty SortedAltEmpty

-- Prepend an element to a sorted list
export
sortedAltPrepend : Forall (LTE a) xs -> SortedAlt xs -> SortedAlt (a :: xs)
sortedAltPrepend = SortedAltRec _ _
