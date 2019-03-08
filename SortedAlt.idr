module SortedAlt

import Forall

%default total

-- Alternative definition of what is a sorted list
public export
data SortedAlt : (Nat -> Nat -> Type) -> List Nat -> Type
    where
        -- Empty list is sorted
        SortedAltEmpty : (lte : Nat -> Nat -> Type) -> SortedAlt lte []
        -- Non-empty list is sorted when
        -- * first element is smaller than the rest
        -- * remaining elements form a sorted list
        SortedAltRec : (lte : Nat -> Nat -> Type) -> (a : Nat) -> (rem : List Nat) ->
            Forall (lte a) rem -> SortedAlt lte rem -> SortedAlt lte (a :: rem)

-- Proof that single element list is always sorted
sortedAlt1 : (lte : Nat -> Nat -> Type) -> (a : Nat) -> SortedAlt lte [a]
sortedAlt1 lte a = SortedAltRec lte a [] ForallEmpty (SortedAltEmpty lte)

-- Prepend an element to a sorted list
export
sortedAltPrepend : (lte : Nat -> Nat -> Type) -> Forall (lte x) xs -> SortedAlt lte xs -> SortedAlt lte (x :: xs)
sortedAltPrepend lte = SortedAltRec lte _ _
