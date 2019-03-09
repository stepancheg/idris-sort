module SortedAlt

import Forall

%default total

-- Alternative definition of what is a sorted list
public export
data SortedAlt : (a -> a -> Type) -> List a -> Type
    where
        -- Empty list is sorted
        SortedAltEmpty : {lte : a -> a -> Type} -> SortedAlt lte []
        -- Non-empty list is sorted when
        -- * first element is smaller than the rest
        -- * remaining elements form a sorted list
        SortedAltRec : {lte : a -> a -> Type} -> (x : a) -> (rem : List a) ->
            Forall (lte x) rem -> SortedAlt lte rem -> SortedAlt lte (x :: rem)

-- Proof that single element list is always sorted
sortedAlt1 : (x : a) -> SortedAlt lte [x]
sortedAlt1 x = SortedAltRec x [] ForallEmpty SortedAltEmpty

-- Prepend an element to a sorted list
export
sortedAltPrepend : {lte : a -> a -> Type} -> Forall (lte x) xs -> SortedAlt lte xs -> SortedAlt lte (x :: xs)
sortedAltPrepend = SortedAltRec _ _
