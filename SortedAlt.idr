module SortedAlt

import LTEAll

%default total

public export
data SortedAlt : List Nat -> Type
    where
        SortedAltEmpty : SortedAlt []
        SortedAltRec : (a : Nat) -> (rem : List Nat) ->
            LTEAll a rem -> SortedAlt rem -> SortedAlt (a :: rem)

sortedAlt1 : (a : Nat) -> SortedAlt [a]
sortedAlt1 a = SortedAltRec a [] (LTEAllEmpty a) SortedAltEmpty

export
sortedAltPrepend : LTEAll a xs -> SortedAlt xs -> SortedAlt (a :: xs)
sortedAltPrepend = SortedAltRec _ _
