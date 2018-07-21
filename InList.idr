module InList

%default total

public export
data InList : Nat -> List Nat -> List Nat -> Type
    where
        InListHere : InList x l (x :: l)
        InListThere : InList x l m -> InList x (a :: l) (a :: m)

inListPrepend : (zs : List Nat) -> InList x xs xxs -> InList x (zs ++ xs) (zs ++ xxs)
inListPrepend [] il = il
inListPrepend (z :: zs) il = InListThere (inListPrepend zs il)

export
inListFromPlus : (xs : List Nat) -> (v : Nat) -> (ys : List Nat) -> InList v (xs ++ ys) (xs ++ [v] ++ ys)
inListFromPlus xs v ys = inListPrepend xs InListHere

export
inListImpliesNotEmpty : InList x xs xxs -> NonEmpty xxs
inListImpliesNotEmpty InListHere = IsNonEmpty
inListImpliesNotEmpty (InListThere _) = IsNonEmpty

export
inListIncreasesLength : InList x xs xxs -> S (length xs) = length xxs
inListIncreasesLength InListHere = Refl
inListIncreasesLength (InListThere i) =
    rewrite inListIncreasesLength i in
    Refl

