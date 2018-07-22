module InList

%default total

-- Element is in the list
-- This is a helper data type to define a permutation
public export
data InList : t -> List t -> List t -> Type
    where
        InListHere : InList x l (x :: l)
        InListThere : InList x l m -> InList x (a :: l) (a :: m)

inListPrepend : (zs : List t) -> InList x xs xxs -> InList x (zs ++ xs) (zs ++ xxs)
inListPrepend [] il = il
inListPrepend (z :: zs) il = InListThere (inListPrepend zs il)

-- Explicitly construct `InList` from an element and two lists
export
inListFromPlus : (xs : List t) -> (v : t) -> (ys : List t) -> InList v (xs ++ ys) (xs ++ [v] ++ ys)
inListFromPlus xs v ys = inListPrepend xs InListHere

-- Deconstruct `InList` into an element and two lists
export
inListDismantle : InList x xs xxs -> (as ** bs ** (as ++ [x] ++ bs = xxs, as ++ bs = xs))
inListDismantle (InListHere {x} {l}) =
    let fact1 = (the ([] ++ [x] ++ l = x :: l) Refl) in
    let fact2 = (the ([] ++ l = l) Refl) in
    ([] ** l ** (fact1, fact2))
inListDismantle {xxs = a :: m} {xs = a :: l} (InListThere il {x} {a} {m}) =
    let (a1s ** b1s ** (prf1, prf2)) = inListDismantle {x} {xxs = m} il in
    let fact1 : ((a :: a1s) ++ [x] ++ b1s = a :: m) = cong prf1 in
    let fact2 : (a :: a1s ++ b1s = a :: l) = cong prf2 in
    ((a :: a1s) ** b1s ** (fact1, fact2))

-- Result list of `InList` is never empty
export
inListImpliesNotEmpty : InList x xs xxs -> NonEmpty xxs
inListImpliesNotEmpty InListHere = IsNonEmpty
inListImpliesNotEmpty (InListThere _) = IsNonEmpty

-- Third parameter of `InList` is always one element longer than second parameter
export
inListIncreasesLength : InList x xs xxs -> S (length xs) = length xxs
inListIncreasesLength InListHere = Refl
inListIncreasesLength (InListThere i) =
    rewrite inListIncreasesLength i in
    Refl

