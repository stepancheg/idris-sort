module Forall

%default total

-- Property is true for all elements of the list
public export
data Forall : (a -> Type) -> List a -> Type
    where
        ForallEmpty : Forall p []
        ForallRec : p x -> Forall p xs -> Forall p (x :: xs)

export
forallFromList : ((x : a) -> p x) -> (xs : List a) -> Forall p xs
forallFromList _ [] = ForallEmpty
forallFromList f (x :: xs) = ForallRec (f x) (forallFromList f xs)

export
forall0 : Forall p []
forall0 = ForallEmpty

export
forall1 : {p : a -> Type} -> p x -> Forall p [x]
forall1 p_x = ForallRec p_x ForallEmpty

export
forallMap : (f : (x : a) -> p x -> q x) -> Forall p xs -> Forall q xs
forallMap {xs = []} _ ForallEmpty = ForallEmpty
forallMap {xs = x :: xs} f (ForallRec p_x fa_xs) = ForallRec (f x p_x) (forallMap f fa_xs)

export
forallConcat : Forall p xs -> Forall p ys -> Forall p (xs ++ ys)
forallConcat ForallEmpty f = f
forallConcat {xs} f ForallEmpty = rewrite appendNilRightNeutral xs in f
forallConcat {xs = x :: xs} (ForallRec p_x fx) z =
    ForallRec p_x (forallConcat fx z)

export
forallSplit : Forall p (xs ++ ys) -> (Forall p xs, Forall p ys)
forallSplit {xs = []} {ys = []} ForallEmpty = (ForallEmpty, ForallEmpty)
forallSplit {xs = []} r = (ForallEmpty, r)
forallSplit {xs = xxs} r =
    case xxs of
        [] => (ForallEmpty, r)
        x :: xs =>
            case r of
                ForallEmpty impossible
                ForallRec p_x forall_xs_ys =>
                    let (forall_xs, forall_ys) = forallSplit forall_xs_ys in
                    let forall_x_xs = forallConcat (forall1 p_x) forall_xs in
                    (forall_x_xs, forall_ys)
