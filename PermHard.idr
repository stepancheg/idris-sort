module PermHard

-- Implementation of list permutation property in Idris.
-- This algorithm is a translation of this code in Agda I've found
-- https://gist.github.com/AndrasKovacs/0d7bcc3aba513c29ef73/
-- This definition is not very human friendly, but it's suitable
-- for proving transitivity.
-- Simpler definitions of permutation is in the file `PermSimple.idr`
-- which also contains a proof that both definitions are equivalent.

import InList

%default total

public export
data PermHard : List a -> List a -> Type
    where
        PermHardRefl : PermHard l l
        PermHardIns : PermHard l m -> InList x l l1 -> InList x m m1 -> PermHard l1 m1

inv : InList a as cs -> InList b bs cs -> Either (a = b, as = bs) (ds ** (InList b ds as, InList a ds bs))
inv {as} InListHere InListHere = Left (Refl, Refl)
inv InListHere (InListThere p2) = Right (_ ** (p2, InListHere))
inv (InListThere p1) InListHere = Right (_ ** (InListHere , p1))
inv (InListThere p1) (InListThere p2) =
    case inv p1 p2 of
        Left (Refl, Refl) => Left (Refl, Refl)
        Right (ds ** (ias, ibs)) => Right ((_ :: ds) ** (InListThere ias, InListThere ibs))

exch : InList x xs xxs -> InList y xxs yxxs -> (yxs ** (InList y xs yxs, InList x yxs yxxs))
exch p1 InListHere = (_ ** (InListHere, InListThere p1))
exch InListHere (InListThere p2) = (_ ** (p2, InListHere))
exch (InListThere p1) (InListThere p2) with (exch p1 p2)
    exch _ _ | (_ ** (p1x, p2x)) = (_ ** (InListThere p1x, InListThere p2x))


l1 : PermHard (x :: xs) xys -> (ys ** (InList x ys xys, PermHard xs ys))
l1 PermHardRefl = (_ ** (InListHere, PermHardRefl))
l1 (PermHardIns p InListHere iys) = (_ ** (iys, p))
l1 (PermHardIns p (InListThere ixs) iys) with (l1 p)
    l1 (PermHardIns p (InListThere ixs) iys {x = y}) {x = x} | (ys ** (i, perm)) with (exch i iys)
        l1 (PermHardIns p (InListThere ixs) iys) | (ys ** (i, perm)) | (proj1 ** (proj2, proj3)) =
            (proj1 ** (proj3, PermHardIns perm ixs proj2))


nonEmptyListLengthNeverZero : (xxs : List t) -> {auto nonEmpty : NonEmpty xxs} -> Not (length xxs = Z)
nonEmptyListLengthNeverZero [] {nonEmpty} = absurd nonEmpty
nonEmptyListLengthNeverZero (x :: xs) = absurd

extrPerm : InList x xs xxs -> {l : Nat} -> {auto ok : (length xxs = l)} -> PermHard xxs xys -> (ys ** (InList x ys xys, PermHard xs ys))

extrPerm {xxs} {l = Z} {ok} i _ =
    let i = inListImpliesNotEmpty i in
    let nz = nonEmptyListLengthNeverZero xxs in
    void (nz ok)

extrPerm i PermHardRefl = (_ ** (i, PermHardRefl))

extrPerm InListHere (PermHardIns l1_m1 InListHere i_m1) = (_ ** (i_m1, l1_m1))

extrPerm InListHere (PermHardIns p2 (InListThere ixs) iys) =
    let (proj1 ** (proj2, proj6)) = l1 p2 in
    let (proj3 ** (proj4, proj5)) = exch proj2 iys in
    (proj3 ** (proj5, PermHardIns proj6 ixs proj4))

extrPerm {ok} {xxs = a :: xs} {l = S k} n@(InListThere p1 {a} {l = zs} {m = xs}) (PermHardIns p2 InListHere iys) =
    let www = length xs = k in
    let (proj1 ** (proj2, proj6)) = extrPerm {l = k} {xxs = xs} {ok = cong {f=Nat.pred} ok} p1 p2 in
    let (proj3 ** (proj4, proj5)) = exch proj2 iys in
    (proj3 ** (proj5, PermHardIns proj6 InListHere proj4))

extrPerm {l = S (S k)} {ok} (InListThere p1) (PermHardIns p2 (InListThere ixs) iys) =
    case inv p1 ixs of
        Left (Refl, Refl) => (_ ** (iys, p2))
        Right (proj11 ** (proj12, proj13)) =>
            let (proj21 ** (proj22, proj23)) = l1 p2 in
            let ok0 = inListIncreasesLength ixs in
            let ok1 = cong {f=Nat.pred} ok in
            let ok2 = trans ok0 ok1 in
            let ok3 = cong {f=Nat.pred} ok2 in
            let (proj31 ** (proj32, proj33)) = extrPerm {l = k} proj13 proj23 in
            let (proj41 ** (proj42, proj43)) = exch proj32 proj22 in
            let (proj51 ** (proj52, proj53)) = exch proj43 iys in
            (proj51 ** (proj53, PermHardIns (PermHardIns proj33 InListHere proj42) (InListThere proj12) proj52))

extrPerm {l = S Z} {ok} {xxs = a :: x1 :: xs} (InListThere p1 {m = x1 :: xs}) _ =
    let imp02 : Not (length (a :: x1 :: xs) = S Z) = SSIsNotSZ in
    absurd (imp02 ok)
    where
        SSIsNotSZ : {x: Nat} -> (S (S x) = S Z) -> Void
        SSIsNotSZ Refl impossible


export
permHardTrans : PermHard xs ys -> PermHard ys zs -> PermHard xs zs
permHardTrans PermHardRefl p = p
permHardTrans p PermHardRefl = p
permHardTrans (PermHardIns xy ix iy) p2 =
    let (proj1 ** (proj2, proj3)) = extrPerm iy p2 in
    PermHardIns (permHardTrans xy proj3) ix proj2

main : IO ()
main = putStrLn $ show $ "aa"
