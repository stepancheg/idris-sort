module PermSimple

import Perm3
import InList

%default total

public export
data PermSimple : List Nat -> List Nat -> Type
    where
        PermSimpleEmpty : PermSimple [] []
        PermSimpleInsert : (p : PermSimple (xs ++ ys) (zs ++ ws)) ->
            PermSimple (xs ++ [v] ++ ys) (zs ++ [v] ++ ws)

export
permSimpleFromRefl : (xs : _) -> PermSimple xs xs
permSimpleFromRefl [] = PermSimpleEmpty
permSimpleFromRefl (v :: xs) =
    let pp = permSimpleFromRefl xs in
    PermSimpleInsert pp {xs = []} {ys = xs} {zs = []} {ws = xs}

export
permSimplePrepend : PermSimple xs ys -> PermSimple (a :: xs) (a :: ys)
permSimplePrepend = PermSimpleInsert {xs = []} {zs = []}

permSimpleToHard : PermSimple as bs -> Perm as bs
permSimpleToHard PermSimpleEmpty = PermRefl
permSimpleToHard {as = xs ++ [v] ++ ys} {bs = zs ++ [v] ++ ws} (PermSimpleInsert p) =
    let xys = xs ++ ys in
    let zws = zs ++ ws in
    let xvys = xs ++ [v] ++ ys in
    let zvws = zs ++ [v] ++ ws in
    let pp : Perm xys zws = permSimpleToHard p in
    PermIns pp (inListFromPlus xs v ys) (inListFromPlus zs v ws)

-- Copy-paste of `replace`, I don't understand how it works
replace2 : {P : a -> b -> Type} -> x = y -> z = w -> P x z -> P y w
replace2 Refl Refl prf = prf

permHardToSimple : Perm as bs -> PermSimple as bs
permHardToSimple PermRefl = permSimpleFromRefl _
permHardToSimple {as} {bs} (PermIns {l} {m} p ias ibs {x = v}) =
    let (xs ** ys ** (xs_v_ys, xs_ys)) = inListDismantle ias in
    let (zs ** ws ** (zs_v_ws, zs_ws)) = inListDismantle ibs in
    let f1 : (xs ++ [v] ++ ys = as) = xs_v_ys in
    let f2 : (zs ++ [v] ++ ws = bs) = zs_v_ws in
    let f3 : (xs ++ ys = l) = xs_ys in
    let f4 : (zs ++ ws = m) = zs_ws in
    let pp : PermSimple (xs ++ ys) (zs ++ ws) = replace2 (sym f3) (sym f4) (permHardToSimple p) in
    replace2 f1 f2 (PermSimpleInsert pp {xs} {ys} {zs} {ws} {v})

export
permSimpleTrans : PermSimple xs ys -> PermSimple ys zs -> PermSimple xs zs
permSimpleTrans p1 p2 =
    let p1h = permSimpleToHard p1 in
    let p2h = permSimpleToHard p2 in
    let ph = permTrans p1h p2h in
    permHardToSimple ph

permSimpleSym : PermSimple xs ys -> PermSimple ys xs
permSimpleSym PermSimpleEmpty = PermSimpleEmpty
permSimpleSym (PermSimpleInsert p) = PermSimpleInsert (permSimpleSym p)
