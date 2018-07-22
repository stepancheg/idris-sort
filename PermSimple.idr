module PermSimple

import PermHard
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

permSimpleToHard : PermSimple as bs -> PermHard as bs
permSimpleToHard PermSimpleEmpty = PermHardRefl
permSimpleToHard {as = xs ++ [v] ++ ys} {bs = zs ++ [v] ++ ws} (PermSimpleInsert p) =
    let xys = xs ++ ys in
    let zws = zs ++ ws in
    let xvys = xs ++ [v] ++ ys in
    let zvws = zs ++ [v] ++ ws in
    let pp : PermHard xys zws = permSimpleToHard p in
    PermHardIns pp (inListFromPlus xs v ys) (inListFromPlus zs v ws)

-- Copy-paste of `replace`, I don't understand how it works
replace2 : {P : a -> b -> Type} -> x = y -> z = w -> P x z -> P y w
replace2 Refl Refl prf = prf

permHardToSimple : PermHard as bs -> PermSimple as bs
permHardToSimple PermHardRefl = permSimpleFromRefl _
permHardToSimple {as} {bs} (PermHardIns {l} {m} p ias ibs {x = v}) =
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
    -- TODO: oneline
    let p1h = permSimpleToHard p1 in
    let p2h = permSimpleToHard p2 in
    let ph = permHardTrans p1h p2h in
    permHardToSimple ph

export
permSimpleSym : PermSimple xs ys -> PermSimple ys xs
permSimpleSym PermSimpleEmpty = PermSimpleEmpty
permSimpleSym (PermSimpleInsert p) = PermSimpleInsert (permSimpleSym p)

-- TODO: inline
substl : a = b -> a = c -> c = b
substl a_b a_c = trans (sym a_c) a_b

substr : a = b -> b = c -> a = c
substr a_b b_c = trans a_b b_c

substlr : a = b -> a = c -> b = d -> c = d
substlr a_b a_c b_d = substr (substl a_b a_c) b_d

lengthAppend3 : (xs, ys, zs : List Nat) -> length (xs ++ ys ++ zs) = length xs + length ys + length zs
lengthAppend3 xs ys zs =
    let t2 : (length (ys ++ zs) = length ys + length zs) = lengthAppend ys zs in
    let t5 : (length xs + length (ys ++ zs) = length xs + (length ys + length zs)) =
        plusConstantLeft _ _ _ t2 in

    let sl : (length xs + length (ys ++ zs) = length (xs ++ ys ++ zs)) = sym $ lengthAppend _ _ in
    let sr : (length xs + (length ys + length zs) = length xs + length ys + length zs) = plusAssociative _ _ _ in

    substlr t5 sl sr

export
permSimpleLengthRefl : PermSimple xs ys -> length xs = length ys
permSimpleLengthRefl PermSimpleEmpty = Refl
permSimpleLengthRefl (PermSimpleInsert p {v} {xs} {ys} {zs} {ws}) =
    let prev : (length (xs ++ ys) = length (zs ++ ws)) = permSimpleLengthRefl p in
    let s_prev : (S (length (xs ++ ys)) = S (length (zs ++ ws))) = cong prev in
    let ins_l : (S (length (xs ++ ys)) = length (xs ++ [v] ++ ys)) = listInsertLength _ _ _ in
    let ins_r : (S (length (zs ++ ws)) = length (zs ++ [v] ++ ws)) = listInsertLength _ _ _ in
    substlr s_prev ins_l ins_r
    where
        flipPlus : (x, y, z : Nat) -> x + y + z = y + x + z
        flipPlus x y z = cong (plusCommutative x y) {f = \v => v + z}

        flipListLength : (xs, ys, zs : List Nat) -> length (xs ++ ys ++ zs) = length (ys ++ xs ++ zs)
        flipListLength xs ys zs =
            let a1 : (length (xs ++ ys ++ zs) = length xs + length ys + length zs) = lengthAppend3 _ _ _ in
            let a2 : (length (ys ++ xs ++ zs) = length ys + length xs + length zs) = lengthAppend3 _ _ _ in
            substlr (flipPlus (length xs) (length ys) (length zs)) (sym a1) (sym a2)

        listInsertLength : (xs : List Nat) -> (v : Nat) -> (ys : List Nat) ->
            S (length (xs ++ ys)) = length (xs ++ [v] ++ ys)
        listInsertLength xs v ys =
            let e1 : (S (length (xs ++ ys)) = length ([v] ++ xs ++ ys)) = Refl in
            substr e1 (flipListLength [v] xs ys)

