module PermSimple

import PermHard
import InList

%default total

-- Human-friendly definition of that is permutation of two lists
-- Alternative definition of permutation is is located
-- in the next module and called `PermHard`.
-- Functions `permSimpleToHard` and `permHardToSimple` prove
-- that both definitions are equivalent.
public export
data PermSimple : List a -> List a -> Type
    where
        -- Empty list is a permutation to itself
        PermSimpleEmpty : PermSimple [] []
        -- If two lists are permutations, then inserting the same element
        -- into middle of them results in permutation of new lists.
        PermSimpleInsert : (p : PermSimple (xs ++ ys) (zs ++ ws)) ->
            PermSimple (xs ++ [v] ++ ys) (zs ++ [v] ++ ws)

-- List is always a permutation to itself.
export
permSimpleFromRefl : (xs : _) -> PermSimple xs xs
permSimpleFromRefl [] = PermSimpleEmpty
permSimpleFromRefl (v :: xs) =
    let pp = permSimpleFromRefl xs in
    PermSimpleInsert pp {xs = []} {ys = xs} {zs = []} {ws = xs}

-- Prepending an element to two lists results in permutation
export
permSimplePrepend : PermSimple xs ys -> PermSimple (a :: xs) (a :: ys)
permSimplePrepend = PermSimpleInsert {xs = []} {zs = []}

-- Convert this definition to "hard" definition
permSimpleToHard : PermSimple as bs -> PermHard as bs
permSimpleToHard PermSimpleEmpty = PermHardRefl
permSimpleToHard {as = xs ++ [v] ++ ys} {bs = zs ++ [v] ++ ws} (PermSimpleInsert p) =
    let xys = xs ++ ys in
    let zws = zs ++ ws in
    let xvys = xs ++ [v] ++ ys in
    let zvws = zs ++ [v] ++ ws in
    let pp : PermHard xys zws = permSimpleToHard p in
    PermHardIns pp (inListFromPlus xs v ys) (inListFromPlus zs v ws)

-- Copy-paste of `replace` for two arguments, I don't understand how it works
replace2 : {P : a -> b -> Type} -> x = y -> z = w -> P x z -> P y w
replace2 Refl Refl prf = prf

-- Convert "hard" definition to simple
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

-- Permutations are transitive.
-- However, regular human cannot prove it with this file definitios of permutation
-- so the proof converts it to "hard" definition, uses trans from there
-- and then converts back.
export
permSimpleTrans : PermSimple xs ys -> PermSimple ys zs -> PermSimple xs zs
permSimpleTrans p1 p2 =
    let p1h = permSimpleToHard p1 in
    let p2h = permSimpleToHard p2 in
    permHardToSimple $ permHardTrans p1h p2h

-- Prove that permutation is a symmetric relation
export
permSimpleSym : PermSimple xs ys -> PermSimple ys xs
permSimpleSym PermSimpleEmpty = PermSimpleEmpty
permSimpleSym (PermSimpleInsert p) = PermSimpleInsert (permSimpleSym p)

-- Permutated lists have the same length
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
        -- trans both arguments shortcut
        substlr : a = b -> a = c -> b = d -> c = d
        substlr a_b a_c b_d = trans (trans (sym a_c) a_b) b_d

        -- three-argument version of `lengthAppend`
        lengthAppend3 : (xs, ys, zs : List t) ->
            length (xs ++ ys ++ zs) = length xs + length ys + length zs
        lengthAppend3 xs ys zs =
            let t2 : (length (ys ++ zs) = length ys + length zs) = lengthAppend ys zs in
            let t5 : (length xs + length (ys ++ zs) = length xs + (length ys + length zs)) =
                plusConstantLeft _ _ _ t2 in

            let sl : (length xs + length (ys ++ zs) = length (xs ++ ys ++ zs)) = sym $ lengthAppend _ _ in
            let sr : (length xs + (length ys + length zs) = length xs + length ys + length zs) =
                plusAssociative _ _ _ in

            substlr t5 sl sr

        flipPlus : (x, y, z : Nat) -> x + y + z = y + x + z
        flipPlus x y z = cong (plusCommutative x y) {f = \v => v + z}

        flipListLength : (xs, ys, zs : List t) -> length (xs ++ ys ++ zs) = length (ys ++ xs ++ zs)
        flipListLength xs ys zs =
            let a1 : (length (xs ++ ys ++ zs) = length xs + length ys + length zs) = lengthAppend3 _ _ _ in
            let a2 : (length (ys ++ xs ++ zs) = length ys + length xs + length zs) = lengthAppend3 _ _ _ in
            substlr (flipPlus (length xs) (length ys) (length zs)) (sym a1) (sym a2)

        listInsertLength : (xs : List t) -> (v : t) -> (ys : List t) ->
            S (length (xs ++ ys)) = length (xs ++ [v] ++ ys)
        listInsertLength xs v ys =
            let e1 : (S (length (xs ++ ys)) = length ([v] ++ xs ++ ys)) = Refl in
            trans e1 (flipListLength [v] xs ys)

