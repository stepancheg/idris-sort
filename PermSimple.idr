module PermSimple

import Perm3
import InList

%default total

data PermWithEq : List Nat -> List Nat -> Type
    where
        PermWithEqRefl : xs = ys -> PermWithEq xs ys
        PermWithEqIns : PermWithEq l m -> InList x l l1 -> InList x m m1 -> PermWithEq l1 m1

permHardToWithEq : Perm xs ys -> PermWithEq xs ys
permHardToWithEq PermRefl = PermWithEqRefl Refl
permHardToWithEq (PermIns p ixs iys) = PermWithEqIns (permHardToWithEq p) ixs iys

permWithEqToHard : PermWithEq xs ys -> Perm xs ys
permWithEqToHard (PermWithEqRefl prf) = rewrite prf in PermRefl
permWithEqToHard (PermWithEqIns p ixs iys) = PermIns (permWithEqToHard p) ixs iys

data PermSimple : List Nat -> List Nat -> Type
    where
        PermSimpleEmpty : PermSimple [] []
        PermSimpleInsert : (p : PermSimple (xs ++ ys) (zs ++ ws)) ->
            PermSimple (xs ++ [v] ++ ys) (zs ++ [v] ++ ws)

permSimpleToHard : PermSimple as bs -> Perm as bs
permSimpleToHard PermSimpleEmpty = PermRefl
permSimpleToHard {as = xs ++ [v] ++ ys} {bs = zs ++ [v] ++ ws} (PermSimpleInsert p) =
    let xys = xs ++ ys in
    let zws = zs ++ ws in
    let xvys = xs ++ [v] ++ ys in
    let zvws = zs ++ [v] ++ ws in
    let pp : Perm xys zws = permSimpleToHard p in
    PermIns pp (inListFromPlus xs v ys) (inListFromPlus zs v ws)
