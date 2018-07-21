module PermSimple

import Perm3
import InList

%default total

data PermSimple : List Nat -> List Nat -> Type
    where
        PermSimpleEmpty : PermSimple [] []
        PermSimpleInsert : (p : PermSimple (xs ++ ys) (zs ++ ws)) ->
            PermSimple (xs ++ [v] ++ ys) (zs ++ [v] ++ ws)

data PermWithEq : List Nat -> List Nat -> Type
    where
        PermWithEqRefl : xs = ys -> PermWithEq xs ys

permReflFromEq : (xs : List Nat) -> (ys : List Nat) -> (xs = ys) -> Perm xs ys

permSimpleToHard : PermSimple as bs -> Perm as bs
permSimpleToHard PermSimpleEmpty = PermRefl
permSimpleToHard {as = xs ++ [v] ++ ys} {bs = zs ++ [v] ++ ws} (PermSimpleInsert p) =
    let xys = xs ++ ys in
    let zws = zs ++ ws in
    let xvys = xs ++ [v] ++ ys in
    let zvws = zs ++ [v] ++ ws in
    let pp : Perm xys zws = permSimpleToHard p in
    case decEq xys zws of
        No contra =>
            case pp of
                PermRefl => ?a -- absurd $ contra (xys = xys)
                PermIns _ _ _ => ?b
        Yes prf =>
            case pp of
                PermRefl => ?a -- permReflFromEq (xs ++ [v] ++ ys) (zs ++ [v] ++ ws) _
                PermIns _ _ _ => ?b

