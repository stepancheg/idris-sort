module LTEAll

import PermSimple
-- Probably should be implemented with `Forall`
import Forall

%default total

-- Element is less or equal than all elements of the list
public export
data LTEAll : Nat -> List Nat -> Type
    where
        LTEAllEmpty : LTEAll v []
        LTEAllRec : (v : Nat) -> (a : Nat) -> LTE v a -> LTEAll v rem -> LTEAll v (a :: rem)

export
lteAll1 : LTE v x -> LTEAll v [x]
lteAll1 {v} {x} lteVX = LTEAllRec v x lteVX LTEAllEmpty

export
lteAllConcat : LTEAll v xs -> LTEAll v ys -> LTEAll v (xs ++ ys)
lteAllConcat {v} {xs = []}      {ys = []} LTEAllEmpty LTEAllEmpty = LTEAllEmpty
lteAllConcat {v} {xs = []}                _ lteAllYs = lteAllYs
lteAllConcat {v} {xs = x :: xs} {ys = []} lteAllXs _ = rewrite appendNilRightNeutral xs in lteAllXs
lteAllConcat {v} {xs = x :: xs} {ys}      (LTEAllRec v  x lteVX lteAllVXs) lteAllVYs =
    LTEAllRec v x lteVX (lteAllConcat lteAllVXs lteAllVYs)

lteAllSplit : LTEAll v (xs ++ ys) -> (LTEAll v xs, LTEAll v ys)
lteAllSplit {xs = []} {ys = []} LTEAllEmpty = (LTEAllEmpty, LTEAllEmpty)
lteAllSplit {xs = xxs} {ys} r @ LTEAllRec =
    case xxs of
        [] => (LTEAllEmpty, r)
        x :: xs =>
            case r of
                LTEAllEmpty impossible
                LTEAllRec v x lte_v_x lteAll_xs_ys =>
                    let (lteAll_xs, lteAll_ys) = lteAllSplit lteAll_xs_ys in
                    let lteAll_x_xs = lteAllConcat (lteAll1 lte_v_x) lteAll_xs in
                    (lteAll_x_xs, lteAll_ys)

lteAllSmaller : LTE a b -> LTEAll b l -> LTEAll a l
lteAllSmaller {a} {b} {l = []} lteAB LTEAllEmpty = LTEAllEmpty
lteAllSmaller {a} {b} {l = c :: rem} lteAB (LTEAllRec b c lteBC lteAllBRem) =
    LTEAllRec a c (lteTransitive lteAB lteBC) (lteAllSmaller lteAB lteAllBRem)

lteAllSmaller_f : LTE a b -> Forall (LTE b) xs -> Forall (LTE a) xs
lteAllSmaller_f lte_a_b = forallMap (\x, lte_b_x => lteTransitive lte_a_b lte_b_x)

export
lteAllPrepend : LTE a b -> LTEAll b l -> LTEAll a (b :: l)
lteAllPrepend {a} {b} {l} lteAB lteAllBL =
    lteAllConcat (lteAll1 lteAB) (lteAllSmaller lteAB lteAllBL)

export
lteAllPrepend_f : LTE a b -> Forall (LTE b) xs -> Forall (LTE a) (b :: xs)
lteAllPrepend_f lte_a_b fa_lte_b_xs =
    forallConcat (forall1 lte_a_b) (lteAllSmaller_f lte_a_b fa_lte_b_xs)

export
lteAllTrans : LTEAll m as -> PermSimple as bs -> LTEAll m bs
lteAllTrans LTEAllEmpty PermSimpleEmpty = LTEAllEmpty
lteAllTrans {m} lteAll_as (PermSimpleIns p {v} {xs} {ys} {zs} {ws}) =
    let (lteAll_xs, lteAll_v_ys) = lteAllSplit lteAll_as {xs = xs} {ys = v :: ys} in
    let (lteAll_v, lteAll_ys) = lteAllSplit lteAll_v_ys {xs = [v]} {ys = ys} in
    let lteAll_xs_ys = lteAllConcat lteAll_xs lteAll_ys in
    let lteAll_zs_ws = lteAllTrans lteAll_xs_ys p in
    let (lteAll_zs, lteAll_ws) = lteAllSplit lteAll_zs_ws {xs = zs} {ys = ws} in
    let lteAll_v_ws = lteAllConcat lteAll_v lteAll_ws in
    let lteAll_zs_v_ws = lteAllConcat lteAll_zs lteAll_v_ws in
    lteAll_zs_v_ws

