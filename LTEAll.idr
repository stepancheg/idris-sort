module LTEAll

import PermSimple

%default total

-- Element is less or equal than all elements of the list
public export
data LTEAll : Nat -> List Nat -> Type
    where
        LTEAllEmpty : (v : Nat) -> LTEAll v []
        LTEAllRec : (v : Nat) -> (a : Nat) -> LTE v a -> LTEAll v rem -> LTEAll v (a :: rem)

export
lteAll1 : LTE v x -> LTEAll v [x]
lteAll1 {v} {x} lteVX = LTEAllRec v x lteVX (LTEAllEmpty v)

export
lteAllConcat : LTEAll v xs -> LTEAll v ys -> LTEAll v (xs ++ ys)
lteAllConcat {v} {xs = []}      {ys = []} (LTEAllEmpty v) (LTEAllEmpty v) = LTEAllEmpty v
lteAllConcat {v} {xs = []}                _ lteAllYs = lteAllYs
lteAllConcat {v} {xs = x :: xs} {ys = []} lteAllXs _ = rewrite appendNilRightNeutral xs in lteAllXs
lteAllConcat {v} {xs = x :: xs} {ys}      (LTEAllRec v  x lteVX lteAllVXs) lteAllVYs =
    LTEAllRec v x lteVX (lteAllConcat lteAllVXs lteAllVYs)

lteAllSmaller : LTE a b -> LTEAll b l -> LTEAll a l
lteAllSmaller {a} {b} {l = []} lteAB (LTEAllEmpty b) = LTEAllEmpty a
lteAllSmaller {a} {b} {l = c :: rem} lteAB (LTEAllRec b c lteBC lteAllBRem) =
    LTEAllRec a c (lteTransitive lteAB lteBC) (lteAllSmaller lteAB lteAllBRem)

export
lteAllPrepend : LTE a b -> LTEAll b l -> LTEAll a (b :: l)
lteAllPrepend {a} {b} {l} lteAB lteAllBL =
    lteAllConcat (lteAll1 lteAB) (lteAllSmaller lteAB lteAllBL)

export
lteAllTrans : LTEAll a xs -> PermSimple xs ys -> LTEAll a ys
