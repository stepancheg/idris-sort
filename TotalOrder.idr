module TotalOrder

%default total

public export
data TotalOrder : (a : Type) -> (a -> a -> Type) -> Type where
    TotalOrderInst :
        (a : Type)
        -> (lte : a -> a -> Type)
        -> ((x, y, z : a) -> lte x y -> lte y z -> lte x z)
        -> ((x, y : a) -> Either (lte x y) (lte y x))
        -> TotalOrder a lte

public export
natLteTrans : (x, y, z: Nat) -> LTE x y -> LTE y z -> LTE x z
natLteTrans _ _ _ = lteTransitive

public export
natLteCmpSucc : Either (LTE x y) (LTE y x) -> Either (LTE (S x) (S y)) (LTE (S y) (S x))
natLteCmpSucc (Left c) = Left $ LTESucc c
natLteCmpSucc (Right c) = Right $ LTESucc c

public export
natLteCmp : (x, y : Nat) -> Either (LTE x y) (LTE y x)
natLteCmp Z _ = Left LTEZero
natLteCmp _ Z = Right LTEZero
natLteCmp (S x) (S y) = natLteCmpSucc $ natLteCmp x y

public export
TotalOrderNat : TotalOrder Nat LTE
TotalOrderNat = TotalOrderInst Nat LTE natLteTrans natLteCmp
