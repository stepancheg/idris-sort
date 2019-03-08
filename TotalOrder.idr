module TotalOrder

%default total

public export
data TotalOrder : (a : Type) -> (a -> a -> Type) -> Type where
    TotalOrderInst :
        (a : Type)
        -> (lte : a -> a -> Type) -- <=
        -> ((x, y, z : a) -> lte x y -> lte y z -> lte x z) -- transitivity
        -> ((x, y : a) -> Dec (lte x y)) -- isLTE
        -> ((x, y : a) -> Not (lte x y) -> lte y x) -- antisymmetry
        -> TotalOrder a lte

public export
natLteTrans : (x, y, z: Nat) -> LTE x y -> LTE y z -> LTE x z
natLteTrans _ _ _ = lteTransitive

public export
natLteCmpSucc : Either (LTE x y) (LTE y x) -> Either (LTE (S x) (S y)) (LTE (S y) (S x))
natLteCmpSucc (Left c) = Left $ LTESucc c
natLteCmpSucc (Right c) = Right $ LTESucc c

public export
natLteAntisymmetric : (a, b : Nat) -> Not (LTE a b) -> LTE b a
natLteAntisymmetric Z _ notLTE = absurd (notLTE LTEZero)
natLteAntisymmetric (S k) Z notLTE = LTEZero
natLteAntisymmetric (S k) (S j) notLTE = LTESucc (natLteAntisymmetric k j (notLTE . LTESucc))

public export
TotalOrderNat : TotalOrder Nat LTE
TotalOrderNat = TotalOrderInst Nat LTE natLteTrans isLTE natLteAntisymmetric
