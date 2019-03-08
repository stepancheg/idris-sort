-- Nat extensions
module Natx

import TotalOrder

%default total

public export
lteAntisymmetric : {a, b : Nat} -> Not (LTE a b) -> LTE b a
lteAntisymmetric {a = Z} notLTE = absurd (notLTE LTEZero)
lteAntisymmetric {a = S k} {b = Z} notLTE = LTEZero
lteAntisymmetric {a = S k} {b = S j} notLTE = LTESucc (lteAntisymmetric {a=k} {b=j} (notLTE . LTESucc))

public export
TotalOrderNat : TotalOrder Nat LTE
TotalOrderNat = TotalOrderInst Nat LTE lteTransitive isLTE lteAntisymmetric
