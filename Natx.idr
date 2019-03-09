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
TotalOrderNat = TotalOrderInst Nat LTE isLTE lteTransitive lteAntisymmetric

public export
gteAntisymmetric : {a, b : Nat} -> Not (GTE a b) -> GTE b a
gteAntisymmetric {a} {b} notGTE = lteAntisymmetric {a=b} {b=a} notGTE

public export
isGTE : (m, n : Nat) -> Dec (GTE m n)
isGTE m n = isLTE n m

public export
gteTransitive : GTE n m -> GTE m p -> GTE n p
gteTransitive = flip lteTransitive

public export
TotalOrderNatRev : TotalOrder Nat GTE
TotalOrderNatRev = TotalOrderInst Nat GTE isGTE gteTransitive gteAntisymmetric
