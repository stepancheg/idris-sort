import Sort
import Natx
import Sorted
import PermSimple
import TotalOrderLite
import Listx

%default total

-- demo shortcut
export
sortNat : (i : List Nat) -> (o : List Nat ** (Sorted (lte Natx.totalOrderNat) o, PermSimple i o))
sortNat = Sort.sort

-- another demo shortcut
export
sortNatRev : (i : List Nat) -> (o : List Nat ** (Sorted (lte Natx.totalOrderNatRev) o, PermSimple i o))
sortNatRev = Sort.sort

export
sortListNat : List (List Nat) -> List (List Nat)
sortListNat l = Sort.sortSimple {t = totalOrderListLte} l
