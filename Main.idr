import Sort
import Natx
import Sorted
import PermSimple
import TotalOrderLite
import Listx

%default total

-- demo shortcut
export
sortNat : (i : List Nat) -> (o : List Nat ** (Sorted LTEX o, PermSimple i o))
sortNat = Sort.sort {to = totalOrderNat}

-- another demo shortcut
export
sortNatRev : (i : List Nat) -> (o : List Nat ** (Sorted Rev_LTEX o, PermSimple i o))
sortNatRev = Sort.sort {to = totalOrderNatRev}

export
sortListNat : List (List Nat) -> List (List Nat)
sortListNat l = Sort.sortSimple {to = totalOrderListLte} l
