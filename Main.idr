import Sort
import Natx
import Sorted
import PermSimple
import TotalOrder

%default total

-- demo shortcut
export
sortNat : (i : List Nat) -> (o : List Nat ** (Sorted LTE o, PermSimple i o))
sortNat = Sort.sort {to = totalOrderNat}

-- another demo shortcut
export
sortNatRev : (i : List Nat) -> (o : List Nat ** (Sorted GTE o, PermSimple i o))
sortNatRev = Sort.sort {to = totalOrderNatRev}
