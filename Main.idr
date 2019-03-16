import Sort
import NatTotalOrder
import Sorted
import PermSimple
import TotalOrderLite
import ListTotalOrder

%default total

-- demo shortcut
export
sortNat : (i : List Nat) -> (o : List Nat ** (Sorted (lte NatTotalOrder.totalOrderLiteNat) o, PermSimple i o))
sortNat = Sort.sort {t = NatTotalOrder.totalOrderLiteNat}

-- another demo shortcut
export
sortNatRev : (i : List Nat) -> (o : List Nat ** (Sorted (lte NatTotalOrder.totalOrderLiteNatRev) o, PermSimple i o))
sortNatRev = Sort.sort {t = NatTotalOrder.totalOrderLiteNatRev}

export
sortListNat : List (List Nat) -> List (List Nat)
sortListNat l = Sort.sortSimple {t = totalOrderListLte} l
