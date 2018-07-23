module PermSimpleForall

import PermSimple
import Forall

%default total

-- Permutation preserves forall property
export
forallPermSimple : Forall m as -> PermSimple as bs -> Forall m bs
forallPermSimple ForallEmpty PermSimpleEmpty = ForallEmpty
forallPermSimple {m} fa_as (PermSimpleIns p {v} {xs} {ys} {zs} {ws}) =
    let (fa_xs, fa_v_ys) = forallSplit fa_as {xs = xs} {ys = v :: ys} in
    let (fa_v, fa_ys) = forallSplit fa_v_ys {xs = [v]} {ys = ys} in
    let fa_xs_ys = forallConcat fa_xs fa_ys in
    let fa_zs_ws = forallPermSimple fa_xs_ys p in
    let (fa_zs, fa_ws) = forallSplit fa_zs_ws {xs = zs} {ys = ws} in
    let fa_v_ws = forallConcat fa_v fa_ws in
    let fa_zs_v_ws = forallConcat fa_zs fa_v_ws in
    fa_zs_v_ws
