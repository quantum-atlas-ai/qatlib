/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.PairLCMOrderRecovery
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Order recovery from two samples

This module gives finite counting and number-theoretic ingredients for recovering a modular
order from two independent samples. A quarter-fraction coprimality bound and an exact
least-common-multiple identity yield the explicit constant success bound in
`pair_fresh_success_constant`, in the order-finding setting of [CleveEtAl1998].

## Main statements

* `coprime_pair_fraction_quarter`: at least a quarter of the residue pairs satisfy the required
  coprimality condition.
* `pair_denominators_lcm`: the two reduced denominators recover the order.
* `pair_fresh_success_constant`: a constant lower bound for two fresh modular-order samples.

## References

* [Cleve et al., 1998][CleveEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators Classical
open Qatlib.Concepts.PeriodSampling.OrderRecovery

namespace Qatlib.Papers.QAlgorithms97.MainResults.OrderFinding

/-- For `r > 1`, the coprime-pair count is at least `r ^ 2 / 4` [CleveEtAl1998]. -/
theorem coprime_pair_fraction_quarter (r : ℕ) (hr : 1 < r) :
    (r : ℝ) ^ 2 / 4 ≤ (orderCoprimePairCount r : ℝ) :=
  coprime_order_pair_uniform_constant r hr

/-- If `gcd s t` is coprime to the positive modulus `r`, the least common multiple of `r / gcd s
r` and `r / gcd t r` equals `r` [CleveEtAl1998]. -/
theorem pair_denominators_lcm (r s t : ℕ) (hr : 0 < r) (hs : s < r) (ht : t < r)
    (hc : Nat.Coprime (Nat.gcd s t) r) :
    Nat.lcm (r / Nat.gcd s r) (r / Nat.gcd t r) = r :=
  reduced_order_pair_lcm_arithmetic r s t hr hs ht hc

/-- Under the stated modulus, order, and sampling-size hypotheses, two independent modular-order
samples decode the exact order with probability at least `(8 / π ^ 2) ^ 2 / 4`
[CleveEtAl1998]. -/
theorem pair_fresh_success_constant {N M : ℕ} [NeZero N] (a : (ZMod N)ˣ)
    (hM : 0 < M) (hN : 1 < N) (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M) :
    (∑ yz ∈ Finset.univ.filter (fun yz : Fin M × Fin M =>
        (pairLCMOrderDecode N M a yz).1 = some (orderOf a)),
        (modularOrderLaw N M a hM).prob yz.1 * (modularOrderLaw N M a hM).prob yz.2) ≥
      (8 / Real.pi ^ 2) ^ 2 / 4 :=
  pair_lcm_order_actual_fresh_success_bound N M a hM hN hr hsize

end Qatlib.Papers.QAlgorithms97.MainResults.OrderFinding
