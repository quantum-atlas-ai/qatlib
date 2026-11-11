/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicGcdDecoder

/-!
# Cyclic order recovery and decoder budgets

This module formalizes the cyclic order-recovery setting associated with Corollary 8. The
equality `source_corollary8_hidden_subgroup` identifies collisions of powers of an element of
order `r` with equality of exponents in `ZMod r`.

When `r` divides a positive sampling modulus `N`, `source_corollary8_cyclic_decoder_budget`
packages the recovery success bound, circuit query and gate counts, and the counted GCD decoder
bound.

The mathematical background is discussed in [CheungMosca2001].

## Main statements

* `source_corollary8_hidden_subgroup`: characterizes power collisions by residues modulo the
  order.
* `source_corollary8_cyclic_decoder_budget`: packages success probability and resource bounds.

## References

* [Cheung and Mosca, 2001][CheungMosca2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Papers.AbelianDecomp01.MainResults

/-- For an element of order `r`, two natural powers are equal exactly when their exponents have
equal images in `ZMod r`. See [Cheung and Mosca, Corollary 8][CheungMosca2001]. -/
lemma source_corollary8_hidden_subgroup {G : Type*} [Group G] (a : G) {r : ℕ}
    (hr : orderOf a = r) (x y : ℕ) :
    a ^ x = a ^ y ↔ (x : ZMod r) = (y : ZMod r) := by
  rw [pow_eq_pow_iff_modEq, hr, ZMod.natCast_eq_natCast_iff']
  rfl

/-- For positive `r ∣ N` equal to the order of `a`, and `m = Nat.log2 N + 1 + k`, package the
power-collision characterization with recovery probability at least `1 - 2 ^ (-k)` within
budget `m + 2`, query count `m + 2`, gate count `2 * m`, and counted GCD bound `m * (N +
1)`. See [Cheung and Mosca, Corollary 8][CheungMosca2001]. -/
theorem source_corollary8_cyclic_decoder_budget
    {G : Type*} [Group G] (a : G) {r N k : ℕ} [NeZero r]
    (hr : orderOf a = r) (hrpos : 0 < r) (hN : 0 < N) (hrdvd : r ∣ N) :
    (∀ x y : ℕ, a ^ x = a ^ y ↔ (x : ZMod r) = (y : ZMod r)) ∧
      (let m := Nat.log2 N + 1 + k
       (ENNReal.ofReal (1 - (2 : ℝ) ^ (-(k : ℤ))) ≤
          within (cyclicCountedRecovery N hN (fun x : Fin N => (x.val : ZMod r)) m)
            (m + 2) (fun out => out = some r)) ∧
        ((List.replicate m (cyclicSamplingCircuit (R := ZMod r) N)).map QueryCount).sum + 2
          = m + 2 ∧
        ((List.replicate m (cyclicSamplingCircuit (R := ZMod r) N)).map GateCount).sum
          = 2 * m ∧
        (∀ ω : Fin m → Fin N,
          (cyclicGcdCounted N (List.ofFn (fun i => (ω i).val))).2 ≤ m * (N + 1))) := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact source_corollary8_hidden_subgroup a hr x y
  · intro m
    have hcol : ∀ x y : Fin N,
        (fun x : Fin N => (x.val : ZMod r)) x = (fun y : Fin N => (y.val : ZMod r)) y
          ↔ x.val % r = y.val % r := by
      intro x y
      exact ZMod.natCast_eq_natCast_iff' x.val y.val r
    obtain ⟨hprob, hq, hg, hm, _⟩ :=
      cyclic_accessible_budget_and_measurements N r k hN
        (fun x : Fin N => (x.val : ZMod r)) hrpos hrdvd hcol
    exact ⟨hprob, hq, hg, hm⟩

end Qatlib.Papers.AbelianDecomp01.MainResults
