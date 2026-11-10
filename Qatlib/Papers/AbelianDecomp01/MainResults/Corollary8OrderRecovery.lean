/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicGcdDecoder
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Papers.AbelianDecomp01.MainResults

lemma source_corollary8_hidden_subgroup {G : Type*} [Group G] (a : G) {r : ℕ}
    (hr : orderOf a = r) (x y : ℕ) :
    a ^ x = a ^ y ↔ (x : ZMod r) = (y : ZMod r) := by
  rw [pow_eq_pow_iff_modEq, hr, ZMod.natCast_eq_natCast_iff']
  rfl

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
