/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueAttemptSuccessStat
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueGcdBranchShor
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.SampledAttemptSuccessShor

/-!
# Success of residue-based factoring attempts

Splits the single-attempt residue success mass into the classical gcd contribution and the
accepted-unit contribution. This decomposition proves `residueAttemptSuccess`, including
soundness of both branches, in the factoring probability model associated with [Shor1997].

## Main statements

* `residue_single_mass_split`: Decomposes the success mass into gcd and unit-attempt terms.
* `residueAttemptSuccess`: Establishes the one-attempt residue success contract.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.RiskEstimation.PopulationGap
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib
open scoped Classical

/-- The number of units modulo nonzero `N` is at most `N`. -/
private theorem residue_units_card_le (N : ℕ) [NeZero N] : Fintype.card (ZMod N)ˣ ≤ N := by
  rw [← residue_coprime_card N]
  exact (Finset.card_filter_le _ _).trans_eq (ZMod.card N)

/-- The single residue-attempt success probability equals `residueGcdProperCount N / 2 ^ k` plus
the corresponding unit-based attempt success probability. -/
theorem residue_single_mass_split (N M k : ℕ) [NeZero N] (hM : 0 < M)
    (hk : N ≤ 2^k) :
    (residueAttemptLaw N M k hM hk).probEvent (L := 1)
      (fun ω => residueAttemptSuccessEvent N M k (ω 0)) =
    (residueGcdProperCount N : ℝ)/2^k +
    (attemptLaw N M k hM ((residue_units_card_le N).trans hk)).probEvent (L := 1)
      (fun ω => attemptSuccess N M k (ω 0)) := by
  have hclass : (∑ y : ZMod N, if (residueClassicalFactor N y).isSome then
      residueAttemptMass N M k hM (Sum.inr (Sum.inl y)) else 0) =
      (residueGcdProperCount N : ℝ)/2^k := by
    have he (y : ZMod N) : (if (residueClassicalFactor N y).isSome then
        residueAttemptMass N M k hM (Sum.inr (Sum.inl y)) else 0) =
      if 1 < Nat.gcd y.val N ∧ Nat.gcd y.val N < N then (2^k : ℝ)⁻¹ else 0 := by
      by_cases h : 1 < Nat.gcd y.val N ∧ Nat.gcd y.val N < N
      · have hc : ¬ Nat.Coprime y.val N := by
          intro hc
          have hg := hc.gcd_eq_one
          omega
        simp [residueClassicalFactor, h, residueAttemptMass, hc]
      · simp [residueClassicalFactor, h]
    simp_rw [he]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    dsimp [residueGcdProperCount]
    rw [div_eq_mul_inv]
  rw [singleEvent_mass, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [residueAttemptSuccessEvent, ↓reduceIte, Finset.sum_const_zero, zero_add]
  simp only [residueAttemptLaw]
  rw [hclass, singleEvent_mass, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [attemptSuccess, ↓reduceIte, Finset.sum_const_zero, zero_add]
  rfl

/-- Establishes the residue-attempt success lower bound and soundness of the classical gcd and
unit-based factor outputs in the probability model associated with [Shor1997]. -/
theorem residueAttemptSuccess : ResidueAttemptSuccess := by
  intro N M k _ hM hk hN hodd hs hsize
  have hu := (residue_units_card_le N).trans hk
  have hq := sampledAttemptSuccess N M k hM hu hN hodd hs hsize
  refine ⟨?_, residue_classical_factor_sound N, attemptFactor_sound N M⟩
  rw [residue_single_mass_split]
  have he : shorResidueAttemptBound N k =
      (residueGcdProperCount N : ℝ)/2^k+shorAttemptBound N k := by
    unfold shorResidueAttemptBound shorAttemptBound
    ring
  rw [he]
  exact add_le_add le_rfl hq.1

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
