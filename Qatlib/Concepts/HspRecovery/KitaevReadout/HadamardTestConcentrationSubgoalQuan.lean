/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.HadamardTestConcentrationSubgoalStat
import Qatlib.Concepts.HspRecovery.KitaevReadout.HadamardTestBitLawSubgoalQuan

/-!
# Concentration of Hadamard test bit averages

This module proves `HadamardTestConcentrationSubgoal` by identifying the expectation of
`hadamardBitDist` and applying a finite independent-sample concentration bound. It supplies the
statistical estimate used by the phase readout construction of [Kitaev1995].

## Main statements

* `hadamardBitDist_expect`: the mean of the true-bit indicator.
* `hadamardTestConcentrationSubgoal`: the deviation probability bound under the specified
  sample-size condition.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.HspRecovery.KitaevReadout
open scoped BigOperators

/-- The expectation of the true-bit indicator under `hadamardBitDist φ` is `(1 - cos (2πφ)) /
2`. -/
theorem hadamardBitDist_expect (φ : ℝ) :
    (hadamardBitDist φ).expect (fun b => if b then (1 : ℝ) else 0) =
      (1 - Real.cos (2 * Real.pi * φ)) / 2 := by
  simpa [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Fintype.sum_bool, hadamardBitDist] using
    (hadamardTestBitState_born φ).2

/-- Proves the Hadamard bit average deviation bound with failure probability at most `ε` when
the sample size is at least `log (2 / ε) / (2 * τ^2)`. -/
theorem hadamardTestConcentrationSubgoal : HadamardTestConcentrationSubgoal := by
  classical
  intro φ s τ ε hτ hε hε1 hsize
  have hlog : 0 < Real.log (2 / ε) :=
    Real.log_pos ((lt_div_iff₀ hε).mpr (by linarith))
  have hsR : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hsize
  have hs : 0 < s := by exact_mod_cast hsR
  have hsq : Real.log (2 / ε) / (2 * (s : ℝ)) ≤ τ ^ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * τ ^ 2)).mp hsize
    nlinarith
  have hroot : Real.sqrt (1 ^ 2 * Real.log (2 / ε) / (2 * (s : ℝ))) ≤ τ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hτ.le, by simpa using hsq⟩
  have htail := finite_iid_bounded_average_tail (hadamardBitDist φ)
    (fun b => if b then (1 : ℝ) else 0) s 1 ε hs (by norm_num) hε hε1
    (by intro b; cases b <;> norm_num)
  rw [hadamardBitDist_expect] at htail
  refine le_trans ?_ htail
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hroot.trans hω
  · intro ω _ _
    exact Finset.prod_nonneg (fun i _ => (hadamardBitDist φ).nonneg (ω i))

end Qatlib.Concepts.HspRecovery.KitaevReadout
