/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SubHypergraph13.MainResults.SourceModel

@[expose] public section


/-! Counterexamples to the legacy degree-regularity domain and cost indexing.
The source paper imposes admissibility and uses one-based schedule indices. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Papers.SubHypergraph13.MainResults

namespace Qatlib.Papers.SubHypergraph13.MainResults

/-- The old Lemma 8 admits a requested subset size larger than its universe. -/
theorem lemma8_false :
    ¬ (1 - 2 * (1 : ℝ) * Real.exp (-(40 : ℝ) / (8 * 1)) -
        2 * (1 : ℝ) * Real.exp (-(40 : ℝ) / (8 * 1)) -
        (1 : ℝ) * 1 * 0 * (1 / 2 : ℝ) ^ (11 * 40 * 0 / (1 * 1 * 1)) ≤
      uniformEventProb ((Finset.univ : Finset (Fin 1 × Fin 1)).powersetCard 40)
        (fun Fij => degreeRegular 40 Fij ∧
          pairTripleBound 40 0 Fij (∅ : Finset (Fin 1 × Fin 1)) ∅)) := by
  have hempty : ((Finset.univ : Finset (Fin 1 × Fin 1)).powersetCard 40) = ∅ := by
    rw [Finset.powersetCard_eq_empty]
    norm_num
  rw [hempty]
  norm_num [uniformEventProb]
  have hx := Real.add_one_le_exp (5 : ℝ)
  have he : Real.exp (-5) < (1 : ℝ) / 4 := by
    rw [Real.exp_neg]
    have he5 : (4 : ℝ) < Real.exp 5 := by linarith
    have hdiv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) he5
    simpa using hdiv
  linarith

/-- The final one-based level lies outside the zero-based Fin schedule model. -/
theorem final_level_zero {κ m : ℕ} (σ : Fin m → ScheduleItem κ)
    (P : Parameters κ) (n : ℕ) :
    epsAt σ P n m = 0 ∧ deltaAt σ P m = 0 := by
  simp [epsAt, deltaAt]

/-- A one-level vertex walk has zero cost in the legacy expression. -/
theorem one_level_zero (P : Parameters 1) (n : ℕ) :
    nestedWalkCost (completeHypergraph 1)
      (fun _ : Fin 1 => ScheduleItem.vertex 0) P n = 0 := by
  simp [nestedWalkCost, setupCost, epsAt, deltaAt]

end Qatlib.Papers.SubHypergraph13.MainResults
