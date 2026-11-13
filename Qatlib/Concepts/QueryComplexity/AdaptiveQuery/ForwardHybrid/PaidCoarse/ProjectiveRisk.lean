/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OperatorErrors.OperatorError
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Operator norm distance to a phase orbit

This module defines the global phase orbit `phaseOrbit V` and the distance `dpo U V` from `U` to
that orbit in operator norm. It proves nonnegativity, vanishing for phase multiples, and
Lipschitz continuity in the first argument.

For unitary matrices the distance is at most two, and its square has Lipschitz constant four.
The phase orbit construction reflects the global phase equivalence of quantum gates described in
[NielsenChuang2010].

## Main statements

* `dpo_phase_smul`: a global phase multiple has zero distance to the original matrix's orbit.
* `dpo_lipschitz_left`: the distance is one Lipschitz in its first argument.
* `dpo_sq_lipschitz_left_of_unitary`: the squared distance is four Lipschitz on unitary
  matrices.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse

open Matrix
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The set of scalar multiples of `V` by complex numbers of unit modulus. -/
def phaseOrbit (V : Matrix (Fin d) (Fin d) ℂ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  Set.range (fun z : unitary ℂ => (z : ℂ) • V)

/-- The operator norm distance from `U` to the global phase orbit of `V`. -/
noncomputable def dpo (U V : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Metric.infDist U (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.phaseOrbit V)

/-- The distance to a global phase orbit is nonnegative. -/
theorem dpo_nonneg (U V : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V := by
  exact Metric.infDist_nonneg

/-- A matrix has zero distance to its own global phase orbit. -/
@[simp] theorem dpo_self (U : Matrix (Fin d) (Fin d) ℂ) : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U U = 0 := by
  apply Metric.infDist_zero_of_mem
  exact ⟨1, by simp⟩

/-- A unit modulus scalar multiple of `V` has zero distance to the phase orbit of `V`. -/
@[simp] theorem dpo_phase_smul (z : unitary ℂ) (V : Qatlib.Foundations.PureStateMath.Operator d) :
    Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo ((z : ℂ) • V) V = 0 := by
  exact Metric.infDist_zero_of_mem ⟨z, rfl⟩

/-- Changing the first matrix changes its distance to a fixed phase orbit by at most the
operator norm of the matrix difference. -/
theorem dpo_lipschitz_left (U U' V : Matrix (Fin d) (Fin d) ℂ) :
    |dpo U V - Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V| ≤ ‖U - U'‖ := by
  have h₁ := Metric.infDist_le_infDist_add_dist
    (x := U) (y := U') (s := Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.phaseOrbit V)
  have h₂ := Metric.infDist_le_infDist_add_dist
    (x := U') (y := U) (s := Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.phaseOrbit V)
  have h₁' : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V ≤ Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V + ‖U - U'‖ := by
    simpa [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo,
        dist_eq_norm] using h₁
  have h₂' : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V ≤ Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V + ‖U - U'‖ := by
    simpa [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo,
        dist_eq_norm, norm_sub_rev] using h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The distance from one unitary matrix to the phase orbit of another is at most two. -/
theorem dpo_le_two_of_unitary (U V : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V ≤ 2 := by
  have hmem : ((1 : unitary ℂ) : ℂ) • V ∈ Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.phaseOrbit V :=
    ⟨1, rfl⟩
  calc
    Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V ≤ dist U (((1 : unitary ℂ) : ℂ) • V) :=
      Metric.infDist_le_dist_of_mem hmem
    _ = ‖U - V‖ := by simp [dist_eq_norm]
    _ ≤ ‖U‖ + ‖V‖ := norm_sub_le _ _
    _ ≤ 2 := by
      linarith [Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hU, Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hV]

/-- For unitary matrices, changing the first matrix changes the squared distance to a fixed
phase orbit by at most four times the operator norm of the matrix difference. -/
theorem dpo_sq_lipschitz_left_of_unitary
    (U U' V : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hU' : U' ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    |(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V)^2 - (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V)^2| ≤ 4 * ‖U - U'‖ := by
  have hU0 :=
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo_nonneg U V
  have hU'0 :=
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo_nonneg U' V
  have hU2 :=
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo_le_two_of_unitary U V hU hV
  have hU'2 :=
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo_le_two_of_unitary U' V hU' hV
  have hdist :=
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo_lipschitz_left U U' V
  have hsum :
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V + Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V ≤ 4 := by linarith
  have hfactor : (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V)^2 - (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V)^2 =
      (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V - Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V) * (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V + Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg (add_nonneg hU0 hU'0)]
  calc
    |dpo U V - Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V| * (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V + Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V)
        ≤ ‖U - U'‖ * (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U V + Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.dpo U' V) :=
          mul_le_mul_of_nonneg_right hdist (add_nonneg hU0 hU'0)
    _ ≤ ‖U - U'‖ * 4 :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 4 * ‖U - U'‖ := by ring

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse
