/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
import Qatlib.Concepts.QueryComplexity.NormObstruction.Lemma33FactorizationToAlgorithmQuan

/-!
# Unitary dilation of a normalized linear map

Proves the finite-dimensional dilation statement of Lemma 3.3 in [AradLandau2010]. For a nonzero
complex matrix `A`, normalization by its Euclidean operator norm produces a contraction that can
be embedded as the first block of a unitary on a doubled index space.

The theorem `lemma3_3_unitary_dilation` states the action on vectors supported in the first
summand and supplies a matrix for the remaining output block.

## Main statements

* `lemma3_3_unitary_dilation`: constructs the unitary and its action on the first summand.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option warningAsError false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Lemma33

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {R : Type} [Fintype R] [DecidableEq R]

set_option maxHeartbeats 4000000 in

/-- Every nonzero finite complex matrix `A` has a unitary dilation on the doubled index space
whose first output block on `Sum.elim α 0` is `‖A‖⁻¹` times `A *ᵥ α`. See [AradLandau2010]. -/
theorem lemma3_3_unitary_dilation (A : Matrix R R ℂ) (hA : A ≠ 0) :
    ∃ (U : Matrix (R ⊕ R) (R ⊕ R) ℂ) (S : Matrix R R ℂ),
      U ∈ Matrix.unitaryGroup (R ⊕ R) ℂ ∧
        ∀ α : R → ℂ,
          U *ᵥ Sum.elim α 0
            = Sum.elim ((((‖A‖)⁻¹ : ℝ) : ℂ) • (A *ᵥ α)) (S *ᵥ α) := by

  have hpos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hScalar : ‖(((‖A‖)⁻¹ : ℝ) : ℂ)‖ = (‖A‖)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  have hnorm : ‖(((‖A‖)⁻¹ : ℝ) : ℂ) • A‖ = (‖A‖)⁻¹ * ‖A‖ := by
    rw [norm_smul, hScalar]
  have hM : ‖(((‖A‖)⁻¹ : ℝ) : ℂ) • A‖ ≤ 1 := by
    rw [hnorm]
    exact le_of_eq (inv_mul_cancel₀ hpos.ne')
  obtain ⟨U, S, hU, hact⟩ :=
    Qatlib.Concepts.QueryComplexity.NormObstruction.contraction_unitary_dilation
      ((((‖A‖)⁻¹ : ℝ) : ℂ) • A) hM
  refine ⟨U, S, hU, fun α => ?_⟩
  rw [hact α, Matrix.smul_mulVec]

end Qatlib.Papers.TensorNetwork08.MainResults.Lemma33
