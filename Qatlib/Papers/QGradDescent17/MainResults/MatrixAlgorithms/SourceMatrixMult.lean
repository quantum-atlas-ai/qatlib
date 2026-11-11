/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# `QGradDescent17.MainResults.MatrixAlgorithms` — Theorem IV.7

Kerenidis--Prakash, fixed arXiv:1704.04992v5.

Theorem IV.7 (p. 22): for a matrix `A` and its inverse `A⁻¹`, Algorithm IV.2
outputs states `|z⟩` with `‖|Ax⟩ − |z⟩‖ ≤ δ` (and `‖|A⁻¹x⟩ − |z⟩‖ ≤ δ`) in time
`Õ(κ² μ / δ)`, where `κ` is the condition number.

Formalised: the error propagation from the residual `‖Ax − z‖ ≤ ε₁‖x‖` to the
normalised-state distance `√2 ε₁ κ`, which is the quantitative heart of the
theorem (it combines Claim II.3 with the condition-number bound
`‖x‖ ≤ κ‖Ax‖`), plus the `Õ(κ²μ/δ)` cost form.  The circuit construction and the
second (`A⁻¹`) error bound are recorded in the docstring / PR table.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QGradDescent17.MainResults.MatrixAlgorithms

open scoped RealInnerProductSpace BigOperators

/-- Coarse soft-`O`: `f` is at most a polynomial in `1 + g`. -/
def SoftBigO (f g : ℝ) : Prop := ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ f ≤ C * (1 + g) ^ D

/-- A nonnegative cost is bounded by itself in the polynomial overhead relation. -/
theorem softBigO_self {g : ℝ} (hg : 0 ≤ g) : SoftBigO g g := by
  refine ⟨1, 1, one_pos, ?_⟩
  rw [pow_one]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Arithmetic core of Claim II.3 (restated; see `SourceNormBridge`). -/
theorem normalizedDistance_sq_le {R S c : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hc : 0 ≤ c) (hc_le : c ≤ R * S) :
    2 - 2 * (c / (R * S)) ≤ 2 * (R ^ 2 + S ^ 2 - 2 * c) / R ^ 2 := by
  set t : ℝ := c / (R * S) with ht_def
  have hRS : 0 < R * S := mul_pos hR hS
  have ht0 : 0 ≤ t := div_nonneg hc (le_of_lt hRS)
  have ht1 : t ≤ 1 := by
    rw [ht_def, div_le_one hRS]
    exact hc_le
  have hmul : 0 ≤ t * (1 - t) * R ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg R)
  have hsq : 0 ≤ (S - t * R) ^ 2 := sq_nonneg _
  have hct : c = t * (R * S) := by
    rw [ht_def]
    field_simp
  have hR2 : 0 < R ^ 2 := by positivity
  rw [le_div_iff₀ hR2]
  nlinarith [hmul, hsq, hct]

/-- **Claim II.3** (p. 10, eq. (6)), restated for the error-propagation step. -/
theorem claimII3_normalized_distance (phi phit : E) (hphi : phi ≠ 0) (hphit : phit ≠ 0)
    (hcos : 0 ≤ ⟪phi, phit⟫) (hangle : ⟪phi, phit⟫ ≤ ‖phi‖ * ‖phit‖) :
    ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ≤
      Real.sqrt 2 * ‖phi - phit‖ / ‖phi‖ := by
  set R : ℝ := ‖phi‖ with hRdef
  set S : ℝ := ‖phit‖ with hSdef
  set c : ℝ := ⟪phi, phit⟫ with hcdef
  have hR : 0 < R := by rw [hRdef]; exact norm_pos_iff.mpr hphi
  have hS : 0 < S := by rw [hSdef]; exact norm_pos_iff.mpr hphit
  have hc : 0 ≤ c := by rw [hcdef]; exact hcos
  have hc_le : c ≤ R * S := by rw [hcdef, hRdef, hSdef]; exact hangle
  have hnv : ‖NormedSpace.normalize phi‖ = 1 := NormedSpace.norm_normalize hphi
  have hnw : ‖NormedSpace.normalize phit‖ = 1 := NormedSpace.norm_normalize hphit
  have hin : ⟪NormedSpace.normalize phi, NormedSpace.normalize phit⟫ = c / (R * S) := by
    rw [hcdef, hRdef, hSdef, NormedSpace.normalize, NormedSpace.normalize,
      real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hLHS : ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ^ 2 =
      2 - 2 * (c / (R * S)) := by
    rw [norm_sub_sq_real, hnv, hnw, hin]
    ring
  have hnorm : ‖phi - phit‖ ^ 2 = R ^ 2 + S ^ 2 - 2 * c := by
    rw [norm_sub_sq_real, ← hRdef, ← hSdef, ← hcdef]
    ring
  have hRHS : (Real.sqrt 2 * ‖phi - phit‖ / R) ^ 2 =
      2 * (R ^ 2 + S ^ 2 - 2 * c) / R ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hnorm]
  have hsqle : ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ^ 2 ≤
      (Real.sqrt 2 * ‖phi - phit‖ / R) ^ 2 := by
    rw [hLHS, hRHS]
    exact normalizedDistance_sq_le hR hS hc hc_le
  calc ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖
      = Real.sqrt (‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt 2 * ‖phi - phit‖ / R) ^ 2) := Real.sqrt_le_sqrt hsqle
    _ = Real.sqrt 2 * ‖phi - phit‖ / R := Real.sqrt_sq (by positivity)
    _ = Real.sqrt 2 * ‖phi - phit‖ / ‖phi‖ := by rw [hRdef]

/-- **Theorem IV.7, error propagation** (p. 22).  If the computed state `z`
satisfies the residual bound `‖Ax − z‖ ≤ ε₁‖x‖` and `x` obeys the
condition-number bound `‖x‖ ≤ κ‖Ax‖` (i.e. `κ ≥ ‖A‖‖A⁻¹‖`), then the normalised
output is `√2 ε₁ κ`-close to `|Ax⟩`. -/
theorem theorem_IV_7_normalized_error (Ax z x : E) (hne : Ax ≠ 0) (hzn : z ≠ 0)
    (hcos : 0 ≤ ⟪Ax, z⟫) (ε₁ κ : ℝ) (hε : 0 ≤ ε₁)
    (hres : ‖Ax - z‖ ≤ ε₁ * ‖x‖) (hcond : ‖x‖ ≤ κ * ‖Ax‖) :
    ‖NormedSpace.normalize Ax - NormedSpace.normalize z‖ ≤ Real.sqrt 2 * ε₁ * κ := by
  have hAx : 0 < ‖Ax‖ := norm_pos_iff.mpr hne
  have h1 := claimII3_normalized_distance Ax z hne hzn hcos (real_inner_le_norm _ _)
  have hdiv : ‖x‖ / ‖Ax‖ ≤ κ := by
    rw [div_le_iff₀ hAx]
    exact hcond
  calc ‖NormedSpace.normalize Ax - NormedSpace.normalize z‖
      ≤ Real.sqrt 2 * ‖Ax - z‖ / ‖Ax‖ := h1
    _ ≤ Real.sqrt 2 * (ε₁ * ‖x‖) / ‖Ax‖ :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hres (Real.sqrt_nonneg 2)) (norm_nonneg _)
    _ = Real.sqrt 2 * ε₁ * (‖x‖ / ‖Ax‖) := by
        field_simp
    _ ≤ Real.sqrt 2 * ε₁ * κ :=
        mul_le_mul_of_nonneg_left hdiv
          (mul_nonneg (Real.sqrt_nonneg 2) hε)

/-- The cost of Theorem IV.7, `Õ(κ² μ / δ)`. -/
def qlsCost (κ μ δ : ℝ) : ℝ := κ ^ 2 * μ / δ

/-- The matrix multiplication cost satisfies the polynomial overhead estimate of Theorem IV.7. -/
theorem theorem_IV_7_cost (κ μ δ : ℝ) (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    SoftBigO (qlsCost κ μ δ) (κ ^ 2 * μ / δ) :=
  softBigO_self (div_nonneg (mul_nonneg (sq_nonneg κ) hμ) (le_of_lt hδ))

end Qatlib.Papers.QGradDescent17.MainResults.MatrixAlgorithms
