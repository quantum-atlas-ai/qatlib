/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QEigenProc24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Real Part of the Numerical Range Equals Numerical Range of the Hermitian Part

This module proves Proposition 34: for any `d × d` complex matrix `C`, the set of
real parts of elements in the numerical range `W(C)` coincides with the numerical
range `W(ℜ(C))` of its Hermitian part `ℜ(C) = (C + Cᴴ) / 2`.

## Main statements

* `real_part_numerical_range`: `realPartNumericalRange C = {t : ℝ | (t : ℂ) ∈ numericalRange (hermitianPart C)}`.

## References

* [Low and Su, 2024][LowSu2024QEigenProc], Proposition 34, Eq. (472), p. 101.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace

namespace Qatlib.Papers.QEigenProc24.MainResults.NumericalRange

open Qatlib.Papers.QEigenProc24.MainResults

private lemma inner_hermitianPart {d : ℕ} (C : Op d) (x : Vec d) :
    ⟪x, applyOp (hermitianPart C) x⟫_ℂ = ((⟪x, applyOp C x⟫_ℂ).re : ℂ) := by
  have hstar : ⟪x, applyOp Cᴴ x⟫_ℂ = star ⟪x, applyOp C x⟫_ℂ := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, applyOp]
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose,
      star_star, Matrix.star_dotProduct]
    congr 1
    exact dotProduct_comm _ _
  calc
    ⟪x, applyOp (hermitianPart C) x⟫_ℂ =
        (1 / 2 : ℂ) * (⟪x, applyOp C x⟫_ℂ + ⟪x, applyOp Cᴴ x⟫_ℂ) := by
      simp only [hermitianPart, applyOp, Matrix.smul_mulVec, Matrix.add_mulVec,
        WithLp.toLp_smul, WithLp.toLp_add, inner_smul_right, inner_add_right]
    _ = ((⟪x, applyOp C x⟫_ℂ).re : ℂ) := by
      rw [hstar]
      generalize ⟪x, applyOp C x⟫_ℂ = z
      apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
      ring

/-- **Proposition 34**: for any `d × d` matrix `C`, `ℜ(W(C)) = W(ℜ(C))`. -/
theorem real_part_numerical_range {d : ℕ} (C : Op d) :
    realPartNumericalRange C =
      {t : ℝ | (t : ℂ) ∈ numericalRange (hermitianPart C)} := by
  ext t
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (inner_hermitianPart C x).symm⟩
  · rintro ⟨x, hx, ht⟩
    refine ⟨⟪x, applyOp C x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
    rw [inner_hermitianPart] at ht
    exact Complex.ofReal_injective ht.symm

end Qatlib.Papers.QEigenProc24.MainResults.NumericalRange
