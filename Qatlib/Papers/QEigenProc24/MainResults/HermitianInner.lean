/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QEigenProc24.MainResults.SourceModel
public import Qatlib.Papers.QEigenProc24.MainResults.NumericalRange

@[expose] public section


/-!
Proposition 34 of arXiv:2401.06240v3: taking real parts of a matrix numerical
range agrees with taking the numerical range of its Hermitian part. The proof
uses the exact public Euclidean state and matrix-action representation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace

namespace Qatlib.Papers.QEigenProc24.MainResults.HermitianInner
open Qatlib.Papers.QEigenProc24.MainResults

/-- The quadratic form of a matrix adjoint is the conjugate of the original quadratic form. -/
theorem inner_apply_adjoint {d : ℕ} (C : Op d) (x : Vec d) :
    ⟪x, applyOp Cᴴ x⟫_ℂ = star ⟪x, applyOp C x⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, applyOp]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  exact (Matrix.star_dotProduct _ _).trans (congrArg star (dotProduct_comm _ _))

/-- The Hermitian part has quadratic form equal to the real part of the original quadratic form. -/
theorem inner_hermitian_part {d : ℕ} (C : Op d) (x : Vec d) :
    ⟪x, applyOp (hermitianPart C) x⟫_ℂ = ((⟪x, applyOp C x⟫_ℂ).re : ℂ) := by
  have hact : applyOp (hermitianPart C) x =
      (1 / 2 : ℂ) • (applyOp C x + applyOp Cᴴ x) := by
    change (Matrix.toEuclideanLin (hermitianPart C)) x = _
    rw [hermitianPart, map_smul, map_add]
    rfl
  have hreal : ∀ z : ℂ, (1 / 2 : ℂ) * (z + star z) = (z.re : ℂ) := by
    intro z
    apply Complex.ext
    · simp
      ring
    · simp
  rw [hact, inner_smul_right, inner_add_right, inner_apply_adjoint]
  exact hreal _

/-
theorem real_part_numerical_range {d : ℕ} (C : Op d) :
    realPartNumericalRange C =
      {t : ℝ | (t : ℂ) ∈ numericalRange (hermitianPart C)} := by
  ext t
  constructor
  · rintro ⟨z, ⟨x, hx, hz⟩, hzt⟩
    subst z
    refine ⟨x, hx, ?_⟩
    rw [inner_hermitian_part]
    exact congrArg (fun r : ℝ => (r : ℂ)) hzt.symm
  · rintro ⟨x, hx, hxt⟩
    refine ⟨⟪x, applyOp C x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
    rw [inner_hermitian_part] at hxt
  exact_mod_cast hxt.symm
-/

end Qatlib.Papers.QEigenProc24.MainResults.HermitianInner
