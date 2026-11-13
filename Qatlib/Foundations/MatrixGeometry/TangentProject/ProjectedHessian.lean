/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TangentProject.Projection
import Qatlib.Foundations.MatrixGeometry.TangentProject.AmbientGradient

/-!
# Projected energy gradients and Hessians

Expresses the projection of the ambient energy gradient as `gradientExtension` and rewrites
tangent state variations as commutators. The theorem `projected_gradient_fderiv` gives the
projected derivative along `Ω * U` as `lieHessian O (stateMap ψ U) Ω * U` for unitary `U` and
skew-Hermitian `Ω`. See [LaiEtAl2026] for related background.

## Main statements

* `project_energy_gradient`: For Hermitian `O` and `ψ`, projecting `2 • (O * U * ψ)` at `U`
  gives `gradientExtension O ψ U`.
* `projected_gradient_fderiv`: For Hermitian `O` and `ψ`, unitary `U`, and skew-Hermitian `Ω`,
  projecting the gradient-extension derivative along `Ω * U` gives `lieHessian O (stateMap ψ U)
  Ω * U`.

## References

* [Lai et al., 2026][LaiEtAl2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Foundations.MatrixGeometry.TangentProject
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix commutator `A * B - B * A`. -/
def bracket (A B : Matrix n n ℂ) : Matrix n n ℂ := A * B - B * A

/-- The matrix expression `½ • ([O, [Ω, ρ]] + [[O, Ω], ρ])` formed from nested commutators. -/
def lieHessian (O ρ Ω : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 / 2 : ℝ) • (bracket O (bracket Ω ρ) + bracket (bracket O Ω) ρ)

/-- For Hermitian `O` and `ψ`, projecting `2 • (O * U * ψ)` at `U` gives `gradientExtension O ψ
U`. -/
theorem project_energy_gradient (O ψ U : Matrix n n ℂ) (hO : Oᴴ = O) (hψ : ψᴴ = ψ) :
    project U ((2 : ℝ) • (O * U * ψ)) = gradientExtension O ψ U := by
  simp only [project, skew, Matrix.smul_mul, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hO, hψ,
    ← smul_sub, smul_smul]
  norm_num
  unfold gradientExtension stateMap
  noncomm_ring

/-- For skew-Hermitian `Ω`, the state derivative along `Ω * U` equals the commutator of `Ω` with
`stateMap ψ U`. -/
theorem stateDerivative_tangent (ψ U Ω : Matrix n n ℂ) (hΩ : Ωᴴ = -Ω) :
    stateDerivative ψ U (Ω * U) = bracket Ω (stateMap ψ U) := by
  rw [stateDerivative_apply]
  simp only [Matrix.conjTranspose_mul, hΩ, Matrix.mul_neg, bracket, stateMap]
  noncomm_ring

/-- For Hermitian `O` and `ψ`, unitary `U`, and skew-Hermitian `Ω`, projecting the
gradient-extension derivative along `Ω * U` gives `lieHessian O (stateMap ψ U) Ω * U`. -/
theorem projected_gradient_fderiv (O ψ U Ω : Matrix n n ℂ)
    (hO : Oᴴ = O) (hψ : ψᴴ = ψ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (hΩ : Ωᴴ = -Ω) :
    project U (fderiv ℝ (gradientExtension O ψ) U (Ω * U)) =
      lieHessian O (stateMap ψ U) Ω * U := by
  have hu : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  let ρ := stateMap ψ U
  have hρ : ρᴴ = ρ := by
    simp only [ρ, stateMap, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hψ]
    noncomm_ring
  have hd : fderiv ℝ (gradientExtension O ψ) U (Ω * U) =
      (bracket O (bracket Ω ρ) + bracket O ρ * Ω) * U := by
    rw [(gradientExtension_hasFDerivAt O ψ U).fderiv]
    change gradientDerivative O ψ U (Ω * U) = _
    rw [gradientDerivative_apply]
    have hs : Ω * U * ψ * Uᴴ + U * ψ * (Ω * U)ᴴ = bracket Ω ρ := by
      change _ = bracket Ω (stateMap ψ U)
      rw [← stateDerivative_apply]
      exact stateDerivative_tangent ψ U Ω hΩ
    rw [hs]
    change (O * bracket Ω ρ - bracket Ω ρ * O) * U +
      (O * ρ - ρ * O) * (Ω * U) = _
    simp only [bracket]
    noncomm_ring
  rw [hd]
  have hp : project U ((bracket O (bracket Ω ρ) + bracket O ρ * Ω) * U) =
      skew (bracket O (bracket Ω ρ) + bracket O ρ * Ω) * U := by
    unfold project
    rw [Matrix.mul_assoc, hu, Matrix.mul_one]
  rw [hp]
  congr 1
  unfold skew lieHessian
  congr 1
  simp only [bracket, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, hO, hρ, hΩ]
  noncomm_ring
