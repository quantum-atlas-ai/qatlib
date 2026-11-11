/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ImaginaryFlow.LeastSquares.TangentResidual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Least squares for normalized complex ansatzes

This module proves positivity of `metricMatrix` and equivalence of coordinate stationarity, the
Gram normal equation, and global minimization of the squared residual cost. `inverseRate` gives
the minimizing rate when the Gram matrix is invertible.

For real-parameter complex ansatzes of constant unit norm, differentiability gives real tangent
orthogonality. This connects the real Gram formulation to complex inner products and to the
variational imaginary-time setting of [McArdleTew2020].

## Main statements

* `stationary_iff_global_min`: stationarity is equivalent to global least-squares optimality.
* `stationary_iff_normal_equation`: the normal equation under tangent orthogonality.
* `complex_ansatz_inverse_minimizer`: the inverse-Gram minimizer for a normalized complex
  ansatz.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.ImaginaryFlow.LeastSquares
noncomputable section
open scoped BigOperators InnerProductSpace RealInnerProductSpace
open Qatlib.Concepts.ImaginaryFlow.LeastSquares

section RealLeastSquares
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real Gram matrix of a finite family of vectors is positive semidefinite. -/
theorem metric_posSemidef {n : ℕ} (d : Fin n → E) : (metricMatrix d).PosSemidef :=
  Matrix.posSemidef_gram ℝ d

/-- Vanishing of every coordinate derivative of the squared residual cost is equivalent to
global minimality over all real rates. -/
theorem stationary_iff_global_min {n : ℕ} (d : Fin n → E) (w : E) (v : Fin n → ℝ) :
    (∀ k, HasDerivAt (fun t : ℝ => mclachlanCost d w (varyRate v k t)) 0 0) ↔
      ∀ x : Fin n → ℝ, mclachlanCost d w v ≤ mclachlanCost d w x := by
  constructor
  · intro hs x
    have ho := (mclachlan_stationary_iff d w v).mp hs
    have hlin : (∑ i, (x i - v i) • d i) = (∑ i, x i • d i) - (∑ i, v i • d i) := by
      simp only [sub_smul, Finset.sum_sub_distrib]
    have hres : ((∑ i, x i • d i) + w) =
        ((∑ i, v i • d i) + w) + (∑ i, (x i - v i) • d i) := by
      rw [hlin]
      abel
    have horth : ⟪((∑ i, v i • d i) + w), (∑ i, (x i - v i) • d i)⟫_ℝ = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [inner_smul_right, real_inner_comm, ho i, mul_zero]
    unfold mclachlanCost
    rw [hres, norm_add_sq_real ((∑ i, v i • d i) + w) (∑ i, (x i - v i) • d i), horth]
    nlinarith [sq_nonneg ‖∑ i, (x i - v i) • d i‖]
  · intro hm k
    have hmin : IsLocalMin (fun t : ℝ => mclachlanCost d w (varyRate v k t)) 0 := by
      apply Filter.Eventually.of_forall
      intro t
      have h0 : varyRate v k 0 = v := by ext i; simp [varyRate]
      simpa only [h0] using hm (varyRate v k t)
    have hd := hasDerivAt_mclachlanCost_direction d w v k
    rw [hmin.hasDerivAt_eq_zero hd] at hd
    exact hd

/-- When the tangent vectors are real-orthogonal to `φ`, coordinate stationarity for the
centered evolution residual is equivalent to the Gram normal equation `metricMatrix d * v =
-gradientVector d H φ`. -/
theorem stationary_iff_normal_equation {n : ℕ} (d : Fin n → E)
    (H : E →ₗ[ℝ] E) (φ : E) (hnormal : ∀ i, ⟪d i, φ⟫_ℝ = 0) (v : Fin n → ℝ) :
    (∀ k, HasDerivAt (fun t : ℝ =>
      mclachlanCost d (H φ - ⟪φ, H φ⟫_ℝ • φ) (varyRate v k t)) 0 0) ↔
      (metricMatrix d).mulVec v = - gradientVector d H φ := by
  rw [mclachlan_stationary_iff]
  constructor
  · intro hs
    ext k
    exact mclachlan_parameter_update_rule d H φ v hnormal hs k
  · intro he k
    have hk := congrFun he k
    change (∑ i, metricMatrix d k i * v i) = - gradientVector d H φ k at hk
    rw [inner_add_right, inner_sub_right, inner_smul_right, hnormal k]
    simp only [mul_zero, sub_zero]
    rw [inner_sum]
    simp only [inner_smul_right]
    have hsum : (∑ i, v i * ⟪d k, d i⟫_ℝ) = ∑ i, metricMatrix d k i * v i := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    rw [hsum, hk]
    change - gradientVector d H φ k + gradientVector d H φ k = 0
    ring

/-- The negative inverse-Gram matrix applied to the gradient vector. -/
def inverseRate {n : ℕ} (d : Fin n → E) (H : E →ₗ[ℝ] E) (φ : E) : Fin n → ℝ :=
  - (metricMatrix d)⁻¹.mulVec (gradientVector d H φ)

/-- When the Gram matrix is invertible, `inverseRate` satisfies the Gram normal equation. -/
theorem inverseRate_equation {n : ℕ} (d : Fin n → E) (H : E →ₗ[ℝ] E) (φ : E)
    [Invertible (metricMatrix d)] :
    (metricMatrix d).mulVec (inverseRate d H φ) = - gradientVector d H φ := by
  rw [inverseRate, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- For tangent vectors real-orthogonal to `φ` and an invertible Gram matrix, `inverseRate`
globally minimizes the centered evolution residual cost. -/
theorem inverseRate_global_min {n : ℕ} (d : Fin n → E) (H : E →ₗ[ℝ] E) (φ : E)
    (hnormal : ∀ i, ⟪d i, φ⟫_ℝ = 0) [Invertible (metricMatrix d)] :
    ∀ x, mclachlanCost d (H φ - ⟪φ, H φ⟫_ℝ • φ) (inverseRate d H φ) ≤
      mclachlanCost d (H φ - ⟪φ, H φ⟫_ℝ • φ) x := by
  apply (stationary_iff_global_min _ _ _).mp
  exact (stationary_iff_normal_equation d H φ hnormal _).mpr (inverseRate_equation d H φ)

/-- Under real tangent orthogonality and invertibility of the Gram matrix, every global
minimizer equals `inverseRate`. -/
theorem global_min_eq_inverseRate {n : ℕ} (d : Fin n → E) (H : E →ₗ[ℝ] E) (φ : E)
    (hnormal : ∀ i, ⟪d i, φ⟫_ℝ = 0) [Invertible (metricMatrix d)] (v : Fin n → ℝ)
    (hm : ∀ x, mclachlanCost d (H φ - ⟪φ, H φ⟫_ℝ • φ) v ≤
      mclachlanCost d (H φ - ⟪φ, H φ⟫_ℝ • φ) x) : v = inverseRate d H φ := by
  apply Matrix.mulVec_injective_of_invertible (metricMatrix d)
  rw [inverseRate_equation]
  exact (stationary_iff_normal_equation d H φ hnormal v).mp
    ((stationary_iff_global_min _ _ _).mpr hm)

/-- An Euler step along `inverseRate` subtracts the step size times the inverse-Gram matrix
applied to the gradient vector. -/
theorem euler_update {n : ℕ} (d : Fin n → E) (H : E →ₗ[ℝ] E) (φ : E)
    (θ : Fin n → ℝ) (δ : ℝ) :
    θ + δ • inverseRate d H φ = θ - δ • ((metricMatrix d)⁻¹.mulVec (gradientVector d H φ)) := by
  simp only [inverseRate, smul_neg, sub_eq_add_neg]

end RealLeastSquares

section ComplexAnsatz
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

/-- The real Gram matrix entry is the real part of the corresponding complex inner product. -/
theorem complex_metric_entry {n : ℕ} (d : Fin n → E) (i j : Fin n) :
    metricMatrix d i j = (inner ℂ (d i) (d j)).re := rfl

/-- The gradient entry for a complex-linear operator, viewed as real-linear, is the real part of
the corresponding complex inner product. -/
theorem complex_gradient_entry {n : ℕ} (d : Fin n → E) (H : E →ₗ[ℂ] E)
    (φ : E) (i : Fin n) :
    gradientVector d (H.restrictScalars ℝ) φ i = (inner ℂ (d i) (H φ)).re := rfl

/-- Every derivative direction of a real-differentiable complex ansatz of constant unit norm is
real-orthogonal to its value. -/
theorem normalized_ansatz_tangent {n : ℕ} (Φ : (Fin n → ℝ) → E)
    (θ : Fin n → ℝ) (D : (Fin n → ℝ) →L[ℝ] E)
    (hD : HasFDerivAt Φ D θ) (hnorm : ∀ x, ‖Φ x‖ = 1) (v : Fin n → ℝ) :
    (inner ℂ (D v) (Φ θ)).re = 0 := by
  have hconst : HasFDerivAt (fun x : Fin n → ℝ => ‖Φ x‖ ^ 2)
      (0 : (Fin n → ℝ) →L[ℝ] ℝ) θ := by
    have hf : (fun x : Fin n → ℝ => ‖Φ x‖ ^ 2) = fun _ => (1 : ℝ) := by
      ext x
      rw [hnorm x]
      norm_num
    rw [hf]
    exact hasFDerivAt_const (1 : ℝ) θ
  have he := congrArg (fun T : (Fin n → ℝ) →L[ℝ] ℝ => T v) (hD.norm_sq.unique hconst)
  have hreal : inner ℝ (D v) (Φ θ) = 0 := by
    simp only [two_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, ContinuousLinearMap.zero_apply] at he
    rw [real_inner_comm] at he
    linarith
  exact hreal

/-- The coordinate tangent vectors of a differentiable unit-norm complex ansatz are orthogonal
to its value in the underlying real inner product. -/
theorem normalized_coordinate_tangents {n : ℕ} (Φ : (Fin n → ℝ) → E)
    (θ : Fin n → ℝ) (D : (Fin n → ℝ) →L[ℝ] E)
    (hD : HasFDerivAt Φ D θ) (hnorm : ∀ x, ‖Φ x‖ = 1) :
    ∀ i, inner ℝ (D (Pi.single i 1)) (Φ θ) = 0 := by
  intro i
  exact normalized_ansatz_tangent Φ θ D hD hnorm (Pi.single i 1)

/-- For a differentiable unit-norm complex ansatz with invertible coordinate Gram matrix, that
Gram matrix is positive semidefinite and the inverse-Gram rate globally minimizes the
centered evolution residual [McArdleTew2020]. -/
theorem complex_ansatz_inverse_minimizer {n : ℕ} (Φ : (Fin n → ℝ) → E)
    (θ : Fin n → ℝ) (D : (Fin n → ℝ) →L[ℝ] E)
    (hD : HasFDerivAt Φ D θ) (hnorm : ∀ x, ‖Φ x‖ = 1) (H : E →ₗ[ℂ] E)
    [Invertible (metricMatrix (fun i : Fin n => D (Pi.single i 1)))] :
    let d := fun i : Fin n => D (Pi.single i 1)
    let Hr := H.restrictScalars ℝ
    (metricMatrix d).PosSemidef ∧
      ∀ v, mclachlanCost d (H (Φ θ) - (inner ℂ (Φ θ) (H (Φ θ))).re • Φ θ)
        (inverseRate d Hr (Φ θ)) ≤
      mclachlanCost d (H (Φ θ) - (inner ℂ (Φ θ) (H (Φ θ))).re • Φ θ) v := by
  exact ⟨metric_posSemidef _, inverseRate_global_min _ _ _
    (normalized_coordinate_tangents Φ θ D hD hnorm)⟩

end ComplexAnsatz

end
end Qatlib.Concepts.ImaginaryFlow.LeastSquares
