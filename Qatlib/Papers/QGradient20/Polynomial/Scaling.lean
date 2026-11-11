/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.Polynomial.TensorGradient

/-!
# Homogeneous scaling of tensor polynomial gradients

This module proves the scaling laws of tensor amplitudes, environments, objectives, and
derivative matrices. For positive tensor degree, `gradient_scale` identifies the gradient degree
as `2 * p - 1`. See [GaoEtAl2021] for the paper context.

## Main statements

* `objective_scale`: Scaling the input by `c` multiplies the tensor polynomial objective by `c ^
  (2 * p)`.
* `derivativeMatrix_scale`: Scaling the input by `c` scales the derivative matrix by `c ^ (2 *
  (p - 1))`.
* `gradient_scale`: For positive tensor degree, scaling the input by `c` multiplies each
  gradient coordinate by `c ^ (2 * p - 1)`.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QGradient20.Polynomial

/-- Scaling all input coordinates by `c` multiplies a length-`p` tensor amplitude by `c ^ p`. -/
theorem amplitude_scale {p : ℕ} {I : Type*} (x : I → ℝ) (c : ℝ) (u : TensorIndex p I) :
    amplitude (fun i => c * x i) u = c ^ p * amplitude x u := by
  simp [amplitude, Finset.prod_mul_distrib]

/-- Scaling all input coordinates by `c` multiplies an environment product by `c ^ (p - 1)`. -/
theorem environment_scale {p : ℕ} {I : Type*} (x : I → ℝ) (c : ℝ) (k : Fin p) (u : TensorIndex p I) :
    environment (fun i => c * x i) k u = c ^ (p - 1) * environment x k u := by
  simp [environment, Finset.prod_mul_distrib]

/-- Scaling the input by `c` multiplies the tensor polynomial objective by `c ^ (2 * p)`. See
[GaoEtAl2021]. -/
theorem objective_scale {p : ℕ} {I : Type*} [Fintype I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (x : I → ℝ) (c : ℝ) :
    objective A (fun i => c * x i) = c ^ (2 * p) * objective A x := by
  unfold objective
  simp only [amplitude_scale]
  have he : ∀ u v, A u v * (c ^ p * amplitude x u) * (c ^ p * amplitude x v) =
      c ^ (2*p) * (A u v * amplitude x u * amplitude x v) := by
    intro u v
    rw [show 2*p=p+p by omega, pow_add]
    ring
  simp only [he, ← Finset.mul_sum]
  ring

/-- Scaling the input by `c` scales the derivative matrix by `c ^ (2 * (p - 1))`. -/
theorem derivativeMatrix_scale {p : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (x : I → ℝ) (c : ℝ) :
    derivativeMatrix A (fun i => c*x i) = c ^ (2*(p-1)) • derivativeMatrix A x := by
  ext i j
  simp only [derivativeMatrix, environment_scale, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [show 2*(p-1)=(p-1)+(p-1) by omega, pow_add]
  ring

/-- For positive tensor degree, scaling the input by `c` multiplies each gradient coordinate by
`c ^ (2 * p - 1)`. See [GaoEtAl2021]. -/
theorem gradient_scale {p : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (hp : 0 < p) (A : Matrix (TensorIndex p I) (TensorIndex p I) ℝ) (x : I → ℝ) (c : ℝ) (i : I) :
    gradient A (fun j => c*x j) i = c ^ (2*p-1) * gradient A x i := by
  rw [← derivativeMatrix_mulVec, derivativeMatrix_scale]
  change ∑ j,(c^(2*(p-1))*derivativeMatrix A x i j)*(c*x j)=_
  have he : ∀ j,(c^(2*(p-1))*derivativeMatrix A x i j)*(c*x j)=
      c^(2*p-1)*(derivativeMatrix A x i j*x j) := by
    intro j
    rw [show 2*p-1=2*(p-1)+1 by omega, pow_succ]
    ring
  simp only [he,← Finset.mul_sum]
  rw [← derivativeMatrix_mulVec]
  rfl

end Qatlib.Papers.QGradient20.Polynomial
