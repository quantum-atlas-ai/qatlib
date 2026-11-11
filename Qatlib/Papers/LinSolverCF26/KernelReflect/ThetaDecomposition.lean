/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

set_option backward.isDefEq.respectTransparency false

/-!
# `ThetaDecomposition` — the `θ_t` orthogonal decomposition of the KR start state

Source: P. C. S. Costa, A. M. Dalzell, D. An, D. W. Berry,
*Constant Factor Analysis of Optimal Quantum Linear Solvers in Practice*,
arXiv:2604.22185v2 (fixed version), Section II B, Eqs. (8)–(11).

In the augmented space the KR algorithm starts from the vector `|e_{m-1}⟩` and
rotates to the kernel vector `|x_t⟩`, with
`θ_t = arctan(‖x‖/t)`, `|x_t⟩ = sin θ_t |x⟩ + cos θ_t |e_{m-1}⟩` (Eq. (8)), and
the orthogonal companion `|y_t⟩ = -cos θ_t |x⟩ + sin θ_t |e_{m-1}⟩` (Eq. (11)).
Eq. (10) records the inverse decomposition of the start state,
`|e_{m-1}⟩ = cos θ_t |x_t⟩ + sin θ_t |y_t⟩`.

We model the augmented Hilbert space abstractly: the unknown `x` and the
augmentation vector `e` span an orthogonal plane inside one real inner product
space, and `t > 0` is the norm estimate. All identities below are the exact
algebraic content of Eqs. (8)–(11); no approximation or extra assumption is
introduced.
-/

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace

namespace Qatlib.Papers.LinSolverCF26.KernelReflect.ThetaDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Eq. (9): the rotation angle `θ_t = arctan(‖x‖ / t)`. -/
def theta (t : ℝ) (x : E) : ℝ := Real.arctan (‖x‖ / t)

/-- `u = x / ‖x‖` is the unit vector of the (unnormalized) solution. -/
def unitSolution (x : E) : E := (‖x‖)⁻¹ • x

/-- Eq. (8): the kernel vector `|x_t⟩`, normalised to unit length, written in
terms of the unnormalised solution as `(x + t • e) / √(‖x‖² + t²)`. -/
def kernelVec (t : ℝ) (x e : E) : E :=
  (Real.sqrt (‖x‖ ^ 2 + t ^ 2))⁻¹ • (x + t • e)

/-- Eq. (11): the orthogonal companion
`|y_t⟩ = -cos θ_t |x⟩ + sin θ_t |e_{m-1}⟩`. -/
def companionVec (t : ℝ) (x e : E) : E :=
  -(Real.cos (theta t x)) • unitSolution x + (Real.sin (theta t x)) • e

/-- Eq. (9) evaluated: `cos θ_t = t / √(‖x‖² + t²)` for `t > 0`. -/
theorem cos_theta_eq {t : ℝ} (ht : 0 < t) (x : E) :
    Real.cos (theta t x) = t / Real.sqrt (‖x‖ ^ 2 + t ^ 2) := by
  have hA : 0 < ‖x‖ ^ 2 + t ^ 2 := by positivity
  rw [theta, Real.cos_arctan]
  have h1 : 1 + (‖x‖ / t) ^ 2 = (‖x‖ ^ 2 + t ^ 2) / t ^ 2 := by
    field_simp
    ring
  rw [h1, Real.sqrt_div hA.le, Real.sqrt_sq ht.le, one_div_div]

/-- Eq. (9) evaluated: `sin θ_t = ‖x‖ / √(‖x‖² + t²)` for `t > 0`. -/
theorem sin_theta_eq {t : ℝ} (ht : 0 < t) (x : E) :
    Real.sin (theta t x) = ‖x‖ / Real.sqrt (‖x‖ ^ 2 + t ^ 2) := by
  have hA : 0 < ‖x‖ ^ 2 + t ^ 2 := by positivity
  rw [theta, Real.sin_arctan]
  have h1 : 1 + (‖x‖ / t) ^ 2 = (‖x‖ ^ 2 + t ^ 2) / t ^ 2 := by
    field_simp
    ring
  rw [h1, Real.sqrt_div hA.le, Real.sqrt_sq ht.le]
  field_simp

/-- The rotation angle lies strictly between `0` and `π/2` when `x` is nonzero
and `t > 0`. -/
theorem theta_pos_and_lt {t : ℝ} (ht : 0 < t) {x : E} (hx : 0 < ‖x‖) :
    0 < theta t x ∧ theta t x < Real.pi / 2 :=
  ⟨(Real.arctan_pos).2 (div_pos hx ht), Real.arctan_lt_pi_div_two _⟩

/-- `sin² θ_t + cos² θ_t = 1`. -/
theorem sin_sq_add_cos_sq (t : ℝ) (x : E) :
    Real.sin (theta t x) ^ 2 + Real.cos (theta t x) ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq _

/-- The unit solution has norm one (for `x ≠ 0`). -/
theorem norm_unitSolution {x : E} (hx : 0 < ‖x‖) : ‖unitSolution x‖ = 1 := by
  rw [unitSolution, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx.ne']

/-- `x = ‖x‖ • (x/‖x‖)`. -/
theorem smul_unitSolution {x : E} (hx : 0 < ‖x‖) : ‖x‖ • unitSolution x = x := by
  rw [unitSolution, smul_smul, mul_inv_cancel₀ hx.ne', one_smul]

/-- Eq. (8): the kernel vector is `sin θ_t · x/‖x‖ + cos θ_t · e`. -/
theorem kernelVec_eq {t : ℝ} (ht : 0 < t) {x e : E} (hx : 0 < ‖x‖) :
    kernelVec t x e =
      (Real.sin (theta t x)) • unitSolution x + (Real.cos (theta t x)) • e := by
  have hcoef1 : (Real.sqrt (‖x‖ ^ 2 + t ^ 2))⁻¹ * ‖x‖ =
      Real.sin (theta t x) := by
    rw [sin_theta_eq ht x, div_eq_mul_inv, mul_comm]
  have hcoef2 : (Real.sqrt (‖x‖ ^ 2 + t ^ 2))⁻¹ * t =
      Real.cos (theta t x) := by
    rw [cos_theta_eq ht x, div_eq_mul_inv, mul_comm]
  have harg : x + t • e = ‖x‖ • unitSolution x + t • e := by
    rw [smul_unitSolution hx]
  calc kernelVec t x e = (Real.sqrt (‖x‖ ^ 2 + t ^ 2))⁻¹ • (x + t • e) := rfl
    _ = (Real.sqrt (‖x‖ ^ 2 + t ^ 2))⁻¹ •
          (‖x‖ • unitSolution x + t • e) := by rw [harg]
    _ = ((Real.sqrt (‖x‖ ^ 2 + t ^ 2))⁻¹ * ‖x‖) • unitSolution x +
          ((Real.sqrt (‖x‖ ^ 2 + t ^ 2))⁻¹ * t) • e := by
        rw [smul_add, smul_smul, smul_smul]
    _ = (Real.sin (theta t x)) • unitSolution x +
          (Real.cos (theta t x)) • e := by rw [hcoef1, hcoef2]

/-- Eq. (11) and Eq. (10) are mutually inverse: `x_t` and `y_t` are orthogonal. -/
theorem inner_kernelVec_companion {t : ℝ} (ht : 0 < t) {x e : E}
    (hx : 0 < ‖x‖) (he : ‖e‖ = 1) (hxe : ⟪x, e⟫ = 0) :
    ⟪kernelVec t x e, companionVec t x e⟫ = 0 := by
  have hu : ‖unitSolution x‖ = 1 := norm_unitSolution hx
  have hue : ⟪unitSolution x, e⟫ = 0 := by
    rw [unitSolution, real_inner_smul_left, hxe, mul_zero]
  have huu : ⟪unitSolution x, unitSolution x⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  have hee : ⟪e, e⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  have heu : ⟪e, unitSolution x⟫ = 0 := by rw [real_inner_comm]; exact hue
  rw [kernelVec_eq ht hx, companionVec]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    huu, hue, heu, hee, mul_zero, mul_one, add_zero, zero_add,
    starRingEnd_apply, star_trivial]
  ring

/-- The companion vector is a unit vector. -/
theorem norm_companionVec {t : ℝ} (ht : 0 < t) {x e : E}
    (hx : 0 < ‖x‖) (he : ‖e‖ = 1) (hxe : ⟪x, e⟫ = 0) :
    ‖companionVec t x e‖ = 1 := by
  have hsum := sin_sq_add_cos_sq t x
  have hu : ‖unitSolution x‖ = 1 := norm_unitSolution hx
  have hue : ⟪unitSolution x, e⟫ = 0 := by
    rw [unitSolution, real_inner_smul_left, hxe, mul_zero]
  have horth : ⟪(-(Real.cos (theta t x))) • unitSolution x,
      (Real.sin (theta t x)) • e⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hue, mul_zero, mul_zero]
  have hca : ‖(-(Real.cos (theta t x))) • unitSolution x‖ ^ 2 =
      Real.cos (theta t x) ^ 2 := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs, neg_sq]
  have heb : ‖(Real.sin (theta t x)) • e‖ ^ 2 = Real.sin (theta t x) ^ 2 := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  have hsq : ‖companionVec t x e‖ ^ 2 = 1 := by
    rw [companionVec]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      ((-(Real.cos (theta t x))) • unitSolution x)
      ((Real.sin (theta t x)) • e) horth
    rw [← sq, ← sq, ← sq] at hpy
    rw [hca, heb] at hpy
    linarith [hsum, hpy]
  nlinarith [norm_nonneg (companionVec t x e), hsq]

/-- Eq. (10): the start state decomposes as
`|e_{m-1}⟩ = cos θ_t |x_t⟩ + sin θ_t |y_t⟩`. -/
theorem startVec_decomposition {t : ℝ} (ht : 0 < t) (x e : E) :
    Real.cos (theta t x) • kernelVec t x e + Real.sin (theta t x) • companionVec t x e = e := by
  have hsum := sin_sq_add_cos_sq t x
  by_cases hx0 : ‖x‖ = 0
  · have hx : x = 0 := norm_eq_zero.mp hx0
    subst hx
    have hthet : theta t (0 : E) = 0 := by
      rw [theta, norm_zero, zero_div, Real.arctan_zero]
    have hs : Real.sin (theta t (0 : E)) = 0 := by rw [hthet, Real.sin_zero]
    have hc : Real.cos (theta t (0 : E)) = 1 := by rw [hthet, Real.cos_zero]
    have hkv : kernelVec t (0 : E) e = e := by
      rw [kernelVec, norm_zero]
      have hsq : (0 : ℝ) ^ 2 + t ^ 2 = t ^ 2 := by ring
      rw [hsq, Real.sqrt_sq ht.le, smul_add, smul_smul, smul_zero,
        inv_mul_cancel₀ ht.ne', one_smul, zero_add]
    have huv : unitSolution (0 : E) = 0 := by
      rw [unitSolution, norm_zero, inv_zero, zero_smul]
    rw [hkv, companionVec, hs, hc, huv]
    simp
  · have hx : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
    rw [kernelVec_eq ht hx, companionVec]
    simp only [smul_add, smul_smul]
    rw [show Real.sin (theta t x) * -Real.cos (theta t x) =
          -(Real.cos (theta t x) * Real.sin (theta t x)) from by ring, neg_smul]
    have h2 : Real.cos (theta t x) * Real.cos (theta t x) +
        Real.sin (theta t x) * Real.sin (theta t x) = 1 := by
      nlinarith [hsum]
    rw [show (Real.cos (theta t x) * Real.sin (theta t x)) • unitSolution x +
          (Real.cos (theta t x) * Real.cos (theta t x)) • e +
          (-((Real.cos (theta t x) * Real.sin (theta t x)) • unitSolution x) +
          (Real.sin (theta t x) * Real.sin (theta t x)) • e) =
          (Real.cos (theta t x) * Real.cos (theta t x)) • e +
          (Real.sin (theta t x) * Real.sin (theta t x)) • e from by abel,
      ← add_smul, h2, one_smul]
