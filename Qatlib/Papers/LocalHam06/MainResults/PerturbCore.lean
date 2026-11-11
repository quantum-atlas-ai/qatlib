/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Projection and overlap bounds for perturbations

This module proves real inner-product-space estimates supporting the perturbation arguments of
[KempeKitaevRegev2006]. It bounds symmetric projections, excludes low-energy vectors from a
high-energy subspace, controls projected eigenvector components, and turns an effective energy
bound into a squared-overlap estimate.

## Main statements

* `lower_proj_ne_zero`: Shows that a low-energy vector has a nonzero complementary component.
* `proj_component_le`: Bounds the high-energy component of a perturbed eigenvector.
* `overlap_gap_bound`: Controls overlap with an isolated reference eigenvector.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option autoImplicit false

noncomputable section

open scoped RealInnerProductSpace
open Finset

namespace Qatlib.Papers.LocalHam06.MainResults.Perturb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

/-- A symmetric idempotent real linear map does not increase vector norms. -/
theorem norm_proj_le (P : E →ₗ[ℝ] E) (hPidem : ∀ x, P (P x) = P x)
    (hPsymm : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫) (x : E) : ‖P x‖ ≤ ‖x‖ := by
  have hperp : ⟪P x, x - P x⟫ = 0 := by
    rw [hPsymm x (x - P x), map_sub, hPidem x, sub_self, inner_zero_right]
  have hpyth : ‖P x + (x - P x)‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 :=
    by simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (x - P x) hperp
  have hx : P x + (x - P x) = x := by abel
  have hsq : ‖P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hx] at hpyth
    nlinarith [sq_nonneg ‖x - P x‖]
  nlinarith [norm_nonneg (P x), norm_nonneg x, sq_nonneg (‖P x‖ - ‖x‖)]

omit [FiniteDimensional ℝ E] in

/-- A nonzero vector fixed by `P` cannot have perturbed quadratic energy at most `lamStar *
‖x‖^2` when the stated high-energy lower bound and perturbation bound leave a strict gap
[KempeKitaevRegev2006]. -/
theorem below_cutoff_not_Lplus (P : E →ₗ[ℝ] E) (H V : E →ₗ[ℝ] E)
    {lamStar lamPlus b : ℝ} (hgap : lamStar + b < lamPlus)
    (hH : ∀ y : E, P y = y → lamPlus * ‖y‖ ^ 2 ≤ ⟪y, H y⟫)
    (hV : ∀ x : E, -(b * ‖x‖ ^ 2) ≤ ⟪x, V x⟫)
    {x : E} (hx : x ≠ 0) (hxP : P x = x)
    (hbelow : ⟪x, (H + V) x⟫ ≤ lamStar * ‖x‖ ^ 2) : False := by
  have h1 : lamPlus * ‖x‖ ^ 2 ≤ ⟪x, H x⟫ := hH x hxP
  have h2 : -(b * ‖x‖ ^ 2) ≤ ⟪x, V x⟫ := hV x
  have hsum : ⟪x, (H + V) x⟫ = ⟪x, H x⟫ + ⟪x, V x⟫ := by
    rw [LinearMap.add_apply, inner_add_right]
  have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  nlinarith [h1, h2, hsum, hbelow, hpos]

omit [FiniteDimensional ℝ E] in

/-- For linear maps `P` and `P'` summing to the identity, the component `P' x` of a nonzero
low-energy vector is nonzero under the stated gap and perturbation bounds
[KempeKitaevRegev2006]. -/
theorem lower_proj_ne_zero (P P' : E →ₗ[ℝ] E) (H V : E →ₗ[ℝ] E)
    (hPP' : ∀ x, P x + P' x = x)
    {lamStar lamPlus b : ℝ} (hgap : lamStar + b < lamPlus)
    (hH : ∀ y : E, P y = y → lamPlus * ‖y‖ ^ 2 ≤ ⟪y, H y⟫)
    (hV : ∀ x : E, -(b * ‖x‖ ^ 2) ≤ ⟪x, V x⟫)
    {x : E} (hx : x ≠ 0) (hbelow : ⟪x, (H + V) x⟫ ≤ lamStar * ‖x‖ ^ 2) :
    P' x ≠ 0 := by
  intro h0
  have hxP : P x = x := by
    have h := hPP' x
    rw [h0, add_zero] at h
    exact h
  exact below_cutoff_not_Lplus P H V hgap hH hV hx hxP hbelow

omit [FiniteDimensional ℝ E] in

/-- A quadratic lower bound `c * ‖y‖^2 ≤ inner y (H y)` implies `c * ‖y‖ ≤ ‖H y‖`. -/
theorem norm_le_norm_apply_of_quad_le (H : E →ₗ[ℝ] E) {c : ℝ} (_hc : 0 ≤ c) (y : E)
    (h : c * ‖y‖ ^ 2 ≤ ⟪y, H y⟫) : c * ‖y‖ ≤ ‖H y‖ := by
  have h2 : ⟪y, H y⟫ ≤ ‖y‖ * ‖H y‖ := real_inner_le_norm y (H y)
  have h3 : c * ‖y‖ ^ 2 ≤ ‖y‖ * ‖H y‖ := le_trans h h2
  rcases eq_or_lt_of_le (norm_nonneg y) with hy | hy
  · rw [← hy, mul_zero]
    exact norm_nonneg (H y)
  · nlinarith [hy, norm_nonneg (H y)]

omit [FiniteDimensional ℝ E] in

/-- Under the stated projection, commutation, gap, and perturbation hypotheses, a perturbed
eigenvector satisfies `‖P x‖ * (lamPlus - mu) ≤ b * ‖x‖` [KempeKitaevRegev2006]. -/
theorem proj_component_le (P : E →ₗ[ℝ] E) (hPidem : ∀ x, P (P x) = P x)
    (hPsymm : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (H V : E →ₗ[ℝ] E) (hHcomm : ∀ x, P (H x) = H (P x))
    {lamPlus b mu lam : ℝ} (hlamPlus : 0 ≤ lamPlus)
    (hH : ∀ y : E, P y = y → lamPlus * ‖y‖ ^ 2 ≤ ⟪y, H y⟫)
    (hVnorm : ∀ x : E, ‖V x‖ ≤ b * ‖x‖)
    (hlam0 : 0 ≤ lam) (hlam_mu : lam ≤ mu) (_hmu : mu < lamPlus)
    {x : E} (hxeig : H x + V x = lam • x) :
    ‖P x‖ * (lamPlus - mu) ≤ b * ‖x‖ := by
  have hHapp : lamPlus * ‖P x‖ ≤ ‖H (P x)‖ :=
    norm_le_norm_apply_of_quad_le H hlamPlus (P x) (hH (P x) (hPidem x))
  have hcontra : ‖P (V x)‖ ≤ ‖V x‖ := norm_proj_le P hPidem hPsymm (V x)
  have hVx : ‖V x‖ ≤ b * ‖x‖ := hVnorm x
  have hPeig : P (H x + V x) = lam • P x := by rw [hxeig, map_smul]
  have hnormEq : ‖P (H x + V x)‖ = lam * ‖P x‖ := by
    rw [hPeig, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0]
  have hsplit : P (H x + V x) = P (H x) + P (V x) := by rw [map_add]
  have hcomm : P (H x) = H (P x) := hHcomm x
  have htri : ‖H (P x)‖ ≤ ‖P (H x + V x)‖ + ‖P (V x)‖ := by
    rw [hsplit, hcomm]
    have h := norm_add_le (H (P x) + P (V x)) (-(P (V x)))
    simpa using h
  have hlow : lamPlus * ‖P x‖ - b * ‖x‖ ≤ ‖P (H x + V x)‖ := by linarith
  rw [hnormEq] at hlow
  have hnonneg : 0 ≤ ‖P x‖ := norm_nonneg _
  have hstep : ‖P x‖ * (lamPlus - lam) ≤ b * ‖x‖ := by nlinarith
  have hmono : lamPlus - mu ≤ lamPlus - lam := by linarith
  calc ‖P x‖ * (lamPlus - mu) ≤ ‖P x‖ * (lamPlus - lam) :=
        mul_le_mul_of_nonneg_left hmono hnonneg
    _ ≤ b * ‖x‖ := hstep

omit [FiniteDimensional ℝ E] in

/-- The remainder after subtracting the component of `x` along a unit vector `v` is orthogonal
to `v`. -/
theorem inner_remainder_eq_zero {v x : E} (hv : ‖v‖ = 1) :
    ⟪x - ⟪v, x⟫ • v, v⟫ = 0 := by
  rw [inner_sub_left, real_inner_smul_left, real_inner_comm v x, real_inner_comm v v,
    real_inner_self_eq_norm_sq, hv]
  ring

omit [FiniteDimensional ℝ E] in

/-- For a symmetric effective operator with a normalized eigenvector at `lam1` and complementary
energy at least `lam2 > lam1`, a unit vector of energy at most `lam1 + 2 * eps` has squared
overlap at least `1 - 2 * eps / (lam2 - lam1)` [KempeKitaevRegev2006]. -/
theorem overlap_gap_bound (Heff : E →ₗ[ℝ] E)
    (hHeff : ∀ x y, ⟪Heff x, y⟫ = ⟪x, Heff y⟫)
    {lam1 lam2 eps : ℝ} (hgap : 0 < lam2 - lam1)
    {v : E} (hv : ‖v‖ = 1) (hveig : Heff v = lam1 • v)
    (hcomp : ∀ y : E, ⟪y, v⟫ = 0 → lam2 * ‖y‖ ^ 2 ≤ ⟪y, Heff y⟫)
    {x : E} (hx : ‖x‖ = 1) (hxq : ⟪x, Heff x⟫ ≤ lam1 + 2 * eps) :
    1 - 2 * eps / (lam2 - lam1) ≤ ⟪x, v⟫ ^ 2 := by
  set c : ℝ := ⟪v, x⟫ with hc
  set y : E := x - c • v with hy
  have hvy : ⟪v, y⟫ = 0 := by
    rw [hy, hc, real_inner_comm]
    exact inner_remainder_eq_zero hv
  have hyorth : ⟪y, v⟫ = 0 := by rw [real_inner_comm]; exact hvy
  have hdecomp : x = c • v + y := by rw [hy]; abel
  have hnormy : ‖y‖ ^ 2 = 1 - c ^ 2 := by
    have hperp : ⟪c • v, y⟫ = 0 := by
      rw [real_inner_smul_left, hvy, mul_zero]
    have hpyth : ‖c • v + y‖ ^ 2 = ‖c • v‖ ^ 2 + ‖y‖ ^ 2 :=
      by simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • v) y hperp
    rw [← hdecomp, hx] at hpyth
    have hcv : ‖c • v‖ ^ 2 = c ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
    rw [hcv] at hpyth
    linarith
  have hcross1 : ⟪c • v, Heff y⟫ = 0 := by
    rw [real_inner_smul_left, ← hHeff v y, hveig, real_inner_smul_left, hvy, mul_zero,
      mul_zero]
  have hcross2 : ⟪y, Heff (c • v)⟫ = 0 := by
    rw [map_smul, real_inner_smul_right, hveig, real_inner_smul_right, hyorth, mul_zero,
      mul_zero]
  have hquad : ⟪x, Heff x⟫ = c ^ 2 * lam1 + ⟪y, Heff y⟫ := by
    rw [hdecomp]
    have hsplit1 : Heff (c • v + y) = Heff (c • v) + Heff y := map_add _ _ _
    rw [hsplit1, inner_add_left, inner_add_right, inner_add_right]
    simp only [hcross1, hcross2, add_zero, zero_add]
    have hcvv : ⟪c • v, Heff (c • v)⟫ = c ^ 2 * lam1 := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right, hveig,
        real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
      ring
    rw [hcvv]
  have hlow : lam2 * ‖y‖ ^ 2 ≤ ⟪y, Heff y⟫ := hcomp y hyorth
  have hmain : lam1 + 2 * eps ≥ c ^ 2 * lam1 + lam2 * ‖y‖ ^ 2 := by
    rw [hquad] at hxq
    linarith
  rw [hnormy] at hmain
  have hkey : 2 * eps ≥ (1 - c ^ 2) * (lam2 - lam1) := by nlinarith [hmain]
  have hdiv : 1 - c ^ 2 ≤ 2 * eps / (lam2 - lam1) := by
    rw [le_div_iff₀ hgap]
    linarith
  have hc2 : ⟪x, v⟫ ^ 2 = c ^ 2 := by
    rw [hc]
    exact congrArg (· ^ 2) (real_inner_comm x v).symm
  rw [hc2]
  linarith

end Qatlib.Papers.LocalHam06.MainResults.Perturb
