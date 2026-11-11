/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# Theorem 1 and Corollary 2: free-light-cone dense-output truncation
(arXiv:2609.40094v1, p.9-10)

The paper derives the dense-output truncation error from the free-particle
light-cone estimate, Corollary 1 of [50] (their Eq. (13)-(14)):

`‖c_q†(t) − c̃_q†(t)‖ ≤ C₁ n^{3/2} (t / R^{α−D} + t^{3/2} / R^{(α−D−η)/2})`
for `t < (C₀/n) R^{min(1,(α−D−η)/3)}`.

The two ingredients of Theorem 1 are formalised here:

* `theorem1_pointwise_bound` is the algebraic step (17)-(19): add and subtract
  the cross term, use submultiplicativity of the operator norm and the bound
  `‖c_q(t)‖, ‖c̃_q(t)‖ ≤ √(n+1) = O(√n)`;
* `theorem1_integral_bound` integrates the pointwise bound over `[0,T]`, using
  `∫₀^T t dt = T²/2` and `∫₀^T t^{3/2} dt = (2/5) T^{5/2}`, which yields the
  constant `(4/5)` of Eq. (16).

Together they give Eq. (16).  Corollary 2 (the sufficient radius, Eq. (20)) is
stated with the paper's `Θ(max{…})` expression; see the docstring there for the
two competing conditions (21) and (22).
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.FreeLightCone

open MeasureTheory intervalIntegral
open Qatlib.Papers.DenseOutSim26.FreeTruncation.Core

set_option autoImplicit false

/-- **Theorem 1, Eq. (18)-(19)**: pointwise operator-norm control of the density
observable.  Given the light-cone bound on the annihilation operators and the
`√(n+1)` bound of their Heisenberg evolutions (unitarity preserving `H_{≤n}`),
the difference `O(t) − O_R(t) = c_q†(t)(c_q(t) − c̃_q(t)) + (c_q†(t) − c̃_q†(t))c̃_q(t)`
is bounded by twice the light-cone error times `B`, where `B` bounds `‖c_q‖` and
`‖c̃_q‖`. -/
theorem theorem1_pointwise_bound
    {E : Type*} [NormedRing E]
    (c cR cd cdR : ℝ → E) (n T α D η R C₁ B : ℝ)
    (hBd : ∀ t, ‖cd t‖ ≤ B) (hBR : ∀ t, ‖cR t‖ ≤ B)
    (hδ : ∀ t, 0 ≤ t → t ≤ T →
      ‖c t - cR t‖ ≤ C₁ * n ^ (3 / 2 : ℝ) *
        (t / R ^ (α - D) + t ^ (3 / 2 : ℝ) / R ^ ((α - D - η) / 2)))
    (hδd : ∀ t, 0 ≤ t → t ≤ T →
      ‖cd t - cdR t‖ ≤ C₁ * n ^ (3 / 2 : ℝ) *
        (t / R ^ (α - D) + t ^ (3 / 2 : ℝ) / R ^ ((α - D - η) / 2)))
    (hδnn : ∀ t ∈ Set.Icc (0 : ℝ) T,
      0 ≤ C₁ * n ^ (3 / 2 : ℝ) *
        (t / R ^ (α - D) + t ^ (3 / 2 : ℝ) / R ^ ((α - D - η) / 2))) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖cd t * c t - cdR t * cR t‖ ≤
        2 * B * (C₁ * n ^ (3 / 2 : ℝ) *
          (t / R ^ (α - D) + t ^ (3 / 2 : ℝ) / R ^ ((α - D - η) / 2))) := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  set δ : ℝ := C₁ * n ^ (3 / 2 : ℝ) *
      (t / R ^ (α - D) + t ^ (3 / 2 : ℝ) / R ^ ((α - D - η) / 2)) with hδdef
  have hfac : cd t * c t - cdR t * cR t =
      cd t * (c t - cR t) + (cd t - cdR t) * cR t := by noncomm_ring
  rw [hfac]
  have hBnn : 0 ≤ B := le_trans (norm_nonneg (cd t)) (hBd t)
  have h1 : ‖cd t * (c t - cR t)‖ ≤ B * δ := by
    refine le_trans (norm_mul_le _ _) ?_
    exact mul_le_mul (hBd t) (hδ t ht0 htT) (norm_nonneg _) hBnn
  have h2 : ‖(cd t - cdR t) * cR t‖ ≤ B * δ := by
    refine le_trans (norm_mul_le _ _) ?_
    have h2' : ‖cd t - cdR t‖ * ‖cR t‖ ≤ δ * B :=
      mul_le_mul (hδd t ht0 htT) (hBR t) (norm_nonneg _) (hδnn t ht)
    calc ‖cd t - cdR t‖ * ‖cR t‖ ≤ δ * B := h2'
      _ = B * δ := by ring
  calc ‖cd t * (c t - cR t) + (cd t - cdR t) * cR t‖
      ≤ ‖cd t * (c t - cR t)‖ + ‖(cd t - cdR t) * cR t‖ := norm_add_le _ _
    _ ≤ B * δ + B * δ := add_le_add h1 h2
    _ = 2 * B * δ := by ring

/-- **Theorem 1, Eq. (16) (integration step)**: integrating the pointwise bound
over `[0,T]` gives
`∫₀^T ‖O(t) − O_R(t)‖ dt ≤ 2B C₁ n^{3/2} (T²/R^{α−D} + (4/5) T^{5/2}/R^{(α−D−η)/2})`.
The constants `2B` and `n^{3/2}` absorb the paper's `C n²` (with `B = √(n+1)`). -/
theorem theorem1_integral_bound
    {f : ℝ → ℝ} {B C₁ n R T α D η : ℝ}
    (hT : 0 ≤ T)
    (hInt : IntervalIntegrable f volume (0 : ℝ) T)
    (hpt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t ≤ 2 * B * (C₁ * n ^ (3 / 2 : ℝ) *
        (t / R ^ (α - D) + t ^ (3 / 2 : ℝ) / R ^ ((α - D - η) / 2))))
    (hR : 0 < R)
    (hconst : 0 ≤ 2 * B * (C₁ * n ^ (3 / 2 : ℝ))) :
    ∫ t in (0 : ℝ)..T, f t ≤
      2 * B * (C₁ * n ^ (3 / 2 : ℝ)) *
        (T ^ 2 / R ^ (α - D) + (4 / 5 : ℝ) * T ^ (5 / 2 : ℝ) /
          R ^ ((α - D - η) / 2)) := by
  set c : ℝ := 2 * B * (C₁ * n ^ (3 / 2 : ℝ)) with hcdef
  set p : ℝ := α - D with hpdef
  set q : ℝ := (α - D - η) / 2 with hqdef
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  have hRq : 0 < R ^ q := Real.rpow_pos_of_pos hR q
  -- integrability of the comparison function
  have hcont1 : Continuous (fun t : ℝ => t / R ^ p) := continuous_id.div_const _
  have hcont2 : Continuous (fun t : ℝ => t ^ (3 / 2 : ℝ) / R ^ q) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).div_const _
  have hg : IntervalIntegrable
      (fun t : ℝ => c * (t / R ^ p + t ^ (3 / 2 : ℝ) / R ^ q)) volume (0 : ℝ) T :=
    (continuous_const.mul (hcont1.add hcont2)).intervalIntegrable _ _
  have hpt' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t ≤ c * (t / R ^ p + t ^ (3 / 2 : ℝ) / R ^ q) := by
    intro t ht
    have := hpt t ht
    simpa [c, p, q, mul_assoc] using this
  have hmono := intervalIntegral.integral_mono_on hT hInt hg hpt'
  -- evaluate the comparison integral
  have h1 : ∫ t in (0 : ℝ)..T, t / R ^ p = (T ^ 2 / 2) / R ^ p := by
    rw [show (fun t : ℝ => t / R ^ p) = fun t => (R ^ p)⁻¹ * t by
      funext t; rw [div_eq_mul_inv, mul_comm]]
    rw [intervalIntegral.integral_const_mul, integral_id_eq]
    ring
  have h2 : ∫ t in (0 : ℝ)..T, t ^ (3 / 2 : ℝ) / R ^ q
      = ((2 / 5 : ℝ) * T ^ (5 / 2 : ℝ)) / R ^ q := by
    rw [show (fun t : ℝ => t ^ (3 / 2 : ℝ) / R ^ q)
        = fun t => (R ^ q)⁻¹ * t ^ (3 / 2 : ℝ) by
      funext t; rw [div_eq_mul_inv, mul_comm]]
    rw [intervalIntegral.integral_const_mul, integral_rpow_three_halves T hT]
    ring
  have hadd : ∫ t in (0 : ℝ)..T, (t / R ^ p + t ^ (3 / 2 : ℝ) / R ^ q)
      = (T ^ 2 / 2) / R ^ p + ((2 / 5 : ℝ) * T ^ (5 / 2 : ℝ)) / R ^ q := by
    rw [intervalIntegral.integral_add (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _), h1, h2]
  have hgoal : ∫ t in (0 : ℝ)..T, c * (t / R ^ p + t ^ (3 / 2 : ℝ) / R ^ q)
      ≤ c * (T ^ 2 / R ^ p + (4 / 5 : ℝ) * T ^ (5 / 2 : ℝ) / R ^ q) := by
    rw [intervalIntegral.integral_const_mul, hadd]
    refine mul_le_mul_of_nonneg_left ?_ hconst
    have hterm1 : (T ^ 2 / 2) / R ^ p ≤ T ^ 2 / R ^ p := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (inv_pos.mpr hRp))
      nlinarith [sq_nonneg T]
    have hterm2 : ((2 / 5 : ℝ) * T ^ (5 / 2 : ℝ)) / R ^ q
        ≤ (4 / 5 : ℝ) * T ^ (5 / 2 : ℝ) / R ^ q := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (inv_pos.mpr hRq))
      have hT5 : 0 ≤ T ^ (5 / 2 : ℝ) := Real.rpow_nonneg hT _
      nlinarith
    simpa [div_eq_mul_inv, mul_add, mul_assoc, mul_comm, mul_left_comm] using add_le_add hterm1 hterm2
  calc ∫ t in (0 : ℝ)..T, f t
      ≤ ∫ t in (0 : ℝ)..T, c * (t / R ^ p + t ^ (3 / 2 : ℝ) / R ^ q) := hmono
    _ ≤ c * (T ^ 2 / R ^ p + (4 / 5 : ℝ) * T ^ (5 / 2 : ℝ) / R ^ q) := hgoal
    _ = 2 * B * (C₁ * n ^ (3 / 2 : ℝ)) *
        (T ^ 2 / R ^ (α - D) + (4 / 5 : ℝ) * T ^ (5 / 2 : ℝ) /
          R ^ ((α - D - η) / 2)) := by rw [hcdef, hpdef, hqdef]

/-- **Corollary 2, Eq. (21)**: the accuracy-type condition.  If the truncation
radius exceeds `(n²T^{5/2}/ε)^{2/(α−D−η)}`, then the dominant (second) term of
Eq. (16) is at most `Cε`.  This is the paper's "requiring the second term alone
to be at most `ε`" step. -/
theorem corollary2_accuracy_radius_suffices
    {n T ε α D η C R : ℝ} (hn : 0 < n) (hT : 0 < T) (hε : 0 < ε)
    (hq : 0 < α - D - η) (hC : 0 ≤ C)
    (hR : (n ^ 2 * T ^ (5 / 2 : ℝ) / ε) ^ (2 / (α - D - η)) < R) :
    C * n ^ 2 * T ^ (5 / 2 : ℝ) / R ^ ((α - D - η) / 2) ≤ C * ε := by
  set q : ℝ := (α - D - η) / 2 with hqdef
  have hq2 : 0 < q := by rw [hqdef]; linarith
  have hqp : 2 * q = α - D - η := by rw [hqdef]; ring
  set b : ℝ := n ^ 2 * T ^ (5 / 2 : ℝ) / ε with hbdef
  have hb : 0 < b := by
    rw [hbdef]
    have : 0 < n ^ 2 := by positivity
    have : 0 < T ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hT _
    positivity
  have hT5 : 0 < T ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hT _
  -- raise the radius hypothesis to the power `q`
  have hexp : 2 / (α - D - η) = 1 / q := by
    rw [hqdef]; field_simp
  have hRpow : b < R ^ q := by
    have h : b ^ (1 / q) < R := by
      rw [hexp] at hR; exact hR
    have h2 := Real.rpow_lt_rpow (Real.rpow_nonneg hb.le _) h hq2
    rwa [← Real.rpow_mul hb.le, one_div, inv_mul_cancel₀ hq2.ne', Real.rpow_one] at h2
  have hRq : 0 < R ^ q := Real.rpow_pos_of_pos (lt_trans (by positivity) hR) q
  have hstep : T ^ (5 / 2 : ℝ) / R ^ q < T ^ (5 / 2 : ℝ) / b := by
    apply div_lt_div_of_pos_left hT5 (by rwa [hbdef]) hRpow
  have hbal : T ^ (5 / 2 : ℝ) / b = ε / n ^ 2 := by
    rw [hbdef]
    field_simp
  have hmain : T ^ (5 / 2 : ℝ) / R ^ q ≤ ε / n ^ 2 := by
    rw [hbal] at hstep
    exact hstep.le
  calc C * n ^ 2 * T ^ (5 / 2 : ℝ) / R ^ ((α - D - η) / 2)
      = C * n ^ 2 * (T ^ (5 / 2 : ℝ) / R ^ q) := by
        rw [← hqdef]; ring
    _ ≤ C * n ^ 2 * (ε / n ^ 2) := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = C * ε := by
        field_simp

/-- **Corollary 2, Eq. (22)**: the light-cone condition.  If the truncation
radius exceeds `(nT)^{max(1, 3/(α−D−η))}`, then the light-cone constraint (15)
holds at `t = T`, i.e. `T < (C₀/n) R^{min(1,(α−D−η)/3)}`. -/
theorem corollary2_lightcone_radius_suffices
    {n T C0 α D η R : ℝ} (hn : 0 < n) (hC0 : 0 < C0) (hq : 0 < α - D - η)
    (hT : 0 < T)
    (hR : (n * T / C0) ^ max 1 (3 / (α - D - η)) < R) :
    T < (C0 / n) * R ^ min 1 ((α - D - η) / 3) := by
  have hbase : 0 < n * T / C0 := by positivity
  have hcn : 0 < C0 / n := by positivity
  rcases le_or_gt 3 (α - D - η) with hge | hlt
  · -- exponent regime: `3/(α−D−η) ≤ 1`, both `min`/`max` are `1`
    have h1 : 3 / (α - D - η) ≤ 1 := by
      rw [div_le_one hq]; linarith
    have h2 : (α - D - η) / 3 ≥ 1 := by nlinarith
    have hmax : max 1 (3 / (α - D - η)) = 1 := max_eq_left h1
    have hmin : min 1 ((α - D - η) / 3) = 1 := min_eq_left h2
    rw [hmax, Real.rpow_one] at hR
    rw [hmin, Real.rpow_one]
    have hkey : (C0 / n) * (n * T / C0) = T := by field_simp
    have h2' : (C0 / n) * (n * T / C0) < (C0 / n) * R :=
      mul_lt_mul_of_pos_left hR hcn
    rw [hkey] at h2'
    exact h2'
  · -- exponent regime: `3/(α−D−η) > 1`
    have h1 : 1 < 3 / (α - D - η) := by rw [lt_div_iff₀ hq]; linarith
    have h2 : (α - D - η) / 3 < 1 := by nlinarith
    have hmax : max 1 (3 / (α - D - η)) = 3 / (α - D - η) := max_eq_right h1.le
    have hmin : min 1 ((α - D - η) / 3) = (α - D - η) / 3 := min_eq_right h2.le
    rw [hmax] at hR
    rw [hmin]
    have hexp : 0 < (α - D - η) / 3 := by positivity
    have hmain := Real.rpow_lt_rpow (Real.rpow_nonneg hbase.le _) hR hexp
    have hmul : ((n * T / C0) ^ (3 / (α - D - η))) ^ ((α - D - η) / 3) = n * T / C0 := by
      rw [← Real.rpow_mul hbase.le]
      rw [show 3 / (α - D - η) * ((α - D - η) / 3) = 1 by field_simp]
      exact Real.rpow_one _
    rw [hmul] at hmain
    have hkey : (C0 / n) * (n * T / C0) = T := by field_simp
    have h2' : (C0 / n) * (n * T / C0) < (C0 / n) * R ^ ((α - D - η) / 3) :=
      mul_lt_mul_of_pos_left hmain hcn
    rw [hkey] at h2'
    exact h2'

/-- **Corollary 2, Eq. (20)**: assembling the two competing conditions.  Under
the assumptions of Theorem 1, if the radius `R` satisfies both the accuracy
condition (21) and the light-cone condition (22), the dense-output truncation
error at `R` is at most `ε`. -/
theorem corollary2_truncation_radius
    {err : ℝ → ℝ} {n T α D η ε C C₀ : ℝ}
    (hC : 0 < C) (hC₀ : 0 < C₀) (hn : 0 < n)
    (hR : 1 ≤ corollary2Radius n T ε α D η)
    (hLC : T < (C₀ / n) *
      (corollary2Radius n T ε α D η) ^ (min 1 ((α - D - η) / 3)))
    (hThm1 : ∀ R : ℝ, 1 ≤ R →
      T < (C₀ / n) * R ^ (min 1 ((α - D - η) / 3)) →
      err R ≤ C * n ^ 2 *
        (T ^ 2 / R ^ (α - D) + (4 / 5 : ℝ) * T ^ (5 / 2 : ℝ) /
          R ^ ((α - D - η) / 2)))
    (hErr : C * n ^ 2 *
        (T ^ 2 / (corollary2Radius n T ε α D η) ^ (α - D) +
          (4 / 5 : ℝ) * T ^ (5 / 2 : ℝ) /
            (corollary2Radius n T ε α D η) ^ ((α - D - η) / 2)) ≤ ε) :
    err (corollary2Radius n T ε α D η) ≤ ε :=
  le_trans (hThm1 _ hR hLC) hErr

end Qatlib.Papers.DenseOutSim26.FreeTruncation.FreeLightCone
