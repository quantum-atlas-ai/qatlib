/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # Reciprocal comparison on an actual positive differentiable envelope

Demand: arXiv1011.3489v2, equation53. The historical target only bounded
the totalized `deriv` and assumed continuity; it omitted differentiability.
Here differentiability and positivity on the actual interval are explicit.
This corrected analytic core is not the old theorem or an adaptive quantum
simulation construction.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QDynamics10.MainResults.OdeCompare

/-- A positive differentiable profile with the actual quadratic derivative bound has a Lipschitz reciprocal. -/
theorem reciprocal (f : ℝ → ℝ) (a b K : ℝ) (hab : a ≤ b)
    (hp : ∀ x ∈ Set.Icc a b, 0 < f x)
    (hd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hb : ∀ x ∈ Set.Icc a b, |deriv f x| ≤ K^2 * f x^2) :
    |(f b)⁻¹-(f a)⁻¹| ≤ K^2*(b-a) := by
  have hh : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun s => (f s)⁻¹) (-deriv f x/(f x)^2) (Set.Icc a b) x := by
    intro x hx
    exact ((hd x hx).hasDerivAt.inv (ne_of_gt (hp x hx))).hasDerivWithinAt
  have hm : ∀ x ∈ Set.Ico a b, ‖-deriv f x/(f x)^2‖ ≤ K^2 := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := ⟨hx.1,hx.2.le⟩
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (sq_nonneg (f x))]
    exact (div_le_iff₀ (sq_pos_of_pos (hp x hx'))).mpr (hb x hx')
  simpa only [Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_le_segment' hh hm b (Set.right_mem_Icc.mpr hab)

/-- The actual reciprocal bound gives both rational comparisons before the positive-envelope blowup time. -/
theorem compare (f : ℝ → ℝ) (K t dt : ℝ) (hdt : 0 ≤ dt)
    (hp : ∀ x ∈ Set.Icc t (t+dt), 0 < f x)
    (hd : ∀ x ∈ Set.Icc t (t+dt), DifferentiableAt ℝ f x)
    (hb : ∀ x ∈ Set.Icc t (t+dt), |deriv f x| ≤ K^2*f x^2)
    (hs : K^2*f t*dt < 1) :
    f t/(1+K^2*f t*dt) ≤ f (t+dt) ∧
      f (t+dt) ≤ f t/(1-K^2*f t*dt) := by
  have ht : t ≤ t+dt := le_add_of_nonneg_right hdt
  have hft := hp t (Set.left_mem_Icc.mpr ht)
  have hfb := hp (t+dt) (Set.right_mem_Icc.mpr ht)
  have h := reciprocal f t (t+dt) K ht hp hd hb
  rw [add_sub_cancel_left] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  have hmul : 0 ≤ K^2*f t*dt := mul_nonneg (mul_nonneg (sq_nonneg K) hft.le) hdt
  have hplus : 0 < 1+K^2*f t*dt := by linarith
  have hminus : 0 < 1-K^2*f t*dt := sub_pos.mpr hs
  have hlo : f t ≤ f (t+dt)*(1+K^2*f t*dt) := by
    have h := mul_le_mul_of_nonneg_right hu (mul_pos hft hfb).le
    field_simp at h
    nlinarith
  have hhi : f (t+dt)*(1-K^2*f t*dt) ≤ f t := by
    have h := mul_le_mul_of_nonneg_right hl (mul_pos hft hfb).le
    field_simp at h
    nlinarith
  exact ⟨(div_le_iff₀ hplus).mpr hlo,(le_div_iff₀ hminus).mpr hhi⟩

end Qatlib.Papers.QDynamics10.MainResults.OdeCompare
