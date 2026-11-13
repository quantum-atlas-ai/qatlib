/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.TelegraphLimit.TelegraphMode
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-band comparison of telegraph and heat modes

This module lifts scalar telegraph-to-heat estimates to finite complex Euclidean states through
`weightedState`. It proves positivity of the telegraph multiplier and a relative norm estimate
for bands with rates between zero and `A`, subject to `4 * δ * A ≤ 3/4`.

The mathematical background is discussed in [JinLiu2024].

## Main statements

* `mode_pos`: positivity of the telegraph multiplier at nonnegative times.
* `relative_norm`: passes a coordinatewise relative bound to the Euclidean norm.
* `finite_band_relative`: compares telegraph and heat evolution on a finite band.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.TimeEvolution.TelegraphLimit

/-- For positive `δ`, nonnegative `a` and time, and `4 * δ * a ≤ 3/4`, the telegraph mode is
strictly positive. -/
theorem mode_pos {δ a t : ℝ} (hδ : 0<δ) (ha : 0≤a) (hm : 4*δ*a≤3/4) (ht : 0≤t) :
    0 < mode δ a t := by
  obtain ⟨_,hgf,hc0,_,_⟩ := rate_bounds hδ ha hm
  have he : Real.exp (-fast δ a*t)≤Real.exp (-slow δ a*t) := Real.exp_le_exp.mpr (by nlinarith)
  have hp := Real.exp_pos (-slow δ a*t)
  have hh := mul_nonneg hc0 (sub_nonneg.mpr he)
  dsimp [mode]
  nlinarith

/-- Multiply each coordinate of a complex Euclidean state by the corresponding real weight. -/
def weightedState {I : Type} (f : I→ℝ) (x : EuclideanSpace ℂ I) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i=>(f i:ℂ)*x i)

/-- Coordinatewise multiplication by nonzero real weights preserves a nonzero state. See
[JinLiu2024]. -/
theorem weightedState_ne_zero {I : Type} (f : I→ℝ) (hf : ∀i,f i≠0)
    (x : EuclideanSpace ℂ I) (hx : x≠0) : weightedState f x≠0 := by
  intro hz
  apply hx
  ext i
  have h := congrArg (fun y : EuclideanSpace ℂ I=>y i) hz
  change (f i:ℂ)*x i=0 at h
  exact (mul_eq_zero.mp h).resolve_left (Complex.ofReal_ne_zero.mpr (hf i))

/-- A coordinatewise relative error bound with nonnegative constant `C` implies the same
relative bound in the Euclidean norm. -/
theorem relative_norm {I : Type} [Fintype I] (U H : EuclideanSpace ℂ I) {C : ℝ} (hC : 0≤C)
    (h : ∀i,‖U i-H i‖≤C*‖H i‖) : ‖U-H‖≤C*‖H‖ := by
  have hsq : ‖U-H‖^2≤(C*‖H‖)^2 := by
    rw [EuclideanSpace.norm_sq_eq,mul_pow,EuclideanSpace.norm_sq_eq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := h i
    change ‖U i-H i‖^2≤C^2*‖H i‖^2
    nlinarith [norm_nonneg (U i-H i)]
  nlinarith [norm_nonneg (U-H),mul_nonneg hC (norm_nonneg H)]

/-- For rates in `[0, A]`, positive `δ`, nonnegative time, and `4 * δ * A ≤ 3/4`, the
telegraph-to-heat norm error is at most `(4 * δ * A + 4 * δ * A ^ 2 * t)` times the
heat-state norm. -/
theorem finite_band_relative {I : Type} [Fintype I] (a : I→ℝ) (x : EuclideanSpace ℂ I)
    {δ A t : ℝ} (hδ : 0<δ) (hA : 0≤A) (ha : ∀i,0≤a i ∧ a i≤A)
    (hm : 4*δ*A≤3/4) (ht : 0≤t) :
    ‖weightedState (fun i=>mode δ (a i) t) x-weightedState (fun i=>heatMode (a i) t) x‖≤
      (4*δ*A+4*δ*A^2*t)*‖weightedState (fun i=>heatMode (a i) t) x‖ := by
  apply relative_norm _ _ (by positivity)
  intro i
  have hi := mode_error hδ (ha i).1 (show 4*δ*a i≤3/4 from
    (mul_le_mul_of_nonneg_left (ha i).2 (by positivity : 0≤4*δ)).trans hm) ht
  have hb : 4*δ*a i+4*δ*(a i)^2*t≤4*δ*A+4*δ*A^2*t := by
    gcongr <;> first | exact (ha i).1 | exact (ha i).2
  have he : 0<heatMode (a i) t := Real.exp_pos _
  change ‖((mode δ (a i) t:ℝ):ℂ)*x i-((heatMode (a i) t:ℝ):ℂ)*x i‖≤
    (4*δ*A+4*δ*A^2*t)*‖((heatMode (a i) t:ℝ):ℂ)*x i‖
  rw [← sub_mul,← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
  calc
    |mode δ (a i) t-heatMode (a i) t| *‖x i‖≤
      ((4*δ*a i+4*δ*(a i)^2*t)*heatMode (a i) t)*‖x i‖ :=
      mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    _≤((4*δ*A+4*δ*A^2*t)*heatMode (a i) t)*‖x i‖ := by gcongr
    _=(4*δ*A+4*δ*A^2*t)*(heatMode (a i) t*‖x i‖) := by ring
end Qatlib.Foundations.TimeEvolution.TelegraphLimit
