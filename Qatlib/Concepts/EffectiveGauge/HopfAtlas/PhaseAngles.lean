/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.ArctanProgram
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local real-angle geometry with quantitative margins

Principal arguments occur only in a disk about 1. The true accumulated
phase is never replaced by a principal argument of the endpoint.
-/

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of complex Phase in the Hopf Atlas construction. -/
def complexPhase (t : ℝ) : ℂ := ⟨Real.cos t,Real.sin t⟩

/-- Original `complexPhase_re` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
@[simp] theorem complexPhase_re (t : ℝ) : (complexPhase t).re=Real.cos t := rfl
/-- Original `complexPhase_im` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
@[simp] theorem complexPhase_im (t : ℝ) : (complexPhase t).im=Real.sin t := rfl

/-- Original `complexPhase_eq_cos_sin` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
theorem complexPhase_eq_cos_sin (t : ℝ) : complexPhase t=(Real.cos t : ℂ)+(Real.sin t : ℂ)*Complex.I := by
  apply Complex.ext
  · change Real.cos t=Real.cos t+(Real.sin t*0-0*1)
    ring
  · change Real.sin t=0+(Real.sin t*1+0*0)
    ring

/-- Original `complexPhase_norm` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
@[simp] theorem complexPhase_norm (t : ℝ) : ‖complexPhase t‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [pow_two,Complex.norm_mul_self_eq_normSq,Complex.normSq_apply]
  change Real.cos t*Real.cos t+Real.sin t*Real.sin t=1^2
  nlinarith [Real.cos_sq_add_sin_sq t]

/-- Original `complexPhase_zero` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
@[simp] theorem complexPhase_zero : complexPhase 0=1 := by apply Complex.ext <;> norm_num [complexPhase]

/-- Original `complexPhase_add` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
theorem complexPhase_add (s t : ℝ) : complexPhase (s+t)=complexPhase s*complexPhase t := by
  apply Complex.ext
  · change Real.cos (s+t)=Real.cos s*Real.cos t-Real.sin s*Real.sin t
    exact Real.cos_add s t
  · change Real.sin (s+t)=Real.cos s*Real.sin t+Real.sin s*Real.cos t
    rw [Real.sin_add]
    ring

/-- Original `complexPhase_conj` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
@[simp] theorem complexPhase_conj (t : ℝ) : conj (complexPhase t)=complexPhase (-t) := by
  apply Complex.ext
  · change Real.cos t=Real.cos (-t)
    rw [Real.cos_neg]
  · change -Real.sin t=Real.sin (-t)
    rw [Real.sin_neg]

/-- Original `abs_arctan_le_abs` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
theorem abs_arctan_le_abs (x : ℝ) : |Real.arctan x| ≤ |x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 1)
    (fun y (_ : y ∈ (univ : Set ℝ)) => (Real.hasDerivAt_arctan y).hasDerivWithinAt)
    (fun y _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/(1+y^2))]
      simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) (show 1 ≤ 1+y^2 by nlinarith))
    convex_univ (mem_univ (0 : ℝ)) (mem_univ x)
  simpa only [Real.arctan_zero,sub_zero,one_mul,Real.norm_eq_abs] using h

/-- Original `arctan_ratio_eq_arg` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
theorem arctan_ratio_eq_arg (z : ℂ) (hz : 0<z.re) : Real.arctan (z.im/z.re)=z.arg := by
  have h := abs_lt.mp ((Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hz))
  rw [← Complex.tan_arg]
  exact Real.arctan_tan h.1 h.2

/-- Original `complex_right_half_repr` guarantee for the `PhaseAngles` construction; the complete source hypotheses are retained. -/
theorem complex_right_half_repr (z : ℂ) (hz : 0<z.re) :
    z=(‖z‖ : ℂ)*complexPhase (Real.arctan (z.im/z.re)) := by
  rw [arctan_ratio_eq_arg z hz]
  have h := (Complex.norm_mul_cos_add_sin_mul_I z).symm
  rw [← Complex.ofReal_cos,← Complex.ofReal_sin,← complexPhase_eq_cos_sin] at h
  exact h

/-- A noisy unit-circle sample produces a small, uniquely chosen real error
angle. The sample itself is not required to have unit magnitude. -/
theorem near_one_real_angle (z : ℂ) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1/2) (hz : ‖z-1‖ ≤ e) :
    0<z.re ∧ |Real.arctan (z.im/z.re)| ≤ 2*e ∧
      z=(‖z‖ : ℂ)*complexPhase (Real.arctan (z.im/z.re)) := by
  have hre : |z.re-1| ≤ e := by simpa using (Complex.abs_re_le_norm (z-1)).trans hz
  have him : |z.im| ≤ e := by simpa using (Complex.abs_im_le_norm (z-1)).trans hz
  have hden : 0<z.re := by linarith [(abs_le.mp hre).1]
  have hhalf : (1/2 : ℝ) ≤ z.re := by linarith [(abs_le.mp hre).1]
  have hratio : |z.im/z.re| ≤ 2*e := by
    rw [abs_div,abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg he (sub_nonneg.mpr hhalf)]
  exact ⟨hden,(abs_arctan_le_abs _).trans hratio,complex_right_half_repr z hden⟩

/-- The exact local angle and the algorithm's real/ratio guard have positive
margin. This bound is applied to a true phase increment plus two sample
error angles, rather than to a principal endpoint phase. -/
theorem small_scaled_phase_increment (r t : ℝ) (hr : 0<r) (ht : |t| ≤ 3/16) :
    0<((r : ℂ)*complexPhase t).re ∧
      |((r : ℂ)*complexPhase t).im/((r : ℂ)*complexPhase t).re| ≤ 1/2 ∧
      Real.arctan (((r : ℂ)*complexPhase t).im/((r : ℂ)*complexPhase t).re)=t := by
  have hsq : t^2 ≤ (3/16 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 3/16)).mpr ht
  have hc : (1/2 : ℝ) ≤ Real.cos t := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have hcp : 0<Real.cos t := by linarith
  have hs : |Real.sin t| ≤ 3/16 := (Real.abs_sin_le_abs).trans ht
  have hratio : ((r : ℂ)*complexPhase t).im/((r : ℂ)*complexPhase t).re=Real.sin t/Real.cos t := by
    simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,complexPhase_re,complexPhase_im,
      zero_mul,add_zero,sub_zero]
    exact mul_div_mul_left _ _ hr.ne'
  refine ⟨by simpa using mul_pos hr hcp,?_,?_⟩
  · rw [hratio,abs_div,abs_of_pos hcp]
    apply (div_le_iff₀ hcp).mpr
    linarith
  · rw [hratio,← Real.tan_eq_sin_div_cos]
    apply Real.arctan_tan <;> linarith [(abs_le.mp ht).1,(abs_le.mp ht).2,Real.pi_gt_three]

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
