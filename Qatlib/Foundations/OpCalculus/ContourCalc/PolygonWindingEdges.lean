/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


/-! Scalar affine-edge winding from finite endpoint branch-crossing data.
The branch correction has positive sign for a downward negative-axis crossing. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Foundations.OpCalculus.ContourCalc.PolygonWinding
open Complex Set MeasureTheory

/-- Construction for edge Path in the polygon winding edges model. -/
def edgePath (a b : ℂ) (t : ℝ) : ℂ := a+(t : ℂ)*(b-a)

/-- Construction for crossing Real in the polygon winding edges model. -/
def crossingReal (a b : ℂ) : ℝ := (a.re*b.im-b.re*a.im)/(b.im-a.im)

/-- Construction for crossing Sign in the polygon winding edges model. -/
def crossingSign (a b : ℂ) : ℤ :=
  if a.im*b.im < 0 ∧ crossingReal a b < 0 then
    (if 0 < a.im then 1 else -1) else 0

/-- The identity or estimate `edgePath_hasDerivAt` holds with the displayed separation, geometry and norm hypotheses. -/
theorem edgePath_hasDerivAt (a b : ℂ) (t : ℝ) : HasDerivAt (edgePath a b) (b-a) t := by
  change HasDerivAt (fun x : ℝ => a + (x : ℂ) * (b-a)) (b-a) t
  convert ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (b-a)).const_add a using 1 <;>
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]

/-- The identity or estimate `opposite_of_zero_im` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem opposite_of_zero_im (a b : ℂ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : a.im ≠ 0) (hb : b.im ≠ 0) (hz : (edgePath a b t).im = 0) :
    a.im*b.im < 0 ∧ b.im-a.im ≠ 0 := by
  have he : (1-t)*a.im+t*b.im = 0 := by
    simp only [edgePath, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, zero_mul, add_zero] at hz
    nlinarith
  have ht0 : 0 < t := by
    by_contra hn
    have ht' : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
    rw [ht'] at he
    simp only [sub_zero, one_mul, zero_mul, add_zero] at he
    exact ha he
  have ht1 : t < 1 := by
    by_contra hn
    have ht' : t = 1 := le_antisymm ht.2 (le_of_not_gt hn)
    rw [ht'] at he
    simp only [sub_self, zero_mul, one_mul, zero_add] at he
    exact hb he
  have hopp : a.im*b.im < 0 := by
    by_contra hn
    have hnon : 0 ≤ a.im*b.im := le_of_not_gt hn
    have hp := mul_nonneg (sub_pos.mpr ht1).le hnon
    have hq := mul_pos ht0 (sq_pos_of_ne_zero hb)
    have hm : ((1-t)*a.im+t*b.im)*b.im = 0 := by rw [he, zero_mul]
    nlinarith
  refine ⟨hopp, ?_⟩
  intro hd
  have heq : b.im = a.im := sub_eq_zero.mp hd
  rw [heq] at hopp
  nlinarith [sq_nonneg a.im]

/-- The identity or estimate `zero_im_re_eq_crossing` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem zero_im_re_eq_crossing (a b : ℂ) (t : ℝ)
    (hd : b.im-a.im ≠ 0) (hz : (edgePath a b t).im = 0) :
    (edgePath a b t).re = crossingReal a b := by
  have he : a.im+t*(b.im-a.im) = 0 := by
    simpa only [edgePath, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, zero_mul, zero_add, add_zero] using hz
  have ht : t = -a.im/(b.im-a.im) := (eq_div_iff hd).mpr (by linarith)
  rw [ht]
  simp only [edgePath, crossingReal, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero]
  field_simp [hd]
  ring

/-- The identity or estimate `edgePath_slit_of_crossing_pos` holds with the displayed separation, geometry and norm hypotheses. -/
theorem edgePath_slit_of_crossing_pos (a b : ℂ) (ha : a.im ≠ 0) (hb : b.im ≠ 0)
    (hcross : a.im*b.im < 0 → 0 < crossingReal a b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : edgePath a b t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hz : (edgePath a b t).im = 0
  · obtain ⟨hopp, hd⟩ := opposite_of_zero_im a b t ht ha hb hz
    exact Or.inl ((zero_im_re_eq_crossing a b t hd hz).symm ▸ hcross hopp)
  · exact Or.inr hz

/-- The identity or estimate `edge_log_integral_of_slit` holds with the displayed separation, geometry and norm hypotheses. -/
theorem edge_log_integral_of_slit (a b : ℂ)
    (hslit : ∀ t ∈ Icc (0 : ℝ) 1, edgePath a b t ∈ Complex.slitPlane) :
    (∫ t in (0 : ℝ)..1, (b-a)/edgePath a b t) = Complex.log b-Complex.log a := by
  have hp : Continuous (edgePath a b) :=
    (show Differentiable ℝ (edgePath a b) from fun t => (edgePath_hasDerivAt a b t).differentiableAt).continuous
  have hc : ContinuousOn (fun t : ℝ => (b-a)/edgePath a b t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hp.continuousOn (fun t ht => Complex.slitPlane_ne_zero (hslit t ht))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (fun t ht => (edgePath_hasDerivAt a b t).clog_real
      (hslit t (by simpa only [uIcc_of_le zero_le_one] using ht)))
    (ContinuousOn.intervalIntegrable_of_Icc zero_le_one hc)
  have h0 : edgePath a b 0 = a := by simp [edgePath]
  have h1 : edgePath a b 1 = b := by
    simp only [edgePath, Complex.ofReal_one, one_mul]
    ring
  simpa only [h0, h1] using he

/-- The identity or estimate `log_neg_of_im_pos` holds with the displayed separation, geometry and norm hypotheses. -/
theorem log_neg_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z-(Real.pi : ℂ)*Complex.I := by
  unfold Complex.log
  rw [norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
  push_cast
  ring

/-- The identity or estimate `log_neg_of_im_neg` holds with the displayed separation, geometry and norm hypotheses. -/
theorem log_neg_of_im_neg (z : ℂ) (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z+(Real.pi : ℂ)*Complex.I := by
  unfold Complex.log
  rw [norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]
  push_cast
  ring

/-- The identity or estimate `crossingReal_neg` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem crossingReal_neg (a b : ℂ) : crossingReal (-a) (-b) = -crossingReal a b := by
  unfold crossingReal
  simp only [Complex.neg_re, Complex.neg_im, neg_mul_neg]
  have hd : -b.im-(-a.im) = -(b.im-a.im) := by ring
  rw [hd, div_neg]

/-- Finite endpoint tests determine the actual affine-edge integral.
No winding value or pathwise branch oracle is supplied as an input. -/
theorem edge_integral_crossing (a b : ℂ) (ha : a.im ≠ 0) (hb : b.im ≠ 0)
    (hsafe : a.im*b.im < 0 → crossingReal a b ≠ 0) :
    (∫ t in (0 : ℝ)..1, (b-a)/edgePath a b t) =
      Complex.log b-Complex.log a+
        (2*(Real.pi : ℂ)*Complex.I)*(crossingSign a b : ℂ) := by
  by_cases hneg : a.im*b.im < 0 ∧ crossingReal a b < 0
  · have hslit : ∀ t ∈ Icc (0 : ℝ) 1, edgePath (-a) (-b) t ∈ Complex.slitPlane := by
      apply edgePath_slit_of_crossing_pos (-a) (-b) (by simpa using ha) (by simpa using hb)
      intro _
      rw [crossingReal_neg]
      linarith [hneg.2]
    have he := edge_log_integral_of_slit (-a) (-b) hslit
    have hp (t : ℝ) : edgePath (-a) (-b) t = -edgePath a b t := by unfold edgePath; ring
    have hd : -b-(-a) = -(b-a) := by ring
    simp_rw [hp, hd, div_neg, neg_div, neg_neg] at he
    rw [he]
    by_cases hapos : 0 < a.im
    · have hbneg : b.im < 0 := by nlinarith [hneg.1]
      rw [log_neg_of_im_neg b hbneg, log_neg_of_im_pos a hapos]
      simp only [crossingSign, ite_eq_left hneg, ite_eq_left hapos, Int.cast_one, mul_one]
      ring
    · have haneg : a.im < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
      have hbpos : 0 < b.im := by nlinarith [hneg.1]
      rw [log_neg_of_im_pos b hbpos, log_neg_of_im_neg a haneg]
      simp only [crossingSign, ite_eq_left hneg, ite_eq_right hapos, Int.cast_neg, Int.cast_one]
      ring
  · have hpos : a.im*b.im < 0 → 0 < crossingReal a b := by
      intro hopp
      have hge : 0 ≤ crossingReal a b := le_of_not_gt (fun hlt => hneg ⟨hopp, hlt⟩)
      exact lt_of_le_of_ne hge (Ne.symm (hsafe hopp))
    have he := edge_log_integral_of_slit a b (edgePath_slit_of_crossing_pos a b ha hb hpos)
    simpa only [crossingSign, ite_eq_right hneg, Int.cast_zero, mul_zero, add_zero] using he

end Qatlib.Foundations.OpCalculus.ContourCalc.PolygonWinding
