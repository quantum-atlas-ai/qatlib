/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Integer winding numbers for absolutely continuous curves

Proves the almost-everywhere derivative formula for complex indefinite integrals and the
exponential identity for winding numbers of absolutely continuous curves. Closed curves avoiding
the reference point consequently have integer winding number.

These results support the contour-integration framework associated with [WangEtAl2026].

## Main statements

* `IntervalIntegrable.ae_hasDerivAt_integral_complex`: The indefinite integral of an
  interval-integrable complex function has derivative `f x` at almost every `x` in the interval,
  for every basepoint in that interval.
* `AbsolutelyContinuousOnInterval.exp_two_pi_I_mul_windingNumber`: For an absolutely continuous
  curve avoiding `z`, exponentiating `2πi` times its winding number gives the ratio of its
  endpoint displacements from `z`.
* `AbsolutelyContinuousOnInterval.exists_int_windingNumber`: The winding number of a closed
  absolutely continuous curve about a point outside its image is an integer.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

/-- The indefinite integral of an interval-integrable complex function has derivative `f x` at
almost every `x` in the interval, for every basepoint in that interval. -/
theorem IntervalIntegrable.ae_hasDerivAt_integral_complex {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    ∀ᵐ x, x ∈ Set.uIcc a b → ∀ c ∈ Set.uIcc a b,
      HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  have hR : IntervalIntegrable (fun t => (f t).re) MeasureTheory.volume a b :=
    ⟨hf.1.re, hf.2.re⟩
  have hI : IntervalIntegrable (fun t => (f t).im) MeasureTheory.volume a b :=
    ⟨hf.1.im, hf.2.im⟩
  filter_upwards [hR.ae_hasDerivAt_integral, hI.ae_hasDerivAt_integral,
    MeasureTheory.volume.ae_ne (min a b), MeasureTheory.volume.ae_ne (max a b)]
      with x hxR hxI hxa hxb hx c hc
  have hxint : x ∈ Set.Ioo (min a b) (max a b) :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have hd := (hxR hx c hc).ofReal_comp.add ((hxI hx c hc).ofReal_comp.mul_const Complex.I)
  rw [Complex.re_add_im] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxint.1 hxint.2] with y hy
  have hfy := hf.mono_set (Set.uIcc_subset_uIcc hc ⟨hy.1.le, hy.2.le⟩)
  have hr := Complex.reCLM.intervalIntegral_comp_comm hfy
  have hi := Complex.imCLM.intervalIntegral_comp_comm hfy
  change (∫ t in c..y, f t) =
    (↑(∫ t in c..y, (f t).re) : ℂ) + ↑(∫ t in c..y, (f t).im) * Complex.I
  change (∫ t in c..y, (f t).re) = (∫ t in c..y, f t).re at hr
  change (∫ t in c..y, (f t).im) = (∫ t in c..y, f t).im at hi
  rw [hr, hi, Complex.re_add_im]

open Complex MeasureTheory Set

namespace TauCeti.Contour

/-- For an absolutely continuous curve avoiding `z`, exponentiating `2πi` times its winding
number gives the ratio of its endpoint displacements from `z`. -/
theorem _root_.AbsolutelyContinuousOnInterval.exp_two_pi_I_mul_windingNumber
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hz : z ∉ γ '' uIcc a b) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z) =
      (γ b - z) / (γ a - z) := by
  let f : ℝ → ℂ := fun t ↦ (γ t - z)⁻¹ * deriv γ t
  let A : ℝ → ℂ := fun t ↦ ∫ v in a..t, f v
  have hf : IntervalIntegrable f volume a b :=
    AbsolutelyContinuousOnInterval.intervalIntegrable_inv_sub_mul_deriv hγ hz
  have hA : AbsolutelyContinuousOnInterval A a b :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral' hf left_mem_uIcc
  have hexp : AbsolutelyContinuousOnInterval (fun t ↦ Complex.exp (-A t)) a b :=
    AbsolutelyContinuousOnInterval.comp_of_contDiffAt hA.neg fun _ _ ↦ (Complex.contDiff_exp (𝕜 := ℝ) (n := 1)).contDiffAt
  have hsub : AbsolutelyContinuousOnInterval (fun t ↦ γ t - z) a b :=
    hγ.fun_sub (LipschitzWith.const (α := ℝ) z).lipschitzOnWith.absolutelyContinuousOnInterval
  have hfactor : AbsolutelyContinuousOnInterval
      (fun t ↦ (γ t - z) * Complex.exp (-A t)) a b := hsub.smul hexp
  have hzero : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun t ↦ (γ t - z) * Complex.exp (-A t)) 0 t := by
    filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
      IntervalIntegrable.ae_hasDerivAt_integral_complex hf]
      with t hdt hAt ht
    have hne : γ t - z ≠ 0 := sub_ne_zero.mpr (fun heq ↦ hz ⟨t, ht, heq⟩)
    convert! ((hdt ht).hasDerivAt.sub_const z).mul ((hAt ht a left_mem_uIcc).neg.cexp) using 1
    try dsimp [f]
    (try field_simp)
    ring
  obtain ⟨C, hC⟩ := hfactor.const_of_ae_hasDerivAt_zero hzero
  have ha := hC a left_mem_uIcc
  have hb := hC b right_mem_uIcc
  have ha0 : A a = 0 := by simp [A]
  rw [ha0, neg_zero, Complex.exp_zero, mul_one] at ha
  have hratio : Complex.exp (A b) = (γ b - z) / (γ a - z) := by
    have hne : γ a - z ≠ 0 := sub_ne_zero.mpr (fun heq ↦ hz ⟨a, left_mem_uIcc, heq⟩)
    rw [← ha, Complex.exp_neg] at hb
    rw [eq_div_iff hne]
    calc
      Complex.exp (A b) * (γ a - z) =
          Complex.exp (A b) * ((γ b - z) * (Complex.exp (A b))⁻¹) := by rw [hb]
      _ = γ b - z := by field_simp
  rw [AbsolutelyContinuousOnInterval.windingNumber_eq_integral hγ hz,
    ← mul_assoc, mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  exact hratio

/-- The winding number of a closed absolutely continuous curve about a point outside its image
is an integer. -/
theorem _root_.AbsolutelyContinuousOnInterval.exists_int_windingNumber
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hz : z ∉ γ '' uIcc a b) :
    ∃ n : ℤ, windingNumber γ a b z = n := by
  have h := AbsolutelyContinuousOnInterval.exp_two_pi_I_mul_windingNumber hγ hz
  rw [← hclosed, div_self (sub_ne_zero.mpr (fun heq ↦ hz ⟨a, left_mem_uIcc, heq⟩))] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
  rw [hn, mul_comm]

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
