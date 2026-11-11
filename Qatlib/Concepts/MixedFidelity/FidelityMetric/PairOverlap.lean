/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity

open Qatlib.Foundations.PureStateMath

/-!
# Pair Overlap

The actual squared distance between two finite amplitude vectors.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.PairOverlap

/-- The actual squared distance between two finite amplitude vectors. -/
def squareDistance {I : Type*} [Fintype I] (ψ φ : QState I) : ℝ :=
  ∑ i,‖ψ i-φ i‖^2

/-- Unit amplitude vectors relate their real overlap to their literal squared distance. -/
theorem real_inner_eq_one_sub_distance {I : Type*} [Fintype I]
    (ψ φ : QState I) (hψ : Normalized ψ) (hφ : Normalized φ) :
    (Qatlib.Foundations.PureStateMath.Inner ψ φ).re=1-squareDistance ψ φ/2 := by
  have hr (a b : ℂ) : (a*(starRingEnd ℂ) b).re=(star a*b).re := by
    simp [Complex.mul_re,RCLike.star_def,mul_comm]
  have hi (a b : ℂ) : ‖a-b‖^2=‖a‖^2+‖b‖^2-2*(star a*b).re := by
    simpa only [Complex.normSq_eq_norm_sq,hr] using Complex.normSq_sub a b
  have ht : squareDistance ψ φ=(∑ i,‖ψ i‖^2)+(∑ i,‖φ i‖^2)-
      2*(Qatlib.Foundations.PureStateMath.Inner ψ φ).re := by
    simp only [squareDistance,hi,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply,
      Complex.re_sum,Finset.mul_sum]
  change (∑ i,‖ψ i‖^2)=1 at hψ
  change (∑ i,‖φ i‖^2)=1 at hφ
  rw [hψ,hφ] at ht
  linarith

/-- The exact semicircle deficit associated with two real correlations. -/
def semicircleDeficit (ρ ξ : ℝ) : ℝ :=
  1-ρ*ξ-Real.sqrt ((1-ρ^2)*(1-ξ^2))

/-- The semicircle deficit is quadratic uniformly inside any fixed strict correlation radius. -/
theorem semicircleDeficit_bound (a ρ ξ : ℝ) (ha : a<1) (hρ : |ρ| ≤ a) (hξ : |ξ| ≤ a) :
    0 ≤ semicircleDeficit ρ ξ ∧
      semicircleDeficit ρ ξ ≤ (ρ-ξ)^2/(2*(1-a^2)) := by
  have ha0 : 0 ≤ a := (abs_nonneg ρ).trans hρ
  have hg : 0<1-a^2 := by nlinarith [mul_pos (by linarith : 0<1-a) (by linarith : 0<1+a)]
  have hρsq : ρ^2 ≤ a^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg ρ) hρ 2
  have hξsq : ξ^2 ≤ a^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg ξ) hξ 2
  have hρn : 0 ≤ 1-ρ^2 := by linarith
  have hξn : 0 ≤ 1-ξ^2 := by linarith
  let u := Real.sqrt (1-ρ^2)
  let v := Real.sqrt (1-ξ^2)
  let g := Real.sqrt (1-a^2)
  have hu : u^2=1-ρ^2 := Real.sq_sqrt hρn
  have hv : v^2=1-ξ^2 := Real.sq_sqrt hξn
  have hgg : g^2=1-a^2 := Real.sq_sqrt hg.le
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hgu : g ≤ u := Real.sqrt_le_sqrt (by linarith)
  have hgv : g ≤ v := Real.sqrt_le_sqrt (by linarith)
  have hden : 4*(1-a^2) ≤ (u+v)^2 := by nlinarith
  have hsum : (ρ+ξ)^2 ≤ 4*a^2 := by nlinarith [sq_nonneg (ρ-ξ)]
  have hid : (u-v)^2*(u+v)^2=(ρ-ξ)^2*(ρ+ξ)^2 := by
    calc _=(u^2-v^2)^2 := by ring
         _=_ := by rw [hu,hv]; ring
  have hmlo := mul_le_mul_of_nonneg_left hden (sq_nonneg (u-v))
  have hmhi := mul_le_mul_of_nonneg_left hsum (sq_nonneg (ρ-ξ))
  have hd : (1-a^2)*(u-v)^2 ≤ a^2*(ρ-ξ)^2 := by nlinarith [hid]
  have hc : semicircleDeficit ρ ξ=((ρ-ξ)^2+(u-v)^2)/2 := by
    rw [semicircleDeficit,Real.sqrt_mul hρn]
    change 1-ρ*ξ-u*v=((ρ-ξ)^2+(u-v)^2)/2
    nlinarith [hu,hv]
  constructor
  · rw [hc]
    positivity
  · rw [hc]
    apply (le_div_iff₀ (by positivity : 0<2*(1-a^2))).2
    nlinarith

end Qatlib.Concepts.MixedFidelity.FidelityMetric.PairOverlap
