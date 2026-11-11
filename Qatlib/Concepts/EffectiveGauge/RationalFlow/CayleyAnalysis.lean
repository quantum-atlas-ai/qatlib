/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CayleyExecution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Cayley interpolation and sharp local transport error

Every step is compared on its own continuous interval. No discontinuous
piecewise-constant coefficient is passed to a continuous-ODE theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of cayley Generator in the Rational Flow construction. -/
def cayleyGenerator (k : ℍ) (t : ℝ) : ℍ := (4/cayleyDenominator k t) • k

/-- Original `scalarPlane_mul_pure` guarantee for the `CayleyAnalysis` construction; the complete source hypotheses are retained. -/
private theorem scalarPlane_mul_pure (a b c : ℝ) (k : ℍ) (hk : k.re=0) :
    (a • (1 : ℍ)+b • k)*(c • k)=(-b*c*Quaternion.normSq k) • (1 : ℍ)+(a*c) • k := by
  have hs : k*k=(-Quaternion.normSq k) • (1 : ℍ) := by
    ext <;> simp [Quaternion.normSq_def',hk] <;> ring
  simp only [add_mul,smul_mul_assoc,mul_smul_comm,one_mul,smul_smul,hs]
  module

/-- Original `cayleyFactor_hasDerivAt` guarantee for the `CayleyAnalysis` construction; the complete source hypotheses are retained. -/
theorem cayleyFactor_hasDerivAt (k : ℍ) (hk : k.re=0) (t : ℝ) :
    HasDerivAt (cayleyFactor k) (cayleyFactor k t*cayleyGenerator k t) t := by
  let n := Quaternion.normSq k
  have hn := (cayleyDenominator_pos k t).ne'
  have hd : HasDerivAt (cayleyDenominator k) (2*n*t) t := by
    apply ((hasDerivAt_const t (4 : ℝ)).add (((hasDerivAt_id t).pow 2).const_mul n)).congr_deriv
    norm_num [id]
    ring
  have ha : HasDerivAt (fun u : ℝ => 4-n*u^2) (-(2*n*t)) t := by
    apply ((hasDerivAt_const t (4 : ℝ)).sub (((hasDerivAt_id t).pow 2).const_mul n)).congr_deriv
    norm_num [id]
    ring
  have hb : HasDerivAt (fun u : ℝ => 4*u) 4 t := by simpa using (hasDerivAt_id t).const_mul 4
  have h := ((ha.div hd hn).smul_const (1 : ℍ)).add ((hb.div hd hn).smul_const k)
  have hA : ((-(2*n*t))*cayleyDenominator k t-(4-n*t^2)*(2*n*t))/(cayleyDenominator k t)^2 =
      -((4*t)/cayleyDenominator k t)*(4/cayleyDenominator k t)*n := by
    field_simp [hn]
    dsimp [cayleyDenominator,n]
    ring
  have hB : (4*cayleyDenominator k t-(4*t)*(2*n*t))/(cayleyDenominator k t)^2 =
      ((4-n*t^2)/cayleyDenominator k t)*(4/cayleyDenominator k t) := by
    field_simp [hn]
    dsimp [cayleyDenominator,n]
    ring
  rw [hA,hB] at h
  exact h.congr_deriv (scalarPlane_mul_pure _ _ _ k hk).symm

/-- Original `continuous_cayleyGenerator` guarantee for the `CayleyAnalysis` construction; the complete source hypotheses are retained. -/
theorem continuous_cayleyGenerator (k : ℍ) : Continuous (cayleyGenerator k) := by
  have hd : Continuous (cayleyDenominator k) := continuous_const.add (continuous_const.mul (continuous_id.pow 2))
  exact (continuous_const.div hd (fun t => (cayleyDenominator_pos k t).ne')).smul continuous_const

/-- Original `cayleyGenerator_re` guarantee for the `CayleyAnalysis` construction; the complete source hypotheses are retained. -/
theorem cayleyGenerator_re (k : ℍ) (hk : k.re=0) (t : ℝ) : (cayleyGenerator k t).re=0 := by
  simp [cayleyGenerator,hk]

/-- Original `cayleyGenerator_error` guarantee for the `CayleyAnalysis` construction; the complete source hypotheses are retained. -/
theorem cayleyGenerator_error (k : ℍ) (t : ℝ) :
    ‖cayleyGenerator k t-k‖ ≤ ‖k‖^3*t^2/4 := by
  have hn := cayleyDenominator_pos k t
  have hu : 0 ≤ Quaternion.normSq k*t^2 := mul_nonneg (Quaternion.normSq_nonneg (a := k)) (sq_nonneg t)
  have hd : 4 ≤ cayleyDenominator k t := by dsimp [cayleyDenominator]; linarith
  have he : 4/cayleyDenominator k t-1=-(Quaternion.normSq k*t^2/cayleyDenominator k t) := by
    field_simp [hn.ne']
    dsimp [cayleyDenominator]
    ring
  have hr : Quaternion.normSq k*t^2/cayleyDenominator k t ≤ Quaternion.normSq k*t^2/4 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hd)]
  calc
    _ = ‖(4/cayleyDenominator k t-1) • k‖ := by rw [sub_smul,one_smul]; rfl
    _ = (Quaternion.normSq k*t^2/cayleyDenominator k t)*‖k‖ := by
      rw [norm_smul,Real.norm_eq_abs,he,abs_neg,abs_of_nonneg (div_nonneg hu hn.le)]
    _ ≤ (Quaternion.normSq k*t^2/4)*‖k‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg k)
    _ = ‖k‖^3*t^2/4 := by rw [Quaternion.normSq_eq_norm_mul_self]; ring

/-- Integrating the true coefficient difference gives a sharp local error. -/
theorem unit_transport_integral_bound {q r k l : ℝ → ℍ} {a b : ℝ} (hab : a ≤ b)
    (hk : ContinuousOn k (Icc a b)) (hl : ContinuousOn l (Icc a b))
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (q t*k t) (Icc a b) t)
    (hr : ∀ t ∈ Icc a b, HasDerivWithinAt r (r t*l t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, (k t).re=0)
    (hnq : ∀ t ∈ Icc a b, ‖q t‖=1) (hnr : ∀ t ∈ Icc a b, ‖r t‖=1)
    (hinit : r a=q a) : ‖r b-q b‖ ≤ ∫ t in a..b, ‖l t-k t‖ := by
  have ha : r a*star (q a)=1 := by
    rw [hinit,Quaternion.self_mul_star,(normSq_eq_one_iff _).mpr (hnq a ⟨le_rfl,hab⟩)]; rfl
  have hb : star (q b)*q b=1 := by
    rw [Quaternion.star_mul_self,(normSq_eq_one_iff _).mpr (hnq b ⟨hab,le_rfl⟩)]; rfl
  have he : (r b*star (q b)-1)*q b=r b-q b := by rw [sub_mul,mul_assoc,hb,mul_one,one_mul]
  have hi := relative_transport_integral hab hk hl hq hr hp
  rw [ha] at hi
  calc
    _ = ‖r b*star (q b)-1‖ := by rw [← he,norm_mul,hnq b ⟨hab,le_rfl⟩,mul_one]
    _ = ‖∫ t in a..b, r t*(l t-k t)*star (q t)‖ := congrArg norm hi.symm
    _ ≤ ∫ t in a..b, ‖r t*(l t-k t)*star (q t)‖ := norm_integral_le_integral_norm hab
    _ = _ := integral_congr (by
      intro t ht
      rw [uIcc_of_le hab] at ht
      simp only [norm_mul,Quaternion.norm_star,hnq t ht,hnr t ht,one_mul,mul_one])

/-- Original `cayleyStep_error` guarantee for the `CayleyAnalysis` construction; the complete source hypotheses are retained. -/
theorem cayleyStep_error {q k : ℝ → ℍ} {h M e B : ℝ} (hh : 0 ≤ h)
    (hk : ContinuousOn k (Icc 0 h)) (hp : ∀ t ∈ Icc 0 h, (k t).re=0)
    (hq : ∀ t ∈ Icc 0 h, HasDerivWithinAt q (q t*k t) (Icc 0 h) t)
    (hnq : ∀ t ∈ Icc 0 h, ‖q t‖=1) (v : ℍ) (hv : v.re=0)
    (hB : ‖v‖ ≤ B) (he : ∀ t ∈ Icc 0 h, ‖v-k t‖ ≤ M*t+e) :
    ‖q 0*cayleyFactor v h-q h‖ ≤ M*h^2/2+e*h+B^3*h^3/12 := by
  let r := fun t => q 0*cayleyFactor v t
  have hr : ∀ t ∈ Icc 0 h, HasDerivWithinAt r (r t*cayleyGenerator v t) (Icc 0 h) t := by
    intro t ht
    simpa only [r,mul_assoc] using ((cayleyFactor_hasDerivAt v hv t).const_mul (q 0)).hasDerivWithinAt
  have hnr : ∀ t ∈ Icc 0 h, ‖r t‖=1 := by
    intro t ht
    simp only [r,norm_mul,hnq 0 ⟨le_rfl,hh⟩,cayleyFactor_unit v hv t,one_mul]
  have hinit : r 0=q 0 := by simp [r]
  have hi := unit_transport_integral_bound hh hk (continuous_cayleyGenerator v).continuousOn hq hr hp hnq hnr hinit
  have hgen : ∀ t ∈ Icc 0 h, ‖cayleyGenerator v t-k t‖ ≤ M*t+e+B^3*t^2/4 := by
    intro t ht
    calc
      _ ≤ ‖cayleyGenerator v t-v‖+‖v-k t‖ := by
        simpa only [dist_eq_norm] using dist_triangle (cayleyGenerator v t) v (k t)
      _ ≤ ‖v‖^3*t^2/4+(M*t+e) := add_le_add (cayleyGenerator_error v t) (he t ht)
      _ ≤ M*t+e+B^3*t^2/4 := by
        have hb := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg v) hB 3) (sq_nonneg t)
        linarith
  have hf : IntervalIntegrable (fun t => ‖cayleyGenerator v t-k t‖) MeasureTheory.volume 0 h :=
    ((continuous_cayleyGenerator v).continuousOn.sub hk).norm.intervalIntegrable_of_Icc hh
  have hg : IntervalIntegrable (fun t : ℝ => M*t+e+B^3*t^2/4) MeasureTheory.volume 0 h := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hm := integral_mono_on hh hf hg hgen
  have hvint : (∫ t in (0 : ℝ)..h, M*t+e+B^3*t^2/4)=M*h^2/2+e*h+B^3*h^3/12 := by
    rw [integral_add (f := fun t : ℝ => M*t+e) (g := fun t : ℝ => B^3*t^2/4)
      (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      integral_add (by apply Continuous.intervalIntegrable; fun_prop) (continuous_const.intervalIntegrable _ _),
      integral_const_mul,integral_id,integral_const,integral_div,integral_const_mul,integral_pow]
    norm_num
    ring
  exact hi.trans (hm.trans_eq hvint)

end Qatlib.Concepts.EffectiveGauge.RationalFlow
