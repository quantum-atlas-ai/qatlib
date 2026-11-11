/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Existence

/-!
# Relative transport and coefficient stability

An exact relative-product identity controls the dependence on coefficients
without an exponential loss. It is a bridge toward parameter regularity,
not yet a theorem asserting smooth dependence on transverse parameters.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Original `relative_transport_derivative` guarantee for the `RelativeTransport` construction; the complete source hypotheses are retained. -/
theorem relative_transport_derivative {q r : ℝ → ℍ} {k l : ℍ} {t : ℝ} {S : Set ℝ}
    (hq : HasDerivWithinAt q (q t*k) S t)
    (hr : HasDerivWithinAt r (r t*l) S t) (hk : k.re=0) :
    HasDerivWithinAt (fun u => r u*star (q u)) (r t*(l-k)*star (q t)) S t := by
  have hstar : star k = -k := by ext <;> simp [hk]
  convert hr.mul hq.star using 1
  simp only [star_mul, hstar]
  noncomm_ring

/-- Exact coefficient-variation identity on the complete closed interval. -/
theorem relative_transport_integral {q r k l : ℝ → ℍ} {a b : ℝ} (hab : a ≤ b)
    (hk : ContinuousOn k (Icc a b)) (hl : ContinuousOn l (Icc a b))
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (q t*k t) (Icc a b) t)
    (hr : ∀ t ∈ Icc a b, HasDerivWithinAt r (r t*l t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, (k t).re=0) :
    (∫ t in a..b, r t*(l t-k t)*star (q t)) = r b*star (q b)-r a*star (q a) := by
  have hqc : ContinuousOn q (Icc a b) := HasDerivWithinAt.continuousOn hq
  have hrc : ContinuousOn r (Icc a b) := HasDerivWithinAt.continuousOn hr
  apply integral_eq_sub_of_hasDerivAt_of_le hab (hrc.mul hqc.star)
  · intro t ht
    exact (relative_transport_derivative (hq t ⟨ht.1.le, ht.2.le⟩)
      (hr t ⟨ht.1.le, ht.2.le⟩) (hp t ⟨ht.1.le, ht.2.le⟩)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact ((hrc.mul (hl.sub hk)).mul hqc.star).intervalIntegrable_of_Icc hab

/-- Unit solutions with the same initial point differ by at most elapsed time
times the uniform coefficient error. The unit hypotheses can be obtained from
`right_transport_exists`; this conditional estimate does not construct a solution. -/
theorem unit_transport_stability {q r k l : ℝ → ℍ} {a b E : ℝ} (hab : a ≤ b)
    (hk : ContinuousOn k (Icc a b)) (hl : ContinuousOn l (Icc a b))
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (q t*k t) (Icc a b) t)
    (hr : ∀ t ∈ Icc a b, HasDerivWithinAt r (r t*l t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, (k t).re=0)
    (hnq : ∀ t ∈ Icc a b, ‖q t‖=1) (hnr : ∀ t ∈ Icc a b, ‖r t‖=1)
    (hinit : r a=q a) (he : ∀ t ∈ Icc a b, ‖l t-k t‖ ≤ E) :
    ‖r b-q b‖ ≤ (b-a)*E := by
  have ha : r a*star (q a)=1 := by
    rw [hinit, Quaternion.self_mul_star, (normSq_eq_one_iff _).mpr (hnq a ⟨le_rfl, hab⟩)]
    rfl
  have hb : star (q b)*q b=1 := by
    rw [Quaternion.star_mul_self, (normSq_eq_one_iff _).mpr (hnq b ⟨hab, le_rfl⟩)]
    rfl
  have heq : (r b*star (q b)-1)*q b=r b-q b := by
    rw [sub_mul, mul_assoc, hb, mul_one, one_mul]
  have hi := relative_transport_integral hab hk hl hq hr hp
  rw [ha] at hi
  calc
    _ = ‖r b*star (q b)-1‖ := by
      rw [← heq, norm_mul, hnq b ⟨hab, le_rfl⟩, mul_one]
    _ = ‖∫ t in a..b, r t*(l t-k t)*star (q t)‖ := congrArg norm hi.symm
    _ ≤ E*|b-a| := by
      apply norm_integral_le_of_norm_le_const
      intro t ht
      have ht' : t ∈ Icc a b := ⟨(uIoc_of_le hab ▸ ht).1.le, (uIoc_of_le hab ▸ ht).2⟩
      simpa only [norm_mul, Quaternion.norm_star, hnq t ht', hnr t ht', one_mul, mul_one]
        using he t ht'
    _ = (b-a)*E := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; ring

/-- Quadratic remainder for the actual linearization in coefficient paths.
This endpoint statement is the quantitative core of the subsequent
continuous-path Frechet derivative; it does not itself define that operator. -/
theorem unit_transport_quadratic_remainder {q r k l : ℝ → ℍ} {a b E : ℝ} (hab : a ≤ b)
    (hk : ContinuousOn k (Icc a b)) (hl : ContinuousOn l (Icc a b))
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (q t*k t) (Icc a b) t)
    (hr : ∀ t ∈ Icc a b, HasDerivWithinAt r (r t*l t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, (k t).re=0)
    (hnq : ∀ t ∈ Icc a b, ‖q t‖=1) (hnr : ∀ t ∈ Icc a b, ‖r t‖=1)
    (hinit : r a=q a) (he : ∀ t ∈ Icc a b, ‖l t-k t‖ ≤ E) :
    ‖r b-q b-(∫ t in a..b, q t*(l t-k t)*star (q t))*q b‖ ≤ (b-a)^2*E^2 := by
  have hqc : ContinuousOn q (Icc a b) := HasDerivWithinAt.continuousOn hq
  have hrc : ContinuousOn r (Icc a b) := HasDerivWithinAt.continuousOn hr
  have hG : IntervalIntegrable (fun t => r t*(l t-k t)*star (q t)) MeasureTheory.volume a b :=
    ((hrc.mul (hl.sub hk)).mul hqc.star).intervalIntegrable_of_Icc hab
  have hH : IntervalIntegrable (fun t => q t*(l t-k t)*star (q t)) MeasureTheory.volume a b :=
    ((hqc.mul (hl.sub hk)).mul hqc.star).intervalIntegrable_of_Icc hab
  have ha : r a*star (q a)=1 := by
    rw [hinit, Quaternion.self_mul_star, (normSq_eq_one_iff _).mpr (hnq a ⟨le_rfl, hab⟩)]
    rfl
  have hb : star (q b)*q b=1 := by
    rw [Quaternion.star_mul_self, (normSq_eq_one_iff _).mpr (hnq b ⟨hab, le_rfl⟩)]
    rfl
  have hi := relative_transport_integral hab hk hl hq hr hp
  rw [ha] at hi
  have hdelta : r b-q b=(∫ t in a..b, r t*(l t-k t)*star (q t))*q b := by
    rw [hi, sub_mul, mul_assoc, hb, mul_one, one_mul]
  have hid : (∫ t in a..b, r t*(l t-k t)*star (q t))-
      (∫ t in a..b, q t*(l t-k t)*star (q t)) =
      ∫ t in a..b, (r t-q t)*(l t-k t)*star (q t) := by
    rw [← integral_sub hG hH]
    congr 1
    funext t
    noncomm_ring
  have hE : 0 ≤ E := (norm_nonneg _).trans (he a ⟨le_rfl, hab⟩)
  have hdiff : ∀ t ∈ Icc a b, ‖r t-q t‖ ≤ (b-a)*E := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := fun _ hu => ⟨hu.1, hu.2.trans ht.2⟩
    have h := unit_transport_stability ht.1 (hk.mono hsub) (hl.mono hsub)
      (fun u hu => (hq u (hsub hu)).mono hsub)
      (fun u hu => (hr u (hsub hu)).mono hsub)
      (fun u hu => hp u (hsub hu)) (fun u hu => hnq u (hsub hu))
      (fun u hu => hnr u (hsub hu)) hinit (fun u hu => he u (hsub hu))
    exact h.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right ht.2 a) hE)
  rw [hdelta, ← sub_mul, hid, norm_mul, hnq b ⟨hab, le_rfl⟩, mul_one]
  calc
    _ ≤ ((b-a)*E*E)*|b-a| := by
      apply norm_integral_le_of_norm_le_const
      intro t ht
      have ht' : t ∈ Icc a b := ⟨(uIoc_of_le hab ▸ ht).1.le, (uIoc_of_le hab ▸ ht).2⟩
      simp only [norm_mul, Quaternion.norm_star, hnq t ht', mul_one]
      exact mul_le_mul (hdiff t ht') (he t ht') (norm_nonneg _)
        (mul_nonneg (sub_nonneg.mpr hab) hE)
    _ = (b-a)^2*E^2 := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; ring

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
