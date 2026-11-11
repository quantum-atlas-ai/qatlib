/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.RelativeTransport

/-!
# Inhomogeneous quaternion transport

The differentiated field need not have unit norm. Multiplication by the
conjugate of the unit fundamental solution removes the skew coefficient
and gives a linear-in-time forcing bound without Gronwall amplification.
-/
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Original `inhomogeneous_transport_derivative` guarantee for the `InhomogeneousTransport` construction; the complete source hypotheses are retained. -/
theorem inhomogeneous_transport_derivative {q z : ℝ → ℍ} {k f : ℍ} {t : ℝ} {S : Set ℝ}
    (hq : HasDerivWithinAt q (q t*k) S t)
    (hz : HasDerivWithinAt z (z t*k+f) S t) (hk : k.re=0) :
    HasDerivWithinAt (fun u => z u*star (q u)) (f*star (q t)) S t := by
  have hstar : star k = -k := by ext <;> simp [hk]
  convert hz.mul hq.star using 1
  simp only [star_mul,hstar]
  noncomm_ring

/-- Original `inhomogeneous_transport_integral` guarantee for the `InhomogeneousTransport` construction; the complete source hypotheses are retained. -/
theorem inhomogeneous_transport_integral {q z k f : ℝ → ℍ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (q t*k t) (Icc a b) t)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (z t*k t+f t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, (k t).re=0) :
    (∫ t in a..b, f t*star (q t)) = z b*star (q b)-z a*star (q a) := by
  have hqc : ContinuousOn q (Icc a b) := HasDerivWithinAt.continuousOn hq
  have hzc : ContinuousOn z (Icc a b) := HasDerivWithinAt.continuousOn hz
  apply integral_eq_sub_of_hasDerivAt_of_le hab (hzc.mul hqc.star)
  · intro t ht
    exact (inhomogeneous_transport_derivative (hq t ⟨ht.1.le,ht.2.le⟩)
      (hz t ⟨ht.1.le,ht.2.le⟩) (hp t ⟨ht.1.le,ht.2.le⟩)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact (hf.mul hqc.star).intervalIntegrable_of_Icc hab

/-- No norm assumption is imposed on the forced solution z. -/
theorem inhomogeneous_transport_norm_le {q z k f : ℝ → ℍ} {a b E : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (q t*k t) (Icc a b) t)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (z t*k t+f t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, (k t).re=0)
    (hnq : ∀ t ∈ Icc a b, ‖q t‖=1) (hinit : z a=0)
    (he : ∀ t ∈ Icc a b, ‖f t‖ ≤ E) :
    ‖z b‖ ≤ (b-a)*E := by
  have hi := inhomogeneous_transport_integral hab hf hq hz hp
  rw [hinit,zero_mul,sub_zero] at hi
  calc
    _ = ‖z b*star (q b)‖ := by
      rw [norm_mul,Quaternion.norm_star,hnq b ⟨hab,le_rfl⟩,mul_one]
    _ = ‖∫ t in a..b, f t*star (q t)‖ := congrArg norm hi.symm
    _ ≤ E*|b-a| := by
      apply norm_integral_le_of_norm_le_const
      intro t ht
      have ht' : t ∈ Icc a b := ⟨(uIoc_of_le hab ▸ ht).1.le,(uIoc_of_le hab ▸ ht).2⟩
      simpa only [norm_mul,Quaternion.norm_star,hnq t ht',mul_one] using he t ht'
    _ = (b-a)*E := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; ring

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
