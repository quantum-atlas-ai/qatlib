/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhaseLogProgram
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CircleLogReconstruction

/-! # Phase-log execution targets the actual real angular primitive -/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ComplexConjugate ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of circle Complex in the Hopf Atlas construction. -/
def circleComplex (q : ℍ) : ℂ := ⟨q.re,q.imI⟩

/-- Original `circleComplex_phase` guarantee for the `PhaseLogPrimitive` construction; the complete source hypotheses are retained. -/
theorem circleComplex_phase (t : ℝ) : circleComplex (phase t)=complexPhase t := by
  apply Complex.ext <;> simp [circleComplex,phase,iAxis,complexPhase]

/-- Original `circleComplex_norm_le` guarantee for the `PhaseLogPrimitive` construction; the complete source hypotheses are retained. -/
theorem circleComplex_norm_le (q : ℍ) : ‖circleComplex q‖ ≤ ‖q‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pow_two,pow_two,Complex.norm_mul_self_eq_normSq,← Quaternion.normSq_eq_norm_mul_self,
    Complex.normSq_apply,Quaternion.normSq_def']
  simp only [pow_two]
  change q.re*q.re+q.imI*q.imI ≤ q.re*q.re+q.imI*q.imI+q.imJ*q.imJ+q.imK*q.imK
  nlinarith [sq_nonneg q.imJ,sq_nonneg q.imK]

/-- Original `circleComplex_sub` guarantee for the `PhaseLogPrimitive` construction; the complete source hypotheses are retained. -/
theorem circleComplex_sub (q r : ℍ) : circleComplex (q-r)=circleComplex q-circleComplex r := by
  apply Complex.ext <;> rfl

/-- Original `abs_imI_le_norm` guarantee for the `PhaseLogPrimitive` construction; the complete source hypotheses are retained. -/
private theorem abs_imI_le_norm (q : ℍ) : |q.imI| ≤ ‖q‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  simp only [pow_two]
  rw [← Quaternion.normSq_eq_norm_mul_self,Quaternion.normSq_def']
  nlinarith [sq_abs q.imI,sq_nonneg q.re,sq_nonneg q.imJ,sq_nonneg q.imK]

/-- Original `circleAngularRate_abs_le` guarantee for the `PhaseLogPrimitive` construction; the complete source hypotheses are retained. -/
theorem circleAngularRate_abs_le (k : TransversePoint → ℍ) (p : TransversePoint) (hn : ‖k p‖=1) :
    |circleAngularRate k p| ≤ ‖fderiv ℝ k p (EuclideanSpace.single 0 1)‖ := by
  apply (abs_imI_le_norm _).trans
  rw [norm_mul,Quaternion.norm_star,hn,one_mul]

/-- Original `fderiv_scaled_argument` guarantee for the `PhaseLogPrimitive` construction; the complete source hypotheses are retained. -/
theorem fderiv_scaled_argument (k : TransversePoint → ℍ) (hk : ContDiff ℝ ∞ k)
    (c : ℝ) (p h : TransversePoint) :
    fderiv ℝ (fun q => k (c • q)) p h=c • (fderiv ℝ k (c • p) h) := by
  have hs : HasFDerivAt (fun q : TransversePoint => c • q) (c • ContinuousLinearMap.id ℝ TransversePoint) p :=
    (hasFDerivAt_id p).const_smul c
  have hd := ((hk.differentiable (by simp) (c • p)).hasFDerivAt).comp p hs
  dsimp only [Function.comp_def] at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_smul]

/-- Original `transversePair_scale` guarantee for the `PhaseLogPrimitive` construction; the complete source hypotheses are retained. -/
theorem transversePair_scale (c y z : ℝ) :
    c • transversePair (y,z)=transversePair (c*y,c*z) := by ext i; fin_cases i <;> rfl

/-- Original `circleAngularRate_scaled` guarantee for the `PhaseLogPrimitive` construction; the complete source hypotheses are retained. -/
theorem circleAngularRate_scaled (k : TransversePoint → ℍ) (hk : ContDiff ℝ ∞ k) (c : ℝ) (p : TransversePoint) :
    circleAngularRate (fun q => k (c • q)) p=c*circleAngularRate k (c • p) := by
  unfold circleAngularRate
  rw [fderiv_scaled_argument k hk c p]
  simp only [mul_smul_comm,Quaternion.imI_smul,smul_eq_mul]

/-- Exact real primitives commute with parameter rescaling. This equality
does not identify only their exponentials and hence retains integer turns. -/
theorem circleLogPrimitive_scaled (k : TransversePoint → ℍ) (hk : ContDiff ℝ ∞ k) (c y z : ℝ) :
    circleLogPrimitive (fun q => k (c • q)) (transversePair (y,z))=
      circleLogPrimitive k (transversePair (c*y,c*z)) := by
  change (∫ u in (0 : ℝ)..y, circleAngularRate (fun q => k (c • q)) (transversePair (u,z)))=_
  calc
    _ = ∫ u in (0 : ℝ)..y, c*circleAngularRate k (transversePair (c*u,c*z)) := by
      apply intervalIntegral.integral_congr
      intro u _
      change circleAngularRate (fun q => k (c • q)) (transversePair (u,z))=
        c*circleAngularRate k (transversePair (c*u,c*z))
      rw [circleAngularRate_scaled k hk c,transversePair_scale]
    _ = c*(∫ u in (0 : ℝ)..y, circleAngularRate k (transversePair (c*u,c*z))) := intervalIntegral.integral_const_mul _ _
    _ = ∫ u in (0 : ℝ)..(c*y), circleAngularRate k (transversePair (u,c*z)) := by
      have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := y)
        (fun u => circleAngularRate k (transversePair (u,c*z))) c
      simpa only [smul_eq_mul,mul_zero] using h
    _ = _ := rfl

/-- Original `phaseGrid_mem` guarantee for the `PhaseLogPrimitive` construction; the complete source hypotheses are retained. -/
private theorem phaseGrid_mem (endpoint : ℚ) (hy : 0 ≤ endpoint) (D : ℕ) (hD : 0<D)
    (j : ℕ) (hj : j ≤ D) :
    (endpoint : ℝ)*((j : ℝ)/(D : ℝ)) ∈ Icc 0 (endpoint : ℝ) := by
  have hd : (0 : ℝ)<D := by exact_mod_cast hD
  have hyR : (0 : ℝ) ≤ endpoint := by exact_mod_cast hy
  constructor
  · positivity
  · have h : (j : ℝ)/(D : ℝ) ≤ 1 := (div_le_one hd).mpr (by exact_mod_cast hj)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h hyR

/-- No real lift is an oracle input: theta is explicitly the existing integral
primitive of the supplied circle curve. Its base value and full turns survive. -/
theorem rationalPhaseLog_primitive (k : TransversePoint → ℍ) (hk : ContDiff ℝ ∞ k)
    (hc : ∀ p, IsCircleQuaternion (k p)) (z : ℝ) (h0 : k (transversePair (0,z))=1)
    (oracle : ℚ × ℕ → RationalCircleSample) (endpoint bound tau : ℚ)
    (hy : 0 ≤ endpoint) (hQ : 0 ≤ bound) (ht : 0<tau)
    (hd : ∀ y ∈ Icc 0 (endpoint : ℝ),
      ‖fderiv ℝ k (transversePair (y,z)) (EuclideanSpace.single 0 1)‖ ≤ (bound : ℝ))
    (horacle : ∀ (t : ℚ), (t : ℝ) ∈ Icc 0 (endpoint : ℝ) → ∀ b,
      ‖rationalCircleCast (oracle (t,b))-circleComplex (k (transversePair ((t : ℝ),z)))‖ ≤ (2^b : ℝ)⁻¹) :
    ∃ r, rationalPhaseLog oracle endpoint bound tau=some r ∧
      |(r.value : ℝ)-circleLogPrimitive k (transversePair ((endpoint : ℝ),z))| ≤ (r.errorBound : ℝ) ∧ r.errorBound ≤ tau ∧
      r.steps=phaseLogSteps endpoint bound ∧ r.precision=phaseLogPrecision tau ∧
      r.terms ≤ r.steps*arctanFuel (tau/(2*(r.steps : ℚ))) := by
  let D := phaseLogSteps endpoint bound
  let b := phaseLogPrecision tau
  let F := fun t : ℝ => circleLogPrimitive k (transversePair (t,z))
  let theta := fun j : ℕ => F ((endpoint : ℝ)*((j : ℝ)/(D : ℝ)))
  have hD : 0<D := phaseLogSteps_pos endpoint bound
  have hDr : (0 : ℝ)<D := by exact_mod_cast hD
  have hyR : (0 : ℝ) ≤ endpoint := by exact_mod_cast hy
  have hQR : (0 : ℝ) ≤ bound := by exact_mod_cast hQ
  have hlip : ∀ s ∈ Icc 0 (endpoint : ℝ), ∀ t ∈ Icc 0 (endpoint : ℝ),
      |F t-F s| ≤ (bound : ℝ)*|t-s| := by
    intro s hs t ht
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u (_ : u ∈ Icc 0 (endpoint : ℝ)) => (circleLogPrimitive_hasDerivAt hk z u).hasDerivWithinAt)
      (fun u hu => by
        rw [Real.norm_eq_abs]
        exact (circleAngularRate_abs_le k _ (hc _).1).trans (hd u hu))
      (convex_Icc 0 (endpoint : ℝ)) hs ht
  have hstep : ∀ j<D, |theta (j+1)-theta j| ≤ 1/8 := by
    intro j hj
    have hs := phaseGrid_mem endpoint hy D hD j (Nat.le_of_lt hj)
    have ht := phaseGrid_mem endpoint hy D hD (j+1) (by omega)
    have h := hlip _ hs _ ht
    have heq : (endpoint : ℝ)*(((j+1 : ℕ) : ℝ)/(D : ℝ))-(endpoint : ℝ)*((j : ℝ)/(D : ℝ))=
        (endpoint : ℝ)/(D : ℝ) := by push_cast; ring
    rw [heq,abs_of_nonneg (div_nonneg hyR hDr.le)] at h
    have hbound : (8 : ℝ)*(endpoint : ℝ)*(bound : ℝ) ≤ D := by exact_mod_cast phaseLogSteps_bound endpoint bound
    have hlast : (bound : ℝ)*((endpoint : ℝ)/(D : ℝ)) ≤ 1/8 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hDr).mpr
      nlinarith
    exact h.trans hlast
  have hsamples : ∀ j ≤ D,
      ‖rationalCircleCast (phaseLogSamples oracle endpoint D b j)-complexPhase (theta j)‖ ≤ (2^b : ℝ)⁻¹ := by
    intro j hj
    by_cases hj0 : j=0
    · subst j
      simp [phaseLogSamples,theta,F,circleLogPrimitive_zero]
    · have htime : ((endpoint*((j : ℚ)/(D : ℚ)) : ℚ) : ℝ) ∈ Icc 0 (endpoint : ℝ) := by
        simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast] using phaseGrid_mem endpoint hy D hD j hj
      have ho := horacle (endpoint*((j : ℚ)/(D : ℚ))) htime b
      have hp := circleLogPrimitive_reconstruct hk hc ((endpoint : ℝ)*((j : ℝ)/(D : ℝ))) z
      rw [h0,mul_one] at hp
      have hpC := congrArg circleComplex hp
      rw [circleComplex_phase] at hpC
      push_cast at ho
      rw [← hpC] at ho
      simpa only [phaseLogSamples,if_neg hj0] using ho
  obtain ⟨r,hr,hv,he,hmeta⟩ := rationalPhaseLog_finite oracle endpoint bound tau ht theta
    (by simp [theta,F,circleLogPrimitive_zero]) hstep hsamples
  have hend : theta D=circleLogPrimitive k (transversePair ((endpoint : ℝ),z)) := by
    dsimp [theta,F]
    rw [div_self hDr.ne',mul_one]
  change |(r.value : ℝ)-theta D| ≤ (r.errorBound : ℝ) at hv
  rw [hend] at hv
  exact ⟨r,hr,hv,he,hmeta⟩

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
