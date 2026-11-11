/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CircleLog

/-!
# Reconstruction from the real angular primitive

The base value k(0,z) is retained. The argument is valid at negative,
zero and positive y, without a principal-argument branch choice.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `circleLogPrimitive_zero` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem circleLogPrimitive_zero (k : TransversePoint → ℍ) (z : ℝ) :
    circleLogPrimitive k (transversePair (0,z))=0 := by
  change (∫ y in (0 : ℝ)..0, circleAngularRate k (transversePair (y,z)))=0
  simp

/-- Original `circleLogPrimitive_reconstruct` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem circleLogPrimitive_reconstruct {k : TransversePoint → ℍ} (hk : ContDiff ℝ ∞ k)
    (hc : ∀ p, IsCircleQuaternion (k p)) (y z : ℝ) :
    phase (circleLogPrimitive k (transversePair (y,z)))*k (transversePair (0,z)) =
      k (transversePair (y,z)) := by
  let a : ℝ := y/physicalPeriod
  let b := k (transversePair (0,z))
  let theta := fun u : ℝ => circleLogPrimitive k (transversePair (a*u,z))
  let c := fun u : ℝ => a*circleAngularRate k (transversePair (a*u,z))
  let coeff := fun u : ℝ => c u • iAxis
  let q := fun u : ℝ => phase (theta u)*b
  let r := fun u : ℝ => k (transversePair (a*u,z))
  have hb : ‖b‖=1 := (hc _).1
  have hbj : b.imJ=0 := (hc _).2.1
  have hbk : b.imK=0 := (hc _).2.2
  have hcomm : iAxis*b=b*iAxis := by ext <;> simp [iAxis,hbj,hbk]
  have hpos : Continuous (fun u : ℝ => transversePair (a*u,z)) :=
    transversePair.continuous.comp ((continuous_const.mul continuous_id).prodMk continuous_const)
  have hcoeff : ContinuousOn coeff (Icc 0 physicalPeriod) :=
    ((continuous_const.mul ((contDiff_circleAngularRate hk).continuous.comp hpos)).smul
      continuous_const).continuousOn
  have hq : ∀ u ∈ Icc 0 physicalPeriod, HasDerivWithinAt q (q u*coeff u) (Icc 0 physicalPeriod) u := by
    intro u _
    have ha : HasDerivAt (fun x : ℝ => a*x) a u := by simpa using (hasDerivAt_id u).const_mul a
    have ht : HasDerivAt theta (c u) u := by
      simpa only [theta,c,Function.comp_def,smul_eq_mul] using
        (circleLogPrimitive_hasDerivAt hk z (a*u)).scomp u ha
    have hd := gauge_hasDerivAt (hasDerivAt_const u b) ht
    apply HasDerivAt.hasDerivWithinAt
    simpa only [q,coeff,zero_add,mul_smul_comm,hcomm,mul_assoc] using hd
  have hr : ∀ u ∈ Icc 0 physicalPeriod, HasDerivWithinAt r (r u*coeff u) (Icc 0 physicalPeriod) u := by
    intro u _
    have ha : HasDerivAt (fun x : ℝ => a*x) a u := by simpa using (hasDerivAt_id u).const_mul a
    have hd := (circle_curve_hasDerivAt hk hc z (a*u)).scomp u ha
    apply HasDerivAt.hasDerivWithinAt
    simpa only [r,coeff,c,Function.comp_def,mul_smul_comm,smul_smul] using hd
  have hqn : ∀ u ∈ Icc 0 physicalPeriod, ‖q u‖=1 := by
    intro u _
    simp only [q,norm_mul,phase_norm,hb,one_mul]
  have hrn : ∀ u ∈ Icc 0 physicalPeriod, ‖r u‖=1 := fun u _ => (hc _).1
  have ht0 : theta 0=0 := by simp only [theta,mul_zero,circleLogPrimitive_zero]
  have hinit : r 0=q 0 := by
    simp only [r,q,mul_zero,ht0,phase,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero,one_mul]
    rfl
  have h := unit_transport_stability physicalPeriod_pos.le hcoeff hcoeff hq hr
    (fun u _ => by simp [coeff,iAxis]) hqn hrn hinit (E := 0) (by intro u _; simp)
  have heq : r physicalPeriod=q physicalPeriod :=
    sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using h) (norm_nonneg _)))
  have ha : a*physicalPeriod=y := div_mul_cancel₀ _ physicalPeriod_pos.ne'
  simpa only [r,q,theta,ha,b] using heq.symm

/-- Original `circleLogPrimitive_eq_zero_of_one` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem circleLogPrimitive_eq_zero_of_one {k : TransversePoint → ℍ} (hk : ContDiff ℝ ∞ k)
    (z y : ℝ) (hy : 0 ≤ y) (hone : ∀ u ∈ Icc (0 : ℝ) y, k (transversePair (u,z))=1) :
    circleLogPrimitive k (transversePair (y,z))=0 := by
  rcases hy.eq_or_lt with hzero | hpos
  · rw [← hzero]
    exact circleLogPrimitive_zero k z
  have hd : ∀ u ∈ Icc (0 : ℝ) y,
      fderiv ℝ k (transversePair (u,z)) (EuclideanSpace.single 0 1)=0 := by
    intro u hu
    have ha := (hk.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt u (transversePair_hasDerivAt z u)
    have hb := (hasDerivAt_const u (1 : ℍ)).hasDerivWithinAt.congr_of_mem hone hu
    exact UniqueDiffWithinAt.eq_deriv (Icc (0 : ℝ) y) (uniqueDiffOn_Icc hpos u hu) ha.hasDerivWithinAt hb
  change (∫ u in (0 : ℝ)..y, circleAngularRate k (transversePair (u,z)))=0
  calc
    _ = ∫ u in (0 : ℝ)..y, (0 : ℝ) := by
      apply integral_congr
      intro u hu
      rw [uIcc_of_le hy] at hu
      simp only [circleAngularRate,hd u hu,mul_zero,Quaternion.imI_zero]
    _ = 0 := integral_zero

/-- A continuous real phase with constant exponential is constant on the
connected physical interval; the explicit zero base value fixes its integer. -/
theorem real_phase_one_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ z ∈ Icc (0 : ℝ) physicalPeriod, phase (f z)=1) (h0 : f 0=0) :
    ∀ z ∈ Icc (0 : ℝ) physicalPeriod, f z=0 := by
  have hd : ∀ z ∈ Icc (0 : ℝ) physicalPeriod, deriv f z=0 := by
    intro z hz
    have hfd := (hf.differentiable (by simp) z).hasDerivAt
    have hpd := (phase_hasDerivAt (f z)).scomp z hfd
    have hc := (hasDerivAt_const z (1 : ℍ)).hasDerivWithinAt.congr_of_mem hp hz
    have he := UniqueDiffWithinAt.eq_deriv (Icc (0 : ℝ) physicalPeriod)
      (uniqueDiffOn_Icc physicalPeriod_pos z hz) hpd.hasDerivWithinAt hc
    rw [hp z hz,mul_one] at he
    have hi := congrArg (fun q : ℍ => q.imI) he
    simpa [iAxis] using hi
  have hr : ∀ z ∈ Ico (0 : ℝ) physicalPeriod, HasDerivWithinAt f 0 (Ici z) z := by
    intro z hz
    simpa only [hd z ⟨hz.1,hz.2.le⟩] using (hf.differentiable (by simp) z).hasDerivAt.hasDerivWithinAt
  exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hf.continuous.continuousOn hr h0 (K := 0) (by intro z hz; simp)

/-- Definition of terminal Real Phase in the Hopf Atlas construction. -/
def terminalRealPhase (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) : TransversePoint → ℝ :=
  circleLogPrimitive (terminalRatio v hv q₀ h₀)

/-- Original `contDiff_terminalRealPhase` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem contDiff_terminalRealPhase (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) : ContDiff ℝ ∞ (terminalRealPhase v hv q₀ h₀) :=
  contDiff_circleLogPrimitive (contDiff_terminalRatio v hv q₀ h₀)

/-- Original `terminalRealPhase_reconstruct` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem terminalRealPhase_reconstruct (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc)
    (y z : ℝ) (hz : 0 ≤ z ∧ z ≤ physicalPeriod) :
    phase (terminalRealPhase v hv q₀ h₀ (transversePair (y,z)))=
      terminalRatio v hv q₀ h₀ (transversePair (y,z)) := by
  have hb : terminalRatio v hv q₀ h₀ (transversePair (0,z))=1 := by
    apply terminalRatio_boundary v hv hu q₀ h₀ eta sc hc
    · intro j
      fin_cases j
      · exact ⟨le_rfl,physicalPeriod_pos.le⟩
      · exact hz
    · exact ⟨0,Or.inl he.le⟩
  have h := circleLogPrimitive_reconstruct (contDiff_terminalRatio v hv q₀ h₀)
    (terminalRatio_circle v hv hu q₀ h₀ hp eta he sc hc hi) y z
  simpa only [terminalRealPhase,hb,mul_one] using h

/-- Original `terminalRealPhase_z_collar_zero` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem terminalRealPhase_z_collar_zero (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (y z : ℝ)
    (hy : 0 ≤ y ∧ y ≤ physicalPeriod) (hz : 0 ≤ z ∧ z ≤ physicalPeriod)
    (hb : z ≤ eta ∨ physicalPeriod-eta ≤ z) :
    terminalRealPhase v hv q₀ h₀ (transversePair (y,z))=0 := by
  apply circleLogPrimitive_eq_zero_of_one (contDiff_terminalRatio v hv q₀ h₀) z y hy.1
  intro u hu'
  apply terminalRatio_boundary v hv hu q₀ h₀ eta sc hc
  · intro j
    fin_cases j
    · exact ⟨hu'.1,hu'.2.trans hy.2⟩
    · exact hz
  · exact ⟨1,hb⟩

/-- Original `terminalRealPhase_upper_zero` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem terminalRealPhase_upper_zero (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc)
    (z : ℝ) (hz : 0 ≤ z ∧ z ≤ physicalPeriod) :
    terminalRealPhase v hv q₀ h₀ (transversePair (physicalPeriod,z))=0 := by
  let f := fun u : ℝ => terminalRealPhase v hv q₀ h₀ (transversePair (physicalPeriod,u))
  have hf : ContDiff ℝ ∞ f := (contDiff_terminalRealPhase v hv q₀ h₀).comp
    (transversePair.contDiff.comp (contDiff_const.prodMk contDiff_id))
  have hphase : ∀ u ∈ Icc (0 : ℝ) physicalPeriod, phase (f u)=1 := by
    intro u hu'
    rw [show f u=terminalRealPhase v hv q₀ h₀ (transversePair (physicalPeriod,u)) from rfl,
      terminalRealPhase_reconstruct v hv hu q₀ h₀ hp eta he sc hc hi physicalPeriod u hu']
    apply terminalRatio_boundary v hv hu q₀ h₀ eta sc hc
    · intro j
      fin_cases j
      · exact ⟨physicalPeriod_pos.le,le_rfl⟩
      · exact hu'
    · exact ⟨0,Or.inr (by change physicalPeriod-eta ≤ physicalPeriod; linarith)⟩
  have hbase : f 0=0 := terminalRealPhase_z_collar_zero v hv hu q₀ h₀ eta sc hc physicalPeriod 0
    ⟨physicalPeriod_pos.le,le_rfl⟩ ⟨le_rfl,physicalPeriod_pos.le⟩ (Or.inl he.le)
  exact real_phase_one_zero hf hphase hbase z hz

/-- Original `terminalRealPhase_left_collar_zero` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem terminalRealPhase_left_collar_zero (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (y z : ℝ)
    (hy : 0 ≤ y ∧ y ≤ physicalPeriod) (hz : 0 ≤ z ∧ z ≤ physicalPeriod) (hb : y ≤ eta) :
    terminalRealPhase v hv q₀ h₀ (transversePair (y,z))=0 := by
  apply circleLogPrimitive_eq_zero_of_one (contDiff_terminalRatio v hv q₀ h₀) z y hy.1
  intro u hu'
  apply terminalRatio_boundary v hv hu q₀ h₀ eta sc hc
  · intro j
    fin_cases j
    · exact ⟨hu'.1,hu'.2.trans hy.2⟩
    · exact hz
  · exact ⟨0,Or.inl (hu'.2.trans hb)⟩

/-- Original `terminalRealPhase_right_collar_zero` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem terminalRealPhase_right_collar_zero (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc)
    (y z : ℝ) (hy : 0 ≤ y ∧ y ≤ physicalPeriod) (hz : 0 ≤ z ∧ z ≤ physicalPeriod)
    (hb : physicalPeriod-eta ≤ y) : terminalRealPhase v hv q₀ h₀ (transversePair (y,z))=0 := by
  let c : ℝ := (physicalPeriod-y)/physicalPeriod
  let f := fun u : ℝ => terminalRealPhase v hv q₀ h₀ (transversePair (physicalPeriod-c*u,z))
  have hc0 : 0 ≤ c := div_nonneg (sub_nonneg.mpr hy.2) physicalPeriod_pos.le
  have hcL : c*physicalPeriod=physicalPeriod-y := div_mul_cancel₀ _ physicalPeriod_pos.ne'
  have hf : ContDiff ℝ ∞ f := (contDiff_terminalRealPhase v hv q₀ h₀).comp
    (transversePair.contDiff.comp
      ((contDiff_const.sub (contDiff_const.mul contDiff_id)).prodMk contDiff_const))
  have hphase : ∀ u ∈ Icc (0 : ℝ) physicalPeriod, phase (f u)=1 := by
    intro u hu'
    have hprod : c*u ≤ physicalPeriod-y :=
      (mul_le_mul_of_nonneg_left hu'.2 hc0).trans_eq hcL
    have hprod0 := mul_nonneg hc0 hu'.1
    have hr : 0 ≤ physicalPeriod-c*u ∧ physicalPeriod-c*u ≤ physicalPeriod := by
      constructor <;> linarith
    rw [show f u=terminalRealPhase v hv q₀ h₀ (transversePair (physicalPeriod-c*u,z)) from rfl,
      terminalRealPhase_reconstruct v hv hu q₀ h₀ hp eta he sc hc hi _ z hz]
    apply terminalRatio_boundary v hv hu q₀ h₀ eta sc hc
    · intro j
      fin_cases j
      · exact hr
      · exact hz
    · exact ⟨0,Or.inr (by change physicalPeriod-eta ≤ physicalPeriod-c*u; linarith)⟩
  have hbase : f 0=0 := by
    simpa only [f,mul_zero,sub_zero] using terminalRealPhase_upper_zero v hv hu q₀ h₀ hp eta he sc hc hi z hz
  have h := real_phase_one_zero hf hphase hbase physicalPeriod ⟨physicalPeriod_pos.le,le_rfl⟩
  simpa only [f,hcL,sub_sub_cancel] using h

/-- Original `transversePair_eta` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
@[simp] theorem transversePair_eta (p : TransversePoint) : transversePair (p 0,p 1)=p := by
  ext j; fin_cases j <;> rfl

/-- Original `terminalRealPhase_boundary_zero` guarantee for the `CircleLogReconstruction` construction; the complete source hypotheses are retained. -/
theorem terminalRealPhase_boundary_zero (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) (p : TransversePoint)
    (hsq : ∀ j, 0 ≤ p j ∧ p j ≤ physicalPeriod)
    (hb : ∃ j, p j ≤ eta ∨ physicalPeriod-eta ≤ p j) : terminalRealPhase v hv q₀ h₀ p=0 := by
  have heq : p=transversePair (p 0,p 1) := (transversePair_eta p).symm
  rw [heq]
  rcases hb with ⟨j,hj⟩
  fin_cases j
  · rcases hj with hj | hj
    · exact terminalRealPhase_left_collar_zero v hv hu q₀ h₀ eta sc hc _ _ (hsq 0) (hsq 1) hj
    · exact terminalRealPhase_right_collar_zero v hv hu q₀ h₀ hp eta he sc hc hi _ _ (hsq 0) (hsq 1) hj
  · exact terminalRealPhase_z_collar_zero v hv hu q₀ h₀ eta sc hc _ _ (hsq 0) (hsq 1) hj

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
