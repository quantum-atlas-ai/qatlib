/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.DiskObstruction
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.HopfFibre
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Transport

/-!
# Hopf Section Obstruction

Hopf Atlas constructions for Effective Gauge.
Defines `quaternionComplexPart`, `diskJAxis`, `diskQuaternion`.
Proves `quaternionComplexPart_continuous`, `quaternionComplexPart_norm`, `diskQuaternion_continuous`.
-/


set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of quaternion Complex Part in the Hopf Atlas construction. -/
def quaternionComplexPart (q : ℍ) : ℂ := (q.re : ℂ)+(q.imI : ℂ)*Complex.I

/-- Original `quaternionComplexPart_continuous` guarantee for the `HopfSectionObstruction` construction; the complete source hypotheses are retained. -/
theorem quaternionComplexPart_continuous : Continuous quaternionComplexPart :=
  (Complex.continuous_ofReal.comp Quaternion.continuous_re).add
    ((Complex.continuous_ofReal.comp Quaternion.continuous_imI).mul continuous_const)

/-- Original `quaternionComplexPart_norm` guarantee for the `HopfSectionObstruction` construction; the complete source hypotheses are retained. -/
theorem quaternionComplexPart_norm (q : ℍ) (hq : ‖q‖=1) (hj : q.imJ=0) (hk : q.imK=0) :
    ‖quaternionComplexPart q‖=1 := by
  have h := (normSq_eq_one_iff q).mpr hq
  simp [Quaternion.normSq_def',hj,hk] at h
  have hc : Complex.normSq (quaternionComplexPart q)=1 := by
    simpa [quaternionComplexPart,Complex.normSq_apply,pow_two] using h
  rw [Complex.normSq_eq_norm_sq] at hc
  nlinarith [norm_nonneg (quaternionComplexPart q)]

/-- Definition of disk JAxis in the Hopf Atlas construction. -/
def diskJAxis : Quaternion ℝ := ⟨0,0,1,0⟩

/-- Definition of disk Quaternion in the Hopf Atlas construction. -/
def diskQuaternion (z : ComplexUnitDisk) : Quaternion ℝ :=
  (z.val.re) • (1 : ℍ)+(z.val.im) • iAxis+
    Real.sqrt (1-Complex.normSq z.val) • diskJAxis

/-- Original `diskQuaternion_continuous` guarantee for the `HopfSectionObstruction` construction; the complete source hypotheses are retained. -/
theorem diskQuaternion_continuous : Continuous diskQuaternion :=
  (((Complex.continuous_re.comp continuous_subtype_val).smul continuous_const).add
    ((Complex.continuous_im.comp continuous_subtype_val).smul continuous_const)).add
      ((Real.continuous_sqrt.comp
        (continuous_const.sub (Complex.continuous_normSq.comp continuous_subtype_val))).smul continuous_const)

/-- Original `diskQuaternion_norm` guarantee for the `HopfSectionObstruction` construction; the complete source hypotheses are retained. -/
theorem diskQuaternion_norm (z : ComplexUnitDisk) : ‖diskQuaternion z‖=1 := by
  have hz : ‖(z : ℂ)‖ ≤ 1 := by
    have hz := z.property
    change dist (z : ℂ) 0 ≤ 1 at hz
    simpa only [dist_zero_right] using hz
  have hN : 0 ≤ 1-Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z : ℂ)]
  apply (normSq_eq_one_iff _).mp
  have hs := Real.sq_sqrt hN
  simp [diskQuaternion,diskJAxis,Quaternion.normSq_def',iAxis,Complex.normSq_apply] at hs ⊢
  nlinarith

/-- Original `diskQuaternion_boundary` guarantee for the `HopfSectionObstruction` construction; the complete source hypotheses are retained. -/
theorem diskQuaternion_boundary (t : ℝ) : diskQuaternion (unitDiskBoundary t)=phase t := by
  have hN : Complex.normSq (unitDiskBoundary t).val=1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [unitDiskBoundary]
  simp only [diskQuaternion,hN,sub_self,Real.sqrt_zero,zero_smul,add_zero]
  ext <;> simp [unitDiskBoundary,phase,iAxis,Circle.coe_exp,
    Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

/-- Abbreviation for Unit Hopf Spin in the Hopf Atlas construction. -/
abbrev UnitHopfSpin := {s : ℍ // s.re=0 ∧ ‖s‖=1}

/-- Definition of disk Hopf Spin in the Hopf Atlas construction. -/
def diskHopfSpin (z : ComplexUnitDisk) : UnitHopfSpin :=
  ⟨hopf (diskQuaternion z),hopf_re _,by rw [hopf_norm,diskQuaternion_norm]; norm_num⟩

/-- Definition of base Hopf Spin in the Hopf Atlas construction. -/
def baseHopfSpin : UnitHopfSpin := ⟨iAxis,by simp [iAxis],norm_iAxis⟩

/-- Original `diskHopfSpin_continuous` guarantee for the `HopfSectionObstruction` construction; the complete source hypotheses are retained. -/
theorem diskHopfSpin_continuous : Continuous diskHopfSpin :=
  (continuous_hopf.comp diskQuaternion_continuous).subtype_mk _

/-- Original `diskHopfSpin_boundary` guarantee for the `HopfSectionObstruction` construction; the complete source hypotheses are retained. -/
theorem diskHopfSpin_boundary (t : ℝ) : diskHopfSpin (unitDiskBoundary t)=baseHopfSpin := by
  apply Subtype.ext
  change hopf (diskQuaternion (unitDiskBoundary t))=iAxis
  rw [diskQuaternion_boundary]
  exact phase_axis t

/-- A continuous choice of unit Hopf lift on the entire spin sphere cannot
exist. The valid piecewise choice with positive margins is unaffected. -/
theorem no_continuous_global_hopf_section (sigma : UnitHopfSpin → ℍ) (hs : Continuous sigma)
    (hn : ∀ s, ‖sigma s‖=1) (hh : ∀ s, hopf (sigma s)=s.val) : False := by
  let r : ComplexUnitDisk → ℍ := fun z =>
    diskQuaternion z*star (sigma (diskHopfSpin z))*sigma baseHopfSpin
  have hr : Continuous r :=
    (diskQuaternion_continuous.mul (hs.comp diskHopfSpin_continuous).star).mul continuous_const
  have hq0 : (sigma baseHopfSpin).imJ=0 ∧ (sigma baseHopfSpin).imK=0 := by
    have h := sameHopf_ratio_components 1 (sigma baseHopfSpin) (by simp) (hn _)
      (by simpa [hopf,baseHopfSpin] using hh baseHopfSpin)
    simpa using h
  have hrc (z : ComplexUnitDisk) : (r z).imJ=0 ∧ (r z).imK=0 := by
    have h := sameHopf_ratio_components (sigma (diskHopfSpin z)) (diskQuaternion z)
      (hn _) (diskQuaternion_norm z) (hh (diskHopfSpin z)).symm
    dsimp only [r]
    constructor
    · rw [Quaternion.imJ_mul, h.1, h.2, hq0.1, hq0.2]
      ring
    · rw [Quaternion.imK_mul, h.1, h.2, hq0.1, hq0.2]
      ring
  have hrn (z : ComplexUnitDisk) : ‖r z‖=1 := by
    simp [r,norm_mul,norm_star,diskQuaternion_norm,hn]
  let R : ComplexUnitDisk → Circle := fun z =>
    ⟨quaternionComplexPart (r z),by
      apply mem_sphere_zero_iff_norm.mpr
      exact quaternionComplexPart_norm _ (hrn z) (hrc z).1 (hrc z).2⟩
  apply no_circle_disk_extension R
    ((quaternionComplexPart_continuous.comp hr).subtype_mk _)
  intro t
  apply Subtype.ext
  have hb : r (unitDiskBoundary t)=phase t := by
    dsimp only [r]
    rw [diskQuaternion_boundary,diskHopfSpin_boundary,mul_assoc,unit_star_mul_self _ (hn _),mul_one]
  change quaternionComplexPart (r (unitDiskBoundary t))=(Circle.exp t : ℂ)
  rw [hb]
  simp [quaternionComplexPart,phase,iAxis,Circle.coe_exp,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
