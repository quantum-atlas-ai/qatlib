/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.FibreDifferential
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhaseLoopObstruction
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerGauge

set_option backward.isDefEq.respectTransparency false

/-!
# Linear Gauge Classification

Hopf Atlas constructions for Effective Gauge.
Defines `realGaugeLinear`.
Proves `hasDerivAt_coordinateLine`, `spatialPartial_gauge_actual`, `realGaugeLinear_apply`.
-/


set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `hasDerivAt_coordinateLine` guarantee for the `LinearGaugeClassification` construction; the complete source hypotheses are retained. -/
theorem hasDerivAt_coordinateLine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (x : SpatialPoint) (hf : DifferentiableAt ℝ f x) (j : Fin 3) :
    HasDerivAt (fun t : ℝ => f (x+t • EuclideanSpace.single j 1))
      (fderiv ℝ f x (EuclideanSpace.single j 1)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x+t • EuclideanSpace.single j 1)
      (EuclideanSpace.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ))).const_add x
  have hd : HasFDerivAt f (fderiv ℝ f x) (x+(0 : ℝ) • EuclideanSpace.single j 1) := by
    simpa using hf.hasFDerivAt
  simpa only [Function.comp_def] using hd.comp_hasDerivAt 0 hl

/-- Original `spatialPartial_gauge_actual` guarantee for the `LinearGaugeClassification` construction; the complete source hypotheses are retained. -/
theorem spatialPartial_gauge_actual (q : QuaternionField) (theta : SpatialPoint → ℝ)
    (x : SpatialPoint) (hq : DifferentiableAt ℝ q x) (ht : DifferentiableAt ℝ theta x) (j : Fin 3) :
    spatialPartial (fun y => phase (theta y)*q y) x j=
      phase (theta x)*(spatialPartial q x j+
        (fderiv ℝ theta x (EuclideanSpace.single j 1)) • (iAxis*q x)) := by
  have hg : DifferentiableAt ℝ (fun y => phase (theta y)*q y) x :=
    ((phase_hasDerivAt (theta x)).differentiableAt.comp x ht).mul hq
  have h1 := gauge_hasDerivAt (hasDerivAt_coordinateLine q x hq j)
    (hasDerivAt_coordinateLine theta x ht j)
  have h2 := hasDerivAt_coordinateLine (fun y => phase (theta y)*q y) x hg j
  simpa only [zero_smul,add_zero,spatialPartial] using h2.unique h1

/-- Definition of real Gauge Linear in the Hopf Atlas construction. -/
def realGaugeLinear (b : Fin 3 → ℝ) : SpatialPoint →L[ℝ] ℝ :=
  innerSL ℝ (WithLp.toLp 2 b)

/-- Original `realGaugeLinear_apply` guarantee for the `LinearGaugeClassification` construction; the complete source hypotheses are retained. -/
theorem realGaugeLinear_apply (b : Fin 3 → ℝ) (x : SpatialPoint) :
    realGaugeLinear b x=∑ j : Fin 3, b j*x j := by
  change inner ℝ (WithLp.toLp 2 b : SpatialPoint) x=_
  simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]

/-- Original `realGaugeLinear_basis` guarantee for the `LinearGaugeClassification` construction; the complete source hypotheses are retained. -/
theorem realGaugeLinear_basis (b : Fin 3 → ℝ) (j : Fin 3) :
    realGaugeLinear b (EuclideanSpace.single j 1)=b j := by
  change inner ℝ (WithLp.toLp 2 b : SpatialPoint) (EuclideanSpace.single j 1)=_
  simpa using EuclideanSpace.inner_single_right j (1 : ℝ) (WithLp.toLp 2 b : SpatialPoint)

/-- Original `realGaugeLinear_latticeBasis` guarantee for the `LinearGaugeClassification` construction; the complete source hypotheses are retained. -/
theorem realGaugeLinear_latticeBasis (b : Fin 3 → ℝ) (j : Fin 3) :
    realGaugeLinear b (latticeShift (Pi.single j 1))=physicalPeriod*b j := by
  rw [realGaugeLinear_apply]
  simp [latticeShift,Pi.single_apply,mul_comm]

/-- A constant connection difference determines its fibre field by an
explicit real linear phase. No pre-existing logarithm is assumed. -/
theorem constantFibreDerivative_classification (z : QuaternionField) (hz : ContDiff ℝ ∞ z)
    (b : Fin 3 → ℝ) (hd : ∀ x j, spatialPartial z x j=b j • (iAxis*z x)) (x : SpatialPoint) :
    z x=phase (realGaugeLinear b x)*z 0 := by
  let theta : SpatialPoint → ℝ := fun y => -realGaugeLinear b y
  have ht : ContDiff ℝ ∞ theta := (realGaugeLinear b).contDiff.neg
  let w : QuaternionField := fun y => phase (theta y)*z y
  have hw : ContDiff ℝ ∞ w := (contDiff_phase.comp ht).mul hz
  have haxes (x : SpatialPoint) (j : Fin 3) : fderiv ℝ w x (EuclideanSpace.single j 1)=0 := by
    have h := spatialPartial_gauge_actual z theta x (hz.differentiable (by simp) x)
      (ht.differentiable (by simp) x) j
    have htheta : fderiv ℝ theta x (EuclideanSpace.single j 1)= -b j := by
      change (fderiv ℝ (-(realGaugeLinear b : SpatialPoint → ℝ)) x) (EuclideanSpace.single j 1) = -b j
      have h := congrArg (fun f : SpatialPoint →L[ℝ] ℝ => f (EuclideanSpace.single j 1))
        ((realGaugeLinear b).hasFDerivAt.neg.fderiv (x := x))
      simpa only [ContinuousLinearMap.neg_apply,realGaugeLinear_basis] using h
    rw [hd,htheta,← add_smul,add_neg_cancel,zero_smul,mul_zero] at h
    exact h
  have hzero (x : SpatialPoint) : fderiv ℝ w x=0 := by
    apply ContinuousLinearMap.ext
    intro v
    change fderiv ℝ w x v=0
    have hv : v=v 0 • EuclideanSpace.single 0 (1 : ℝ)+v 1 • EuclideanSpace.single 1 (1 : ℝ)+
        v 2 • EuclideanSpace.single 2 (1 : ℝ) := by
      ext j
      fin_cases j <;> simp
    rw [hv]
    simp only [map_add,map_smul,haxes,smul_zero,add_zero]
  have hc : w x=w 0 := is_const_of_fderiv_eq_zero (hw.differentiable (by simp)) hzero x 0
  have hw0 : w 0=z 0 := by simp [w,theta,phase]
  rw [hw0] at hc
  have hinv : phase (realGaugeLinear b x)*phase (-realGaugeLinear b x)=1 := by
    rw [← phase_add,add_neg_cancel]
    simp [phase]
  calc
    z x = (phase (realGaugeLinear b x)*phase (-realGaugeLinear b x))*z x := by rw [hinv,one_mul]
    _ = phase (realGaugeLinear b x)*(phase (-realGaugeLinear b x)*z x) := mul_assoc _ _ _
    _ = _ := congrArg (fun q => phase (realGaugeLinear b x)*q) hc

/-- Original `periodic_constantFibreDerivative_integer` guarantee for the `LinearGaugeClassification` construction; the complete source hypotheses are retained. -/
theorem periodic_constantFibreDerivative_integer (z : QuaternionField) (hz : ContDiff ℝ ∞ z)
    (hu : ∀ x, ‖z x‖=1) (hp : IsPeriodicField z) (b : Fin 3 → ℝ)
    (hd : ∀ x j, spatialPartial z x j=b j • (iAxis*z x)) :
    ∃ n : SpatialFrequency, ∀ j, b j=(n j : ℝ) := by
  have heach (j : Fin 3) : ∃ n : ℤ, b j=(n : ℝ) := by
    have h := constantFibreDerivative_classification z hz b hd (latticeShift (Pi.single j 1))
    have hperiod : z (latticeShift (Pi.single j 1))=z 0 := by simpa only [zero_add] using hp 0 (Pi.single j 1)
    rw [hperiod,realGaugeLinear_latticeBasis] at h
    have hz0 : z 0≠0 := by intro hzero; simpa [hzero] using hu 0
    have hphase : phase (physicalPeriod*b j)=phase 0 := by
      have he : phase (physicalPeriod*b j)*z 0=1*z 0 := by simpa only [one_mul] using h.symm
      simpa [phase] using mul_right_cancel₀ hz0 he
    obtain ⟨n,hn⟩ := phase_eq_implies_period_integer (physicalPeriod*b j) 0 hphase
    refine ⟨n,mul_left_cancel₀ physicalPeriod_pos.ne' ?_⟩
    simpa only [sub_zero,mul_comm] using hn
  choose n hn using heach
  exact ⟨n,hn⟩

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
