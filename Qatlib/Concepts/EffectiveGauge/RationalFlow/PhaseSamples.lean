/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhaseAngles

/-!
# Noisy circle samples retain a small real angular error

The true phases below are semantic values, not inputs queried by the program.
They may pass through arbitrarily many turns. Only local increments are
restricted, and samples need not lie exactly on the unit circle.
-/

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of sample Angle Error in the Rational Flow construction. -/
def sampleAngleError (z : ℂ) (theta : ℝ) : ℝ :=
  Real.arctan ((z*conj (complexPhase theta)).im/(z*conj (complexPhase theta)).re)

/-- Original `sampleAngleError_spec` guarantee for the `PhaseSamples` construction; the complete source hypotheses are retained. -/
theorem sampleAngleError_spec (z : ℂ) (theta e : ℝ) (he : 0 ≤ e) (he64 : e ≤ 1/64)
    (hz : ‖z-complexPhase theta‖ ≤ e) :
    0<‖z‖ ∧ |sampleAngleError z theta| ≤ 2*e ∧
      z=(‖z‖ : ℂ)*complexPhase (theta+sampleAngleError z theta) := by
  let u := z*conj (complexPhase theta)
  have hunit : complexPhase theta*conj (complexPhase theta)=1 := by
    rw [complexPhase_conj,← complexPhase_add,add_neg_cancel,complexPhase_zero]
  have hunit' : conj (complexPhase theta)*complexPhase theta=1 := by rw [mul_comm,hunit]
  have hid : u-1=(z-complexPhase theta)*conj (complexPhase theta) := by
    rw [sub_mul,hunit]
  have hn : ‖u-1‖ ≤ e := by
    rw [hid,norm_mul,Complex.norm_conj,complexPhase_norm,mul_one]
    exact hz
  have hu := near_one_real_angle u e he (by linarith) hn
  have hzn : z ≠ 0 := by
    intro hzero
    have h : (0 : ℝ)<0 := by simpa only [u,hzero,zero_mul,Complex.zero_re] using hu.1
    exact (lt_irrefl 0) h
  have hnorm : ‖u‖=‖z‖ := by simp only [u,norm_mul,Complex.norm_conj,complexPhase_norm,mul_one]
  refine ⟨norm_pos_iff.mpr hzn,hu.2.1,?_⟩
  calc
    z = u*complexPhase theta := by dsimp [u]; rw [mul_assoc,hunit',mul_one]
    _ = ((‖z‖ : ℂ)*complexPhase (sampleAngleError z theta))*complexPhase theta := by
      rw [hu.2.2,hnorm]
      rfl
    _ = _ := by rw [complexPhase_add]; ring

/-- Original `sampleAngleError_one` guarantee for the `PhaseSamples` construction; the complete source hypotheses are retained. -/
@[simp] theorem sampleAngleError_one : sampleAngleError 1 0=0 := by simp [sampleAngleError]

/-- Both actual branch guards succeed, and the exact local arctangent equals
the lifted phase difference plus the difference of sample error angles. -/
theorem sampled_phase_increment (previous current : ℂ) (theta0 theta1 e : ℝ)
    (he : 0 ≤ e) (he64 : e ≤ 1/64) (hstep : |theta1-theta0| ≤ 1/8)
    (hp : ‖previous-complexPhase theta0‖ ≤ e) (hc : ‖current-complexPhase theta1‖ ≤ e) :
    0<(current*conj previous).re ∧ |(current*conj previous).im/(current*conj previous).re| ≤ 1/2 ∧
      Real.arctan ((current*conj previous).im/(current*conj previous).re)=
        (theta1-theta0)+sampleAngleError current theta1-sampleAngleError previous theta0 := by
  obtain ⟨hpn,hpa,hprep⟩ := sampleAngleError_spec previous theta0 e he he64 hp
  obtain ⟨hcn,hca,hcrep⟩ := sampleAngleError_spec current theta1 e he he64 hc
  let angle := (theta1-theta0)+sampleAngleError current theta1-sampleAngleError previous theta0
  have hang : |angle| ≤ 3/16 := by
    have h := (abs_sub ((theta1-theta0)+sampleAngleError current theta1)
      (sampleAngleError previous theta0)).trans (add_le_add (abs_add_le _ _) (le_refl _))
    change |angle| ≤ |theta1-theta0|+|sampleAngleError current theta1|+|sampleAngleError previous theta0| at h
    linarith
  have hid : current*conj previous=((‖current‖*‖previous‖ : ℝ) : ℂ)*complexPhase angle := by
    calc
      _ = ((‖current‖ : ℂ)*complexPhase (theta1+sampleAngleError current theta1))*
          conj ((‖previous‖ : ℂ)*complexPhase (theta0+sampleAngleError previous theta0)) :=
        congrArg₂ (fun a b : ℂ => a*conj b) hcrep hprep
      _ = ((‖current‖*‖previous‖ : ℝ) : ℂ)*complexPhase
          ((theta1+sampleAngleError current theta1)-(theta0+sampleAngleError previous theta0)) := by
        have hphase : complexPhase ((theta1+sampleAngleError current theta1)-(theta0+sampleAngleError previous theta0))=
            complexPhase (theta1+sampleAngleError current theta1)*complexPhase (-(theta0+sampleAngleError previous theta0)) := by
          rw [sub_eq_add_neg]
          exact complexPhase_add _ _
        rw [map_mul,Complex.conj_ofReal,complexPhase_conj,Complex.ofReal_mul,hphase]
        ring
      _ = _ := by congr 2; dsimp [angle]; ring
  rw [hid]
  exact small_scaled_phase_increment (‖current‖*‖previous‖) angle (mul_pos hcn hpn) hang

end Qatlib.Concepts.EffectiveGauge.RationalFlow
