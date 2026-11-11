/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CisApproximation

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Period Execution

Torus Fourier constructions for Effective Gauge.
Defines `fourierPeriodExecution`.
Proves `fourierPeriodExecution_error`, `fourierPeriodExecution_gt_five`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Same finite Machin execution used to prepare the mode angle. -/
def fourierPeriodExecution (ell : ℚ) : ℚ := 2*(rationalPi (ell/2)).value

noncomputable section

/-- Original `fourierPeriodExecution_error` guarantee for the `FourierPeriodExecution` construction; the complete source hypotheses are retained. -/
theorem fourierPeriodExecution_error (ell : ℚ) (he : 0<ell) :
    |(fourierPeriodExecution ell : ℝ)-physicalPeriod| ≤ (ell : ℝ) := by
  have hp := rationalPi_error (ell/2) (by positivity)
  have hbudget : ((rationalPi (ell/2)).error : ℝ) ≤ (ell : ℝ)/2 := by
    exact_mod_cast hp.2.2.1
  have hid : (fourierPeriodExecution ell : ℝ)-physicalPeriod=
      2*(((rationalPi (ell/2)).value : ℝ)-Real.pi) := by
    simp only [fourierPeriodExecution,Rat.cast_mul,Rat.cast_ofNat,physicalPeriod]
    ring
  rw [hid,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact (mul_le_mul_of_nonneg_left (hp.1.trans hbudget) (by norm_num)).trans_eq (by ring)

/-- Original `fourierPeriodExecution_gt_five` guarantee for the `FourierPeriodExecution` construction; the complete source hypotheses are retained. -/
theorem fourierPeriodExecution_gt_five (ell : ℚ) (he : 0<ell) (he1 : ell ≤ 1) :
    (5 : ℝ)<fourierPeriodExecution ell := by
  have hbounds := abs_le.mp (fourierPeriodExecution_error ell he)
  have hell : (ell : ℝ) ≤ 1 := by exact_mod_cast he1
  dsimp only [physicalPeriod] at hbounds
  linarith [Real.pi_gt_three]

end
end Qatlib.Concepts.EffectiveGauge.TorusFourier
