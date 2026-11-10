/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.ExponentialWord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exp_time_continuous (K : A) : Continuous (fun t : ℝ => NormedSpace.exp (t • K)) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exp_smul_const' K t).continuousAt)

theorem generator_continuous (ks : List A) : Continuous (generator ks) := by
  induction ks with
  | nil => exact continuous_const
  | cons K ks ih =>
    change Continuous
        (fun t : ℝ => K+NormedSpace.exp (t • K)*generator ks t*NormedSpace.exp ((-t) • K))
    exact continuous_const.add (((exp_time_continuous K).mul ih).mul
      ((exp_time_continuous K).comp continuous_neg))

theorem interaction_continuous (K : A) (ks : List A) : Continuous (interaction K ks) :=
  continuous_iff_continuousAt.mpr (fun t => (interaction_hasDerivAt K ks t).continuousAt)

theorem interactionGenerator_continuous (K : A) (ks : List A) : Continuous (interactionGenerator K ks) := by
  exact (((exp_time_continuous K).comp continuous_neg).mul
    ((generator_continuous ks).sub continuous_const)).mul (exp_time_continuous K)

theorem interaction_integral (K : A) (ks : List A) (a b : ℝ) :
    (∫ t in a..b, interactionGenerator K ks t * interaction K ks t) =
      interaction K ks b-interaction K ks a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => interaction_hasDerivAt K ks t)
    (((interactionGenerator_continuous K ks).mul (interaction_continuous K ks)).intervalIntegrable a b)

theorem interaction_integral_zero (K : A) (ks : List A) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, interactionGenerator K ks s * interaction K ks s) = interaction K ks t-1 := by
  rw [interaction_integral, interaction_zero]
end Qatlib.Foundations.MatrixAlgebra.CommutatorExp
