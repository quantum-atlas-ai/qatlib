/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.ExponentialWord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral identities in the interaction frame

The exponential path, word generator, interaction word, and interaction generator are continuous
in real time. `interaction_integral` integrates the interaction differential equation over an
arbitrary interval.

At initial time zero, `interaction_integral_zero` expresses the interaction-word deviation from
one as an interval integral. These identities support the product-formula error analysis
discussed in [HejaziZiniArrazola2024].

## Main statements

* `interaction_integral`: Integrated interaction equation between two times.
* `interaction_integral_zero`: Integral formula with initial value one.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The exponential of a real scalar multiple of a fixed algebra element is continuous in time. -/
theorem exp_time_continuous (K : A) : Continuous (fun t : ℝ => NormedSpace.exp (t • K)) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exp_smul_const' K t).continuousAt)

/-- The generator of an exponential word is continuous in time. -/
theorem generator_continuous (ks : List A) : Continuous (generator ks) := by
  induction ks with
  | nil => exact continuous_const
  | cons K ks ih =>
    change Continuous
        (fun t : ℝ => K+NormedSpace.exp (t • K)*generator ks t*NormedSpace.exp ((-t) • K))
    exact continuous_const.add (((exp_time_continuous K).mul ih).mul
      ((exp_time_continuous K).comp continuous_neg))

/-- The interaction-frame word is continuous in time. -/
theorem interaction_continuous (K : A) (ks : List A) : Continuous (interaction K ks) :=
  continuous_iff_continuousAt.mpr (fun t => (interaction_hasDerivAt K ks t).continuousAt)

/-- The interaction-frame generator is continuous in time. -/
theorem interactionGenerator_continuous (K : A) (ks : List A) : Continuous (interactionGenerator K ks) := by
  exact (((exp_time_continuous K).comp continuous_neg).mul
    ((generator_continuous ks).sub continuous_const)).mul (exp_time_continuous K)

/-- Integrating the interaction generator times the interaction word from `a` to `b` gives the
difference of the endpoint interaction words. -/
theorem interaction_integral (K : A) (ks : List A) (a b : ℝ) :
    (∫ t in a..b, interactionGenerator K ks t * interaction K ks t) =
      interaction K ks b-interaction K ks a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => interaction_hasDerivAt K ks t)
    (((interactionGenerator_continuous K ks).mul (interaction_continuous K ks)).intervalIntegrable a b)

/-- Integrating the interaction generator times the interaction word from zero to `t` gives the
interaction word at `t` minus one. -/
theorem interaction_integral_zero (K : A) (ks : List A) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, interactionGenerator K ks s * interaction K ks s) = interaction K ks t-1 := by
  rw [interaction_integral, interaction_zero]
end Qatlib.Foundations.MatrixAlgebra.CommutatorExp
