/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgram

/-!
# Corrected kernel-witness contract

Defines `KernelWitnessCorrected` using `sourcePositiveWitness` and `sourceNegativeWitness`, with
source dual feasibility and `W ≥ 1` as hypotheses. The proposition explicitly requires both
witnesses to be nonzero and states their kernel and quantitative overlap properties.

This interface records the witness estimates for the reflection construction of [Reichardt2011].

## Main statements

* `KernelWitnessCorrected`: requires positive root concentration of `9/10` and negative squared
  overlap at least `1 / (9 * W * (W + 1))` times squared norm.

## References

* [Reichardt, 2011][Reichardt2011]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix

/-- The source dual-feasible contract asserting nonzero explicit positive and negative kernel
witnesses, with positive root mass at least `9/10` of squared norm and negative squared
overlap at least `1 / (9 * W * (W + 1))` times squared norm. -/
def KernelWitnessCorrected : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n m : ℕ)
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ),
    SourceDualFeasible input f v W → 1 ≤ W →
    (∀ x,f x=true →
      let ψ:=sourcePositiveWitness input f v W x
      ψ≠0 ∧ sourceMarkedBiadj input f v W x*ᵥψ=0 ∧
      (9/10 : ℝ)*(∑ c,‖ψ c‖^2) ≤ ‖ψ (Sum.inl ())‖^2) ∧
    (∀ x,f x=false →
      let ψ:=sourceNegativeWitness input f v x
      ψ≠0 ∧ (sourceRestrictedBiadj input f v x)ᴴ*ᵥψ=0 ∧
      (1/(9*W*(W+1)))*(∑ r,‖ψ r‖^2) ≤ ‖Qatlib.Foundations.PureStateMath.Inner (tvec W) (fun y=>ψ (Sum.inl y))‖^2)
end Qatlib.Concepts.QueryComplexity.Reflections
