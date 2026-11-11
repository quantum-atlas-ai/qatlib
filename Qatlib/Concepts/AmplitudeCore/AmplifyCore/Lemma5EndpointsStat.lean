/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma5Quan
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# General phase action including endpoint probabilities

`expected` specifies the good and bad component action of `amplitudeEstimationPhaseIterate`
without restricting the success probability to the open unit interval. This includes the cases
where one of the two components vanishes. See [BrassardEtAl2002] for background.

## Main statements

* `expected`: The generalized phase component action proposition, valid also when the good
  component has squared norm zero or one.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open Qatlib.Concepts.AmplitudeCore.AmplifyCore

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma5EndpointsSpec
/-- The generalized phase component action proposition, valid also when the good component has
squared norm zero or one. -/
def expected : Prop :=
  (∀ (ι H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H) (zeroIndex : ι)
    (A : H ≃ₗᵢ[ℂ] H) (χ : ι → Bool) (φ ϕ : ℝ),
  0 ≤ φ → φ < 2 * Real.pi →
  0 ≤ ϕ → ϕ < 2 * Real.pi →
  let G := amplitudeEstimationGoodSubspace basis χ;
  let ψ : H := A (basis zeroIndex);
  let ψ₁ : H := G.toSubmodule.starProjection ψ;
  let ψ₀ : H := ψ - ψ₁;
  let a : ℝ := ‖ψ₁‖ ^ 2;
  let p : ℂ := Complex.exp ((φ : ℂ) * Complex.I);
  let q : ℂ := Complex.exp ((ϕ : ℂ) * Complex.I);
  let Q : H → H := amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ;
  Q ψ₁ =
      (q * ((1 - p) * (a : ℂ) - 1)) • ψ₁ +
      (q * (1 - p) * (a : ℂ)) • ψ₀ ∧
  Q ψ₀ =
      ((1 - p) * (1 - (a : ℂ))) • ψ₁ -
      ((1 - p) * (a : ℂ) + p) • ψ₀)
end Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma5EndpointsSpec
