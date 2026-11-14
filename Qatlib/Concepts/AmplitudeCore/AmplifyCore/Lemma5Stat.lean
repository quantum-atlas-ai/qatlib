/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma3RestrictedQuan
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma5Defs

@[expose] public section

/-!
# Specification of the general phase component action

`expected` expresses the good and bad component coefficients of
`amplitudeEstimationPhaseIterate` for success probability strictly between zero and one. The two
phase parameters are taken in the interval from zero to `2 * Real.pi`. See [BrassardEtAl2002]
for background.

## Main statements

* `expected`: The proposition giving the generalized phase iterate coefficients on good and bad
  components for success probability in `(0, 1)`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

open Qatlib.Concepts.AmplitudeCore.AmplifyCore

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma5Spec
/-- The proposition giving the generalized phase iterate coefficients on good and bad components
for success probability in `(0, 1)`. -/
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
  0 < a → a < 1 →
  let p : ℂ := Complex.exp ((φ : ℂ) * Complex.I);
  let q : ℂ := Complex.exp ((ϕ : ℂ) * Complex.I);
  let Q : H → H := amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ;
  Q ψ₁ =
      (q * ((1 - p) * (a : ℂ) - 1)) • ψ₁ +
      (q * (1 - p) * (a : ℂ)) • ψ₀ ∧
  Q ψ₀ =
      ((1 - p) * (1 - (a : ℂ))) • ψ₁ -
      ((1 - p) * (a : ℂ) + p) • ψ₀)
end Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma5Spec
