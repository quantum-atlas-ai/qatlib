/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma1Quan
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.l2Space
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem2QuadraticSpeedupAuxiliary

/-!
# Specification of the quadratic amplification bound

`expected` records the Grover success lower bound for a prepared state with positive success
probability. The iteration count is the natural floor of `Real.pi / (4 * θ)` for a success angle
satisfying `sin θ^2 = a`. See [BrassardEtAl2002] for background.

## Main statements

* `expected`: The proposition that `floor (π / (4 * θ))` Grover steps achieve success
  probability at least `max (1 - a) a` for positive `a = sin θ^2`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore

end Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem2SpeedupSpec
/-- The proposition that `floor (π / (4 * θ))` Grover steps achieve success probability at least
`max (1 - a) a` for positive `a = sin θ^2`. -/
def expected : Prop :=
  (∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : Set ℤ) (hzero : (0 : ℤ) ∈ S)
    (basis : HilbertBasis S ℂ E) (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool),
  let e₀ : E := basis ⟨0, hzero⟩;
  let P : E →L[ℂ] E := AmplitudeAmplificationCore.goodProjection basis χ;
  let ψ : E := A e₀;
  let a : ℝ := ‖P ψ‖ ^ 2;
  ∀ (θ : ℝ),
    0 < a → 0 < θ → θ ≤ Real.pi / 2 → Real.sin θ ^ 2 = a →
    let m : ℕ := Nat.floor (Real.pi / (4 * θ));
    max (1 - a) a ≤
      ‖P (((AmplitudeAmplificationCore.step A e₀ P)^[m]) ψ)‖ ^ 2)
end Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem2SpeedupSpec
