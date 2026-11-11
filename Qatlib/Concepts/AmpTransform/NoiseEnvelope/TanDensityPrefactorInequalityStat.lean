/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities

/-!
# Specification of tangent-prefactor gain bounds

`TanDensityPrefactorInequality` records an upper density-prefactor bound and a lower bound using
1−2T²/N for the rounded Grover gain. It includes the tangent-density identity and gain
positivity for the amplified-transform parameters of [Cornwell2014].

## Main statements

* `TanDensityPrefactorInequality`: The contract bounding tan²θ times the gain between pref ·
  (1−2T²/N) and pref, with pref = (T/N)(N/(N−T)), together with tan²θ = T/(N−T) and 0 < gain ≤
  1.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope

/-- The contract bounding tan²θ times the gain between pref · (1−2T²/N) and pref, with pref =
(T/N)(N/(N−T)), together with tan²θ = T/(N−T) and 0 < gain ≤ 1. -/
def TanDensityPrefactorInequality : Prop :=
  ∀ (N T : ℕ), 0 < N → 2 ≤ T → 2 * T ≤ N →
    let θ := aqAngle N T
    let k := aqRounds N T
    let pref : ℝ := ((T : ℝ) / (N : ℝ)) * ((N : ℝ) / ((N - T : ℕ) : ℝ))
    let gain : ℝ := (Real.sin (2 * (k : ℝ) * θ)) ^ 2
    (Real.tan θ) ^ 2 * gain ≤ pref ∧
    pref * (1 - 2 * (T : ℝ) ^ 2 / (N : ℝ)) ≤ (Real.tan θ) ^ 2 * gain ∧
    (Real.tan θ) ^ 2 = ((T : ℝ) / ((N - T : ℕ) : ℝ)) ∧
    0 < gain ∧ gain ≤ 1

end Qatlib.Concepts.AmpTransform.NoiseEnvelope
