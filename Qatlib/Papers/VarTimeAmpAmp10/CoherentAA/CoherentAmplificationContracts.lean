/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation

/-!
# The coherent amplification window

This module defines `coherentAmplificationWindow`, the prepared amplitude-amplification
statement used in the variable-time analysis of [Ambainis2012]. It records the exact
sine-squared success probability, a quadratic lower bound within the first-quadrant window, and
a global upper bound.

## Main statements

* `coherentAmplificationWindow`: State the exact success formula and its window bounds for
  unitary preparations.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentAA

open Matrix

/-- The proposition that prepared amplitude amplification has success probability `sin²((2k +
1)θ)`, with the stated quadratic lower bound when `(2k + 1)θ ≤ π / 2` and the stated upper
bound capped at one. -/
def coherentAmplificationWindow : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ), W ∈ Matrix.unitaryGroup I ℂ →
    ∀ (j₀ : I) (S : Finset I) (k : ℕ),
      let a := MeasureProb (ApplyGate W (Ket j₀)) S
      let θ := Real.arcsin (Real.sqrt a)
      let out := Run (preparedMark S) (preparedAACircuit W j₀ k) (Ket j₀)
      MeasureProb out S = Real.sin ((2 * (k : ℝ) + 1) * θ) ^ 2 ∧
      ((2 * (k : ℝ) + 1) * θ ≤ Real.pi / 2 →
        (4 / Real.pi ^ 2) * (2 * (k : ℝ) + 1) ^ 2 * a ≤ MeasureProb out S) ∧
      MeasureProb out S ≤ min ((Real.pi ^ 2 / 4) * (2 * (k : ℝ) + 1) ^ 2 * a) 1

end Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
