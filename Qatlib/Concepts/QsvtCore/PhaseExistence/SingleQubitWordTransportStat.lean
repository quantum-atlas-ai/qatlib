/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitSignal

/-!
# Specification of reflection word response entries

`SingleQubitWordTransport` states the first-column formulas for a reflection word built from
real phase angles. It connects `reflectionWord` to `sourcePhaseResponse` and the response
polynomial `responseQ` evaluated at the signal. See [GilyenSuLowWiebe2019].

## Main statements

* `SingleQubitWordTransport`: the upper and lower first-column identities.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- The assertion that the first-column entries of a reflection word on `[-1, 1]` equal the
upper source response and `sqrt (1 - x^2)` times the lower response. -/
def SingleQubitWordTransport : Prop :=
  ∀ (Φ : List ℝ) (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 →
    reflectionWord x Φ 0 0 = (sourcePhaseResponse Φ).eval (x : ℂ) ∧
    reflectionWord x Φ 1 0 =
      Real.sqrt (1 - x ^ 2) * (responseQ 1 (Φ.map anglePhase)).eval (x : ℂ)

end Qatlib.Concepts.QsvtCore.PhaseExistence
