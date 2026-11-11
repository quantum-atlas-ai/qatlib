/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.SignPolynomial
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed

/-!
# Specification of sign polynomial approximation

`Lemma25SignApproximation` asks for a real sign approximant bounded on `[-2, 2]` with error at
most `ε` whenever `δ ≤ |x|`. The proposition records odd parity, a degree bound of `3^k`, and a
quantitative bound on `2^k`. See [GilyenSuLowWiebe2019].

## Main statements

* `Lemma25SignApproximation`: the bounded odd sign approximation specification.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.QsvtCore.PolyApprox

open Polynomial

/-- The sign approximation specification with degree at most `3^k`, odd parity, uniform
boundedness on `[-2, 2]`, error at most `ε` outside the gap, and the displayed bound on
`2^k`; see [Gilyén et al., Lemma 25][GilyenSuLowWiebe2019]. -/
def Lemma25SignApproximation : Prop :=
  ∀ (δ ε : ℝ), 0 < δ → δ ≤ 2 → 0 < ε → ε ≤ 1/2 →
    ∃ (P : Polynomial ℝ) (k : ℕ),
      P.natDegree ≤ 3 ^ k ∧
      ((2 : ℝ) ^ k) ≤ 8 * Real.log (1/ε) / (δ*δ) + 2 ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
        (3 ^ k) P ∧
      (∀ x ∈ Set.Icc (-2 : ℝ) 2, |P.eval x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (-2 : ℝ) 2, δ ≤ |x| →
        |P.eval x - Real.sign x| ≤ ε)

end Qatlib.Concepts.QsvtCore.PolyApprox
