/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalReciprocal
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed

/-!
# Statement of windowed reciprocal approximation

`Theorem41WindowedPolynomial` packages the existence of a real polynomial approximating
`(δ/2)/x` on `[δ, 1]` when `0 < ε ≤ δ ≤ 1/2`. The polynomial vanishes at zero, is bounded by one
on `[-1, 1]`, and has odd parity with an explicit degree bound.

The proposition also specifies bounds on the truncation parameters `J` and `k` for use in the
pseudoinverse construction associated with Theorem 41 of [GilyenSuLowWiebe2019].

## Main statements

* `Theorem41WindowedPolynomial`: defines the bounded reciprocal-approximation requirement with
  explicit parameter budgets.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Polynomial

/-- The proposition that, for 0 < ε ≤ δ ≤ 1/2, a real polynomial vanishing at zero approximates
(δ/2)/x within ε on [δ, 1] and is bounded by one on [-1, 1]. It also requires parity and
degree at most `2 * J + 1 + 2 * 3 ^ k`, together with explicit bounds on the truncation
parameters [GilyenSuLowWiebe2019]. -/
def Theorem41WindowedPolynomial : Prop :=
  ∀ (ε δ : ℝ), 0 < ε → ε ≤ δ → δ ≤ 1/2 →
    ∃ (Pw : Polynomial ℝ) (J k : ℕ),
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      Pw.natDegree ≤ 2*J+1+2*3^k ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
        (2*J+1+2*3^k) Pw ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε)

end Qatlib.Concepts.QsvtCore.LinearSystems
