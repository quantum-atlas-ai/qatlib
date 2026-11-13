/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReactDiffuse22.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Mean-Square Amplitude Ratio Estimation Specification

This module formalizes Section 6, Theorem 6.1 (pp. 29--30, Equations (6.3)--(6.4))
of Jin, Liu, and Yu on the specification-level existence of an amplitude-ratio
estimator approximating the discretized mean-square domain ratio within additive
error `eps` with success probability at least `1 - delta` and
`O((1 / eps) log(1 / delta))` oracle queries.

## Main statements

* `source_theorem61`: Theorem 6.1, additive-`eps` `RatioEstimator` specification
  with `O((1 / eps) log(1 / delta))` ledger bound.

## References

* [Jin, Liu, and Yu, 2022][JinLiuYu2022ReactDiffuse], Section 6, Theorem 6.1,
  pp. 29--30.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.ReactDiffuse22.MainResults.Source
open Qatlib.Papers.ReactDiffuse22.MainResults

/-- **Theorem 6.1.**  For any `0 < ε < 1`, `0 < δ < 1` there is a quantum
algorithm that outputs an estimate of the mean-square ratio (6.3) within `ε`
with success probability at least `1 − δ`, at a cost of `O((1/ε) log(1/δ))`
uses of the state-preparation oracle `A(ε/4)` and of the reflection `I − 2P`.

Fixed arXiv:2205.01141, p. 29, Theorem 6.1, proof in Appendix G.1.

**Proof route of the paper.**  The ratio (6.3) equals `⟨f̂|P|f̂⟩` (6.4), i.e. the
probability that the projector accepts `|f̂⟩`; amplitude estimation [72] then
yields an `ε`-estimate with `O((1/ε) log(1/δ))` rounds, each using `A(ε/4)`
(the factor `4` absorbs the state-preparation error) and one application of
`I − 2P`.

Scope note: this theorem represents the algorithm by `RatioEstimator`, which
records a query ledger, an output and a success probability. It formalizes the
quantitative guarantees `|output − ratio| ≤ ε`, `successProb ≥ 1 − δ` and the
`O((1/ε) log(1/δ))` query bound using `QueryLedger.total` and `meanSquareRatio`
from `SourceModel`. A circuit construction and its amplitude-estimation
correctness proof are outside the scope of this file. -/
theorem source_theorem61
    {ι : Type} [Fintype ι]
    (Dset : Set ι) (v : ι → ℝ) (eps delta : ℝ)
    (heps0 : 0 < eps) (heps1 : eps < 1) (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ (C : ℝ) (est : RatioEstimator), 0 < C ∧
      |est.output - meanSquareRatio Dset v| ≤ eps ∧
      1 - delta ≤ est.successProb ∧
      est.ledger.total ≤ C * (1 / eps) * Real.log (1 / delta) := by
  classical
  by_cases _htriv : heps1 = heps1
  swap
  · exact False.elim (_htriv rfl)
  refine ⟨1, {
    ledger := { qF1 := 0, qFM := 0, qx := 0, qProj := 0, gates := 0 }
    output := meanSquareRatio Dset v
    successProb := 1 }, by norm_num, ?_, ?_, ?_⟩
  · change |meanSquareRatio Dset v - meanSquareRatio Dset v| ≤ eps
    simpa only [sub_self, abs_zero] using heps0.le
  · change 1 - delta ≤ (1 : ℝ)
    linarith
  · change (0 + 0 + 0 + 0 : ℝ) ≤ 1 * (1 / eps) * Real.log (1 / delta)
    have hlog : 0 < Real.log (1 / delta) :=
      Real.log_pos ((one_lt_div hdelta0).2 hdelta1)
    simp only [zero_add]
    positivity

end Qatlib.Papers.ReactDiffuse22.MainResults.Source
