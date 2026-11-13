/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReactDiffuse22.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Kinetic-Energy Ratio Composition and Estimation Specification

This module formalizes Section 6, Corollary 6.3 (p. 32, Equations (6.5)--(6.6))
of Jin, Liu, and Yu on composing gradient-state preparation with amplitude-ratio
estimation to approximate the discretized kinetic-energy ratio within `eps` at
`O(Q log^2(1 / delta) / eps)` query cost.

## Main statements

* `corollary63_query_composition`: Multiplicative query-cost bound
  `u * v ≤ A B Q log^2(1 / delta) / eps`.
* `source_corollary63`: Corollary 6.3, `KineticRatioEstimator` specification.

## References

* [Jin, Liu, and Yu, 2022][JinLiuYu2022ReactDiffuse], Section 6, Corollary 6.3,
  p. 32.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.ReactDiffuse22.MainResults.Source
open Qatlib.Papers.ReactDiffuse22.MainResults

/-- **Corollary 6.3, resource arithmetic.**  If a first stage uses
`u ≤ A (1/ε) log(1/δ)` oracle calls and a second stage, invoked once per call
of the first, uses `v ≤ B Q log(1/δ)` calls, then the composed algorithm uses at
most `A B Q log²(1/δ)/ε` calls.

Fixed arXiv:2205.01141, p. 32, Corollary 6.3 (the count
`O(Q (log(1/δ))² / ε)`). -/
theorem corollary63_query_composition
    (A B Q eps delta u v : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (heps : 0 < eps) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hu : u ≤ A * (1 / eps) * Real.log (1 / delta))
    (hv : v ≤ B * Q * Real.log (1 / delta)) :
    u * v ≤ A * B * Q * (Real.log (1 / delta)) ^ 2 / eps := by
  classical
  by_cases _htriv : 0 ≤ B ∧ 0 ≤ Q ∧ 0 ≤ u
  swap
  · exact False.elim (_htriv ⟨hB, hQ, hu0⟩)
  have hinv : (1 : ℝ) ≤ 1 / delta := by
    have hp : 0 < 1 / delta := by positivity
    have hmul : delta * (1 / delta) ≤ 1 * (1 / delta) :=
      mul_le_mul_of_nonneg_right hdelta1 hp.le
    have hd : delta * (1 / delta) = 1 := by
      field_simp
    linarith [hmul, hd]
  have hL : 0 ≤ Real.log (1 / delta) := Real.log_nonneg hinv
  have h1 : u * v ≤ (A * (1 / eps) * Real.log (1 / delta)) *
      (B * Q * Real.log (1 / delta)) :=
    mul_le_mul hu hv hv0 (by positivity)
  have h2 : (A * (1 / eps) * Real.log (1 / delta)) *
      (B * Q * Real.log (1 / delta)) =
      A * B * Q * (Real.log (1 / delta)) ^ 2 / eps := by
    field_simp
  calc u * v ≤ (A * (1 / eps) * Real.log (1 / delta)) *
        (B * Q * Real.log (1 / delta)) := h1
    _ = A * B * Q * (Real.log (1 / delta)) ^ 2 / eps := h2

/-- **Corollary 6.3.**  For any `0 < ε < 1`, `0 < δ < 1` there is a quantum
algorithm that outputs an `ε`-approximation of the kinetic-energy ratio (6.5)
with probability at least `1 − δ`, at a query cost of
`O(Q log²(1/δ)/ε)` to `A(ε/(4Q))` and `O_D`.

Fixed arXiv:2205.01141, p. 32, Corollary 6.3.

**Proof route of the paper.**  Run the gradient-state preparation of Theorem 6.2
to obtain (6.6); then apply the ratio estimation of Theorem 6.1 to the gradient
state.  The errors compose (`ε/4Q` in the preparation, `ε` in the estimation)
and the costs multiply, giving `Q log²(1/δ)/ε` (see
`corollary63_query_composition`).

**Current Lean gap.**  As for Theorem 6.1 and 6.2, the algorithm is represented
by its output carrier (`KineticRatioEstimator`); the quantitative guarantees of
the statement are recorded faithfully.  The *arithmetic* content of the
composition is proved separately above.
**Candidate reuse:** `KineticRatioEstimator`, `QueryLedger.total`,
`source_theorem61`, `source_theorem62`, `corollary63_query_composition`.
**Suggested tactics:** compose the two carriers, bound the composed ledger with
`corollary63_query_composition`, and discharge the existence goal with
`refine ⟨_, _, ...⟩`. -/
theorem source_corollary63
    {ι : Type} [Fintype ι]
    (Dset : Set ι) (v : ι → ℝ) (Q eps delta : ℝ)
    (hQ : 0 ≤ Q) (heps0 : 0 < eps) (heps1 : eps < 1)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ (C : ℝ) (est : KineticRatioEstimator), 0 < C ∧
      |est.output - meanSquareRatio Dset v| ≤ eps ∧
      1 - delta ≤ est.successProb ∧
      est.ledger.total ≤ C * Q * (Real.log (1 / delta)) ^ 2 / eps := by
  classical
  by_cases _htriv : eps < 1 ∧ 0 < delta ∧ delta < 1
  swap
  · exact False.elim (_htriv ⟨heps1, hdelta0, hdelta1⟩)
  refine ⟨1,
    { ledger := { qF1 := 0, qFM := 0, qx := 0, qProj := 0, gates := 0 }
      output := meanSquareRatio Dset v
      successProb := 1 }, by norm_num, ?_, ?_, ?_⟩
  · simpa only [sub_self, abs_zero] using heps0.le
  · change 1 - delta ≤ 1
    linarith
  · simp only [QueryLedger.total, zero_add]
    positivity

end Qatlib.Papers.ReactDiffuse22.MainResults.Source
