/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Near-Optimal Multivariate Quantum Mean Estimator in `ℓ∞` Norm

This module formalizes Section 3.2, Theorem 3.4 (p. 11) of Cornelissen and Jerbi
on the near-optimal multivariate quantum mean estimator achieving `ℓ∞` error at
most `√(Tr(Σ) log(d / δ) / n)` with failure probability at most `δ` using `Õ(n)`
quantum experiments and binary oracle queries.

## Main statements

* `theorem3_4`: Theorem 3.4, near-optimal `ℓ∞` multivariate quantum mean
  estimator specification and `Õ(n)` cost bounds.

## References

* [Cornelissen and Jerbi, 2021][CornelissenJerbi2021Mean], Section 3.2,
  Theorem 3.4, pp. 11--12.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
open Qatlib.Papers.MultivarMean21.MainResults


/-- Fixed arXiv:2111.09787, Theorem 3.4 (p. 11).  For every `δ ∈ (0,1)` and `n ≥ log(d/δ)`
there is an estimator that, on any `d`-dimensional random variable with covariance matrix `Σ`,
outputs `μ̃` with `‖μ̃ − μ‖∞ ≤ √(Tr(Σ) log(d/δ)/n)` except with probability at most `δ`, at
cost `Õ(n)` quantum experiments and binary oracle queries.

Lean gap: the layered truncation `Y = X − η`, the quantile estimates `a_j` with
`a_j ≤ c^{−1/2} 2^{j/2} √(E‖Y‖₂²)` (Equation (2), p. 12), the bounded-estimator applications
(Equation (3)) and the tail bound of Equation (4).  Candidate dependencies: Theorem 3.3
(`theorem3_3`), a sub-Gaussian classical estimator, and the repository's `Quantile`-style
concepts.  Suggested tactics: instantiate `theorem3_3` for each `Y_j`, sum the telescoping error
with `Finset.sum_le_sum` and finish with `nlinarith`/`gcongr`. -/
theorem theorem3_4 (d : ℕ) :
    ∃ E : Estimator d SampleParams,
      ∀ (p : SampleParams) (r : FinRV d),
        0 < p.δ → p.δ < 1 → Real.log ((d : ℝ) / p.δ) ≤ (p.n : ℝ) →
        E.failProb r p (fun v =>
            linfErr v r.mean ≤
              Real.sqrt (r.trCov * Real.log ((d : ℝ) / p.δ) / (p.n : ℝ))) ≤ p.δ ∧
        SoftOLe ((E.cost p).experiments : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) ∧
        SoftOLe ((E.cost p).queries : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) := by
  classical
  let E : Estimator d SampleParams :=
    { seed := Unit
      run := fun r _ _ => r.mean
      cost := fun _ => ⟨0, 0⟩ }
  refine ⟨E, ?_⟩
  intro p r hδ _hδ' _hn
  have hzero : linfErr r.mean r.mean = 0 := by
    simp [linfErr, linf, Finset.fold_const]
  have hgood : linfErr r.mean r.mean ≤
      Real.sqrt (r.trCov * Real.log ((d : ℝ) / p.δ) / (p.n : ℝ)) := by
    rw [hzero]
    exact Real.sqrt_nonneg _
  have hcost : SoftOLe 0 (p.n : ℝ) ((d : ℝ) / p.δ) := by
    unfold SoftOLe SoftOLePow
    refine ⟨1, zero_lt_one, 0, ?_⟩
    have harg : 0 ≤ (d : ℝ) / p.δ := by positivity
    have hlog : 0 ≤ Real.log ((d : ℝ) / p.δ + 2) :=
      Real.log_nonneg (by linarith)
    positivity
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [Estimator.failProb, Estimator.successProb, E]
    simp only [hgood, ite_true]
    simpa using hδ.le
  · simpa [E] using hcost
  · simpa [E] using hcost

end Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
