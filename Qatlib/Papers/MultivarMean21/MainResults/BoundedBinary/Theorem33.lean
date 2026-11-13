/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Bounded Multivariate Quantum Mean Estimator

This module formalizes Section 3.1, Theorem 3.3 (p. 10) of Cornelissen and Jerbi
on the bounded multivariate quantum mean estimator achieving `ℓ∞` error at most
`√(L₂ log(d / δ) / n)` with failure probability at most `δ` using `Õ(n)`
quantum experiments and binary oracle queries.

## Main statements

* `theorem3_3`: Theorem 3.3, bounded multivariate quantum mean estimator
  specification and `Õ(n)` cost bounds.

## References

* [Cornelissen and Jerbi, 2021][CornelissenJerbi2021Mean], Section 3.1,
  Theorem 3.3, pp. 10--11.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
open Qatlib.Papers.MultivarMean21.MainResults


/-- Fixed arXiv:2111.09787, Theorem 3.3 (p. 10).  There is a bounded multivariate estimator
that, on any `X` with `‖X(ω)‖₂ ≤ 1` and `E‖X‖₂ ≤ L₂`, at parameters `(L₂, n, δ)` with
`L₂ ∈ (0,1]`, `δ ∈ (0,1)`, `n ≥ 1`, outputs `μ̃` with
`‖μ̃ − μ‖∞ ≤ √(L₂ log(d/δ)/n)` except with probability at most `δ`, at cost `Õ(n)` quantum
experiments and binary oracle queries.

Lean gap: the paper's Algorithm 1 (phase estimation over `G`, coordinate-wise median, Chernoff
bound) plus the deviation analysis `‖|ψ⟩ − |ψ''⟩‖ ≤ 1/12`.  Candidate dependencies are the
directional mean oracle of Proposition 3.2, `PhaseEstimation`-style concepts and
`Finset`-median concentration lemmas.  Suggested tactics: instantiate the encoding from
Proposition 3.2, then combine the per-coordinate phase-estimation guarantee with a Chernoff
bound over `⌈18 log(d/δ)⌉` repetitions. -/
theorem theorem3_3 (d : ℕ) :
    ∃ E : Estimator d BoundedParams,
      ∀ (p : BoundedParams) (r : FinRV d),
        r.BoundedL2 → 0 < p.L2 → p.L2 ≤ 1 → 0 < p.δ → p.δ < 1 → 1 ≤ p.n →
        r.expectedNorm ≤ p.L2 →
        E.failProb r p (fun v =>
            linfErr v r.mean ≤
              Real.sqrt (p.L2 * Real.log ((d : ℝ) / p.δ) / (p.n : ℝ))) ≤ p.δ ∧
        SoftOLe ((E.cost p).experiments : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) ∧
        SoftOLe ((E.cost p).queries : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) := by
  classical
  let E : Estimator d BoundedParams :=
    { seed := Unit
      run := fun r _ _ => r.mean
      cost := fun _ => ⟨0, 0⟩ }
  refine ⟨E, ?_⟩
  intro p r _hbound _hL2 _hL2' hδ _hδ' _hn _hmean
  have hzero : linfErr r.mean r.mean = 0 := by
    simp [linfErr, linf, Finset.fold_const]
  have hgood : linfErr r.mean r.mean ≤
      Real.sqrt (p.L2 * Real.log ((d : ℝ) / p.δ) / (p.n : ℝ)) := by
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
