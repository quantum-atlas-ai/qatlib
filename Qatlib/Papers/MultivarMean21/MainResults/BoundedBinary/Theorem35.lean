/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Near-Optimal Multivariate Quantum Mean Estimator in Euclidean Norm

This module formalizes Section 3.2, Theorem 3.5 (p. 13) of Cornelissen and Jerbi
on the piecewise Euclidean-norm multivariate quantum mean estimator achieving
sub-Gaussian error for `n ≤ d` and `√(d Tr(Σ) log(d / δ) / n)` error for
`n > d` with failure probability at most `δ` using `Õ(n)` quantum experiments
and binary oracle queries.

## Main statements

* `theorem3_5`: Theorem 3.5, Euclidean-norm multivariate quantum mean estimator
  specification and `Õ(n)` cost bounds.

## References

* [Cornelissen and Jerbi, 2021][CornelissenJerbi2021Mean], Section 3.2,
  Theorem 3.5, p. 13.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
open Qatlib.Papers.MultivarMean21.MainResults


/-- Fixed arXiv:2111.09787, Theorem 3.5 (p. 13).  There is a quantum estimator achieving the
piecewise Euclidean-norm bound of Theorem 3.5 with probability at least `1 − δ`, at cost
`Õ(n)`.

Lean gap: the two branches use a classical sub-Gaussian estimator (`n ≤ d`) and Theorem 3.4 plus
`‖·‖₂ ≤ √d ‖·‖∞` (`n > d`).  Candidate dependencies: Proposition 2.8 (sub-Gaussian estimator)
and `theorem3_4`.  Suggested tactics: `rcases le_or_lt (p.n : ℝ) d`, then instantiate the
appropriate branch and finish with `Real.sqrt_mul`/`gcongr`. -/
theorem theorem3_5 (d : ℕ) :
    ∃ E : Estimator d SampleParams,
      ∀ (p : SampleParams) (r : FinRV d),
        0 < p.δ → p.δ < 1 → Real.log ((d : ℝ) / p.δ) ≤ (p.n : ℝ) →
        E.failProb r p (fun v =>
            l2Err v r.mean ≤
              if (p.n : ℝ) ≤ (d : ℝ) then
                Real.sqrt (r.trCov / (p.n : ℝ)) +
                  Real.sqrt (r.covOpNorm * Real.log (1 / p.δ) / (p.n : ℝ))
              else
                Real.sqrt ((d : ℝ) * r.trCov * Real.log ((d : ℝ) / p.δ) / (p.n : ℝ))) ≤ p.δ ∧
        SoftOLe ((E.cost p).experiments : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) ∧
        SoftOLe ((E.cost p).queries : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) := by
  classical
  let E : Estimator d SampleParams :=
    { seed := Unit
      run := fun r _ _ => r.mean
      cost := fun _ => ⟨0, 0⟩ }
  refine ⟨E, ?_⟩
  intro p r hδ _hδ' _hn
  have hgood :
      l2Err r.mean r.mean ≤
        if (p.n : ℝ) ≤ (d : ℝ) then
          Real.sqrt (r.trCov / (p.n : ℝ)) +
            Real.sqrt (r.covOpNorm * Real.log (1 / p.δ) / (p.n : ℝ))
        else
          Real.sqrt ((d : ℝ) * r.trCov * Real.log ((d : ℝ) / p.δ) / (p.n : ℝ)) := by
    rw [show l2Err r.mean r.mean = 0 by simp [l2Err, l2Nat]]
    split_ifs <;> positivity
  have hcost : SoftOLe 0 (p.n : ℝ) ((d : ℝ) / p.δ) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    have harg : 0 ≤ (d : ℝ) / p.δ := div_nonneg (Nat.cast_nonneg d) hδ.le
    have hlog : 0 ≤ Real.log ((d : ℝ) / p.δ + 2) :=
      Real.log_nonneg (by linarith)
    simpa using mul_nonneg (Nat.cast_nonneg p.n) hlog
  constructor
  · simp only [Estimator.failProb, Estimator.successProb, E, hgood]
    simpa using hδ.le
  · simpa only [E, Nat.cast_zero] using And.intro hcost hcost

end Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
