/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SupervisedML13.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c006 — nonlinear metric evaluation in `O(ε⁻¹ q log N)`

Fixed arXiv:1307.0411v2, §"Extension to nonlinear metrics", p. 6.

Given `q` copies of `|u⟩`, `|v⟩`, quantum counting estimates
`(⟨u|⟨v|)^{⊗k} L (|u⟩|v⟩)^{⊗k}` for arbitrary Hermitian `L`, allowing
distance measures that are `q`-th order polynomials in the entries `u_j`,
`v_j`.  Measuring the expectation value of `L` to accuracy `ε` needs
`O(ε⁻¹ q log N)` steps; the dimension dependence is `O(log N)`.

The Lean statement records that the `q`-fold product of the logarithmic
per-copy cost is itself logarithmic in `N^q`: `q log₂ N = log₂(N^q)`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SupervisedML13.MainResults

/-- **c006** (paper p. 6).  The `q`-copy nonlinear-metric cost
`ε⁻¹ q (log₂ N + 1)` equals `ε⁻¹ (log₂(N^q) + q)`: the `q`-fold repetition
only adds `log₂(N^q) = q log₂ N`, the paper's `O(ε⁻¹ q log N)` with the
dimension dependence reduced to `O(log N)`.

Source: arXiv:1307.0411v2 p. 6 "Measurement of the expectation value of `L`
to accuracy `ε` using quantum counting requires `O(ε⁻¹ q log N)` steps.  Once
again, the quantum algorithm reduces the dimension dependence of the
evaluation of distance to `O(log N)`."
Proof step: `Real.logb_pow`, then `ring`. -/
theorem nonlinear_metric_runtime (ε : ℝ) (q N : ℕ) :
    nonlinearMetricCost ε q N
      = ε⁻¹ * (Real.logb 2 ((N : ℝ) ^ q) + (q : ℝ)) := by
  unfold nonlinearMetricCost
  rw [Real.logb_pow]
  ring

/-- **c006**, cost is additive in the `q` copies and proportional to the
accuracy budget: the accounted cost factors as `q · (ε⁻¹ (log₂ N + 1))`.
This is the `q`-fold repetition structure of the nonlinear metric
estimation. -/
theorem nonlinear_metric_cost_factor (ε : ℝ) (q N : ℕ) :
    nonlinearMetricCost ε q N = (q : ℝ) * (ε⁻¹ * (Real.logb 2 (N : ℝ) + 1)) := by
  unfold nonlinearMetricCost
  ring

end Qatlib.Papers.SupervisedML13.MainResults
