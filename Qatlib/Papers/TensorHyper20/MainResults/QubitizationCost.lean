/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.TensorHyper20.MainResults.Definitions

/-!
# Qubitization step and phase-estimation costs

Checks the decomposition of the tensor hypercontraction step cost into SELECT, preparation, and
reflection costs from [LeeEtAl2021]. It also records upper and lower bounds for the
natural-ceiling phase-estimation iteration count.

The theorem `eq45_total_cost` expresses the total Toffoli cost as the iteration count multiplied
by the cost per step.

## Main statements

* `eq44_decomposition`: sums the three cost contributions into `stepCost`.
* `eq45_iterations_lt`: bounds the iteration count above by the real expression plus one.
* `eq45_total_cost`: expresses total cost as iterations times step cost.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.QubitizationCost

open Qatlib.Papers.TensorHyper20.MainResults

/-- The SELECT, preparation, and reflection cost formulas sum to the expanded qubitization step
cost. -/
theorem eq44_decomposition (M N br ℵ i d ks1 ks2 kr1 kr2 : ℕ) :
    selectCost M N i kr1 kr2 + prepareCost M br ℵ d ks1 ks2 + reflectionCost M ℵ
      = stepCost M N br ℵ i d ks1 ks2 kr1 kr2 := by
  unfold selectCost prepareCost reflectionCost stepCost
  ring

/-- The phase-estimation iteration count is the natural ceiling of `π * lam / (2 * eps)`. -/
theorem eq45_qpeIterations_def (lam eps : ℝ) :
    qpeIterations lam eps = ⌈Real.pi * lam / (2 * eps)⌉₊ := rfl

/-- When `π * lam / (2 * eps)` is nonnegative, the iteration count is strictly less than this
expression plus one. -/
theorem eq45_iterations_lt (lam eps : ℝ) (h : 0 ≤ Real.pi * lam / (2 * eps)) :
    (qpeIterations lam eps : ℝ) < Real.pi * lam / (2 * eps) + 1 :=
  Nat.ceil_lt_add_one h

/-- The real phase-estimation expression `π * lam / (2 * eps)` is at most the natural iteration
count cast to the reals. -/
theorem eq45_iterations_ge (lam eps : ℝ) :
    Real.pi * lam / (2 * eps) ≤ (qpeIterations lam eps : ℝ) :=
  Nat.le_ceil _

/-- The total Toffoli cost equals the phase-estimation iteration count multiplied by the
qubitization step cost. See [LeeEtAl2021]. -/
theorem eq45_total_cost (M N br ℵ i d ks1 ks2 kr1 kr2 : ℕ) (lam eps : ℝ) :
    totalToffoli M N br ℵ i d ks1 ks2 kr1 kr2 lam eps
      = (qpeIterations lam eps : ℤ) * stepCost M N br ℵ i d ks1 ks2 kr1 kr2 := rfl

end Qatlib.Papers.TensorHyper20.MainResults.QubitizationCost
