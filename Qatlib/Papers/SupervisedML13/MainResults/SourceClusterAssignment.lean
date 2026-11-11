/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SupervisedML13.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c002 — supervised cluster assignment in `O(ε⁻¹ log(MN))`

Fixed arXiv:1307.0411v2, §"Supervised cluster assignment", p. 3–4:
the assignment algorithm estimates the distance `|u − (1/M)Σ_j v_j|` with
quantum counting (`O(ε⁻¹ log M)` iterations) after qRAM state preparation of
the `N`-dimensional vectors (`O(log N)` steps), i.e. `O(ε⁻¹ log(M N))` total.

The Lean statement is the exact arithmetic identity behind the asymptotic
claim: the accounted cost `ε⁻¹ (log₂ M + log₂ N + 2)` equals
`ε⁻¹ (log₂(M·N) + 2)`.  The logarithmic splitting is Mathlib's
`Real.logb_mul`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SupervisedML13.MainResults

/-- **c002** (paper p. 3–4).  For positive `M`, `N` the quantum assignment
cost `ε⁻¹ (log₂ M + log₂ N + 2)` is exactly `ε⁻¹ (log₂(M·N) + 2)`, the
paper's `O(ε⁻¹ log(MN))`.

Source: arXiv:1307.0411v2 p. 3 "We now exhibit a quantum algorithm for
performing the assignment problem that takes time `O(ε⁻¹ log(MN))`".
Proof step: `log₂(M·N) = log₂ M + log₂ N` (`Real.logb_mul`), then `ring`. -/
theorem quantum_assignment_runtime (ε : ℝ) (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    quantumAssignmentCost ε M N
      = ε⁻¹ * (Real.logb 2 ((M : ℝ) * (N : ℝ)) + 2) := by
  unfold quantumAssignmentCost
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  rw [Real.logb_mul hM0 hN0]

/-- **c002**, cost form.  The same identity with the logarithm exposed:
`log₂(M·N) + 2` is the `log₂ M + log₂ N + 2` sum that the algorithm accounts
for (qRAM preparation plus counting), for positive `M` and `N`. -/
theorem quantum_assignment_runtime_logb (ε : ℝ) (M N : ℕ) :
    quantumAssignmentCost ε M N
      = ε⁻¹ * (Real.logb 2 (M : ℝ) + Real.logb 2 (N : ℝ) + 2) := rfl

/-- **c002**, classical counterpart recorded for the comparison of c001: the
classical distance evaluation over `M` vectors of dimension `N` costs `M·N`
vector entries. -/
theorem classical_assignment_cost (M N : ℕ) :
    classicalAssignmentCost M N = (M : ℝ) * (N : ℝ) := rfl

end Qatlib.Papers.SupervisedML13.MainResults
