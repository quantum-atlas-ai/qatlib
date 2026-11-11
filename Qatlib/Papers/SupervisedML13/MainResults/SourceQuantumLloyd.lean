/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SupervisedML13.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c004 — quantum Lloyd's algorithm step in `O(M log(MN))`

Fixed arXiv:1307.0411v2, p. 4: every one of the `M` vectors is tested
individually for reassignment at each step, and each test is the distance
evaluation of the supervised algorithm on `N`-dimensional vectors.  The
classical step costs `O(M² N)`; the quantum step costs
`O(M log(M N))`.

The Lean statement is the exact accounting identity
`M · (log₂ M + log₂ N + 2) = M · (log₂(M·N) + 2)`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SupervisedML13.MainResults

/-- **c004** (paper p. 4).  For positive `M`, `N` the per-step quantum Lloyd
cost `M (log₂ M + log₂ N + 2)` equals `M (log₂(M·N) + 2)`, the paper's
`O(M log(MN))`.

Source: arXiv:1307.0411v2 p. 4 "...while the quantum Lloyd's algorithm takes
time `O(M log(MN))`.  The additional factor of `M` in both classical and
quantum algorithms arises because every vector is tested individually for
reassignment at each step."
Proof step: `Real.logb_mul` then `ring`. -/
theorem quantum_lloyd_step_runtime (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    lloydStepQuantumCost M N
      = (M : ℝ) * (Real.logb 2 ((M : ℝ) * (N : ℝ)) + 2) := by
  unfold lloydStepQuantumCost
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  rw [Real.logb_mul hM0 hN0]

/-- **c004**, classical counterpart (paper p. 4): the classical step tests
every one of the `M` vectors against `M` centroids in dimension `N`, costing
`M² N`.  This is recorded as the comparison object for c001. -/
theorem classical_lloyd_step_runtime (M N : ℕ) :
    lloydStepClassicalCost M N = (M : ℝ) ^ 2 * (N : ℝ) := rfl

end Qatlib.Papers.SupervisedML13.MainResults
