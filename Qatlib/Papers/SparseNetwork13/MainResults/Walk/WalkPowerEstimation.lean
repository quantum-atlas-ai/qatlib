/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.CostModel

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — ENA via the quantum walk (Theorem 5, Corollary 3)

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

* **Theorem 5** (§4.3, p.28) — ENA-P is solvable by the walk-based algorithm with
  `O(min{c^{0.5}d^{1.5}/(ε λ), c d^{0.5}/(ε λ^{1.5})}·poly log(cd/(ε λ)))` uses of
  `P_v, P_e, P_i`; the two branches correspond to implementing `U(A,B)` by Lemma 12
  (`O(d)` per call) resp. Lemma 13 (`O(√(c/λ))` per call).
* **Corollary 3** (§4.3, p.32) — ENA-ER has the same cost.

The algorithm is **not built**; recorded are the `min` cost function, its positivity, and the
two branch bounds (`costTheorem5 ≤ costTheorem5BranchA`, `≤ costTheorem5BranchB`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SparseNetwork13.MainResults.Walk

open Qatlib.Papers.SparseNetwork13.MainResults.Model

/-- **Theorem 5 (arXiv:1311.1851v10, §4.3, p.28).**  The walk-based ENA-P cost is the minimum
of the two branches `c^{0.5}d^{1.5}/(ελ)` and `c d^{0.5}/(ελ^{1.5})`; it is positive and does
not exceed either branch.  Built: the cost function, positivity, and the branch bounds.
Not built: the walk-based ENA-P algorithm and its amplitude-estimation analysis. -/
theorem theorem5_walk_power_cost (c d lam eps : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hlam : 0 < lam) (heps : 0 < eps) :
    0 < costTheorem5 c d lam eps ∧
      costTheorem5 c d lam eps ≤ costTheorem5BranchA c d lam eps ∧
      costTheorem5 c d lam eps ≤ costTheorem5BranchB c d lam eps := by
  have hA : 0 < costTheorem5BranchA c d lam eps := by
    unfold costTheorem5BranchA
    positivity
  have hB : 0 < costTheorem5BranchB c d lam eps := by
    unfold costTheorem5BranchB
    positivity
  refine ⟨?_, min_le_left _ _, min_le_right _ _⟩
  unfold costTheorem5
  exact lt_min hA hB

/-- **Corollary 3 (arXiv:1311.1851v10, §4.3, p.32).**  ENA-ER via the walk has the same cost
as Theorem 5 (the `√2` rescaling of the external current only affects the output by a factor
`2`).  Built: the cost equality and positivity.  Not built: the algorithm. -/
theorem corollary3_effective_resistance_cost (c d lam eps : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hlam : 0 < lam) (heps : 0 < eps) :
    costCorollary3 c d lam eps = costTheorem5 c d lam eps ∧
      0 < costCorollary3 c d lam eps := by
  refine ⟨rfl, ?_⟩
  unfold costCorollary3
  exact (theorem5_walk_power_cost c d lam eps hc hd hlam heps).1

end Qatlib.Papers.SparseNetwork13.MainResults.Walk
