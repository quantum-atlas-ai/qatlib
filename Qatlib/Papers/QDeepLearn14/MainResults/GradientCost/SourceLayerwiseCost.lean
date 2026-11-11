/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Total gradient cost over all components (Corollary 2)

Source: "Quantum Deep Learning", arXiv:1412.3489v2, Corollary 2, p.17.

If `N_op` is the number of quantum operations and oracle calls needed to compute a
single component of the gradient of `O_ML` (via Algorithm 4 or Corollary 1) for a
Boltzmann machine on a connected graph, then computing all `E` edge components of
the gradient costs `Õ(E · N_op)` operations, for constant learning rate `r`.

The paper's proof: "the proof is a trivial consequence of using the result of
Theorem 2 `O(E)` times to compute each of the components of the gradient vector."
We model the `E` components as a `Finset.range E` and prove that summing the
per-component cost `N_op` yields `E · N_op`. -/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QDeepLearn14.MainResults.GradientCost

/-- **Corollary 2** of arXiv:1412.3489 (p.17): computing each of the `E` gradient
components at cost `N_op` each gives total cost `E · N_op`. -/
theorem corollary2_totalCost (E : ℕ) (Nop : ℝ) :
    Finset.sum (Finset.range E) (fun _ => Nop) = (E : ℝ) * Nop := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Corollary 2, query half: the oracle calls are also additive over the `E`
components, so the total number of oracle calls is `E · (per-component calls)`. -/
theorem corollary2_totalOracleCalls (E : ℕ) (Nq : ℝ) :
    Finset.sum (Finset.range E) (fun _ => Nq) = (E : ℝ) * Nq :=
  corollary2_totalCost E Nq

end Qatlib.Papers.QDeepLearn14.MainResults.GradientCost
