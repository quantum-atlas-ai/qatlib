/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.Policy

/-!
# Histories and pathwise erasure budgets

This module records complete paths of `ErasurePolicy` as the dependent type `History` and
extracts their noise widths using `historyWidths`. Every recorded path respects the policy's
total budget, providing a pathwise cost statement for adaptive erasure analysis
[BhartiHaugTanggara2026].

## Main statements

* `History`: The type of complete random and noise outcomes along a policy path.
* `history_cost_le`: The total width on every history is at most the budget.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

/-- The dependent type of complete policy histories, recording random outcomes and both masks
and observations at noise steps. -/
def History {R : Type*} {S C : ℕ} : ErasurePolicy R S C → Type _
  | .done => PUnit
  | .random _ next => (r : R) × History (next r)
  | .noise width _ next => (mask : Fin width.val → Bool) × (r : R) × History (next mask r)

/-- The sequence of noise-step widths along a complete history of an erasure policy. -/
def historyWidths {R : Type*} {S C : ℕ} (policy : ErasurePolicy R S C) :
    History policy → Fin S → ℕ :=
  match policy with
  | .done => fun _ => Fin.elim0
  | .random _ next => fun h => historyWidths (next h.1) h.2
  | .noise width _ next => fun h => Fin.cons width.val (historyWidths (next h.1 h.2.1) h.2.2)

/-- The sum of the noise widths along any complete policy history is at most the policy budget
`C`. -/
theorem history_cost_le {R : Type*} {S C : ℕ} (policy : ErasurePolicy R S C)
    (history : History policy) : (∑ s, historyWidths policy history s) ≤ C := by
  induction policy with
  | done => simp [historyWidths]
  | random draw next ih => exact ih history.1 history.2
  | @noise steps budget width observe next ih =>
    rw [historyWidths, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have ht := ih history.1 history.2.1 history.2.2
    have hn : width.val ≤ budget := Nat.le_of_lt_succ width.isLt
    omega

end Qatlib.Foundations.ProbabilityCore.ErasureAdaptive
