/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.Policy

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

def History {R : Type*} {S C : ℕ} : ErasurePolicy R S C → Type _
  | .done => PUnit
  | .random _ next => (r : R) × History (next r)
  | .noise width _ next => (mask : Fin width.val → Bool) × (r : R) × History (next mask r)

def historyWidths {R : Type*} {S C : ℕ} (policy : ErasurePolicy R S C) :
    History policy → Fin S → ℕ :=
  match policy with
  | .done => fun _ => Fin.elim0
  | .random _ next => fun h => historyWidths (next h.1) h.2
  | .noise width _ next => fun h => Fin.cons width.val (historyWidths (next h.1 h.2.1) h.2.2)

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
