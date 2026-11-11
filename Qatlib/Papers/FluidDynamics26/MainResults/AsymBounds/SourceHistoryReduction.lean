/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FluidDynamics26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# FluidDynamics26 — reduction from final-state to history-state lower bounds

Fixed source: Ameri–Carolan–Childs–Krovi, *Quantum lower bounds for simulating fluid
dynamics*, arXiv:2603.12161v1 (12 March 2026), Theorem 26, p. 32.

c024 = Theorem 26: if preparing the final-time solution requires `Ω(f(T))` copies, then
preparing the history state requires `k = Ω(f(T)/T)` copies.  The paper's proof
post-selects the final-time slot from `O(T)` copies of the history state
(Eq. (243), p. 32); that step is recorded by the explicit hypothesis
`HistoryPostselection C`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FluidDynamics26.MainResults

/-- **c024, Theorem 26, p. 32**: if the final-time state requires `Ω(f(T))` copies to
accuracy `err`, and `O(T)` copies of the history state suffice to post-select the
final-time state (with the same accuracy), then the history state requires
`Ω(f(T)/T)` copies.

This is the paper's argument verbatim: with `k` copies of `|ψ(0)⟩` producing the history
state, the `O(T)` post-selection of Eq. (243) yields a final-state algorithm with
`O(T)·k` copies, contradicting the `Ω(f(T))` lower bound, so `k = Ω(f(T)/T)`.  The
post-selection cost is the explicit hypothesis `hpost`; the rest is arithmetic. -/
theorem theorem26_history_reduction {f err : ℝ → ℝ}
    (hf : ∀ T : ℝ, 1 ≤ T → 0 ≤ f T)
    (hfinal : RequiresCopiesForError f err)
    (hpost : ∃ C : ℝ, 0 < C ∧ HistoryPostselection C) :
    HistoryRequiresCopiesForError (fun T => f T / T) err := by
  obtain ⟨c, hc0, hc⟩ := hfinal
  obtain ⟨C, hC0, hpost⟩ := hpost
  refine ⟨c / C, div_pos hc0 hC0, ?_⟩
  intro H T hT herr
  obtain ⟨A, herrA, hcop⟩ := hpost H
  have hlow : c * f T ≤ (A.copies T : ℝ) := hc A T hT (by rw [herrA]; exact herr)
  have hup : (A.copies T : ℝ) ≤ C * T * (H.copies T : ℝ) := hcop T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hCT : 0 < C * T := mul_pos hC0 hT0
  have hchain : c * f T ≤ C * T * (H.copies T : ℝ) := le_trans hlow hup
  have hdiv : c * f T / (C * T) ≤ (H.copies T : ℝ) := by
    rw [div_le_iff₀ hCT]
    linarith
  have heq : c / C * (f T / T) = c * f T / (C * T) := by
    field_simp
  rwa [heq]

end Qatlib.Papers.FluidDynamics26.MainResults
