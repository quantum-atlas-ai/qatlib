/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FluidDynamics26.MainResults.SourceModel
import Qatlib.Papers.FluidDynamics26.MainResults.FidelityMetric.SourceFidelityMetricCore
import Qatlib.Papers.FluidDynamics26.MainResults.AsymBounds.SourceHistoryReduction

set_option backward.isDefEq.respectTransparency false

/-!
# FluidDynamics26 — copy-complexity lower bounds for the KdV equation

Fixed source: Ameri–Carolan–Childs–Krovi, *Quantum lower bounds for simulating fluid
dynamics*, arXiv:2603.12161v1 (12 March 2026).

Claims formalised here:

* c009 = Corollary 11, Eq. (90), p. 16 — `k = Ω((d(v(T),v'(T)) / d(v(0),v'(0)))²)`;
* c010 = Corollary 12, Eqs. (91)–(93), p. 16 — `k = e^{Ω(T)}`;
* c025 = Corollary 27, p. 33 — KdV history state needs `Ω(T)` copies.

Theorem 15 (c013, the `Ω(T²)` bound) is not formalized: its proof instantiates
Corollary 11 at the soliton pair of Lemmas 13/14 (c011/c012), neither of which is
formalized.  The statement is preserved in this branch's history.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FluidDynamics26.MainResults

open MeasureTheory Filter

open scoped BigOperators Topology

/-! ## c009 — Corollary 11, Eq. (90), p. 16 -/

/-- **c009, Corollary 11, Eq. (90), p. 16**: if two trajectories have initial and final
distances `d0 = d(v(0),v'(0))` and `dT = d(v(T),v'(T))`, both non-zero, and the copies `k`
satisfy the Lemma 10 chain `dT ≤ 2δ + sqrt(k)·d0` for `δ = dT/4` (the triangle-inequality
step of Lemma 10 with the error half of the target separation), then
`(dT/d0)²/4 ≤ k`, i.e. `k = Ω((dT/d0)²)`.

This is the exact arithmetic content of Corollary 11: Lemma 10 (c008) gives
`k ≥ ((dT - 2δ)/d0)²`, and choosing `δ = dT/4` (valid whenever `dT > 0`) yields the
`1/4` constant.  The two `Ω(1)`-normalization hypotheses of the corollary enter only
through the chain inequality, which is where Lemma 3 (c002) is used to convert the
overlap `|⟨v|v'⟩|` into the Euclidean distance. -/
theorem corollary11_ratio_squared_lower_bound
    {k : ℕ} {d0 dT : ℝ} (hd0 : 0 < d0) (hdT : 0 < dT)
    (hchain : dT ≤ dT / 2 + Real.sqrt (k : ℝ) * d0) :
    (dT / d0) ^ 2 / 4 ≤ (k : ℝ) := by
  have h := lemma10_copy_lower_bound k (ε₀ := d0) (εf := dT) (δ := dT / 4) hd0
    (by linarith) (by linarith)
  have heq : dT - 2 * (dT / 4) = dT / 2 := by ring
  rw [heq] at h
  have hdiv : (dT / 2) / d0 = dT / (2 * d0) := by field_simp
  rw [hdiv] at h
  have hkey : (dT / (2 * d0)) ^ 2 = (dT / d0) ^ 2 / 4 := by
    field_simp
    ring
  calc (dT / d0) ^ 2 / 4 = (dT / (2 * d0)) ^ 2 := hkey.symm
    _ ≤ (k : ℝ) := h

/-! ## c010 — Corollary 12, Eqs. (91)–(93), p. 16 -/

/-- **c010, Corollary 12, Eqs. (91)–(93), p. 16**: suppose, for every `0 < ε < 1`, the
initial overlap `|⟨v(0)|v'(0)⟩| = 1 - O(ε)` and the final overlap
`|⟨v(T)|v'(T)⟩| = 1 - Ω(ε^α)` with `T = O(log(1/ε))` yield (via Corollary 11) the copy
lower bound `k ≥ ε^{α-1}` for every exact simulation of time `T`, `1 ≤ T ≤ log(1/ε)/α`.
Then any exact algorithm requires `k = e^{Ω(T)}` copies, namely
`exp(α(1-α)T) ≤ copies`.

The hypothesis `h11` is exactly Corollary 11 (c009) instantiated at the ε-parametrised
pair of solutions: the overlap deficits `1 - O(ε)` and `1 - Ω(ε^α)` convert through
Lemma 3 (c002) into `d0 = O(√ε)`, `dT = Ω(ε^{α/2})`, so `(dT/d0)² = Ω(ε^{α-1})`.  The
paper then substitutes `ε = e^{-αT}` (from `T = O(log(1/ε))`) to obtain `e^{Ω(T)}`.

The proof below is the paper's final substitution and exponent arithmetic, carried out
for an exact algorithm (`error T ≤ 0`, so that `h11` applies at every `ε`). -/
theorem corollary12_exponential_lower_bound
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (h11 : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ (A : FinalStateAlgorithm) (T : ℝ), 1 ≤ T →
        T ≤ Real.log (1 / ε) / α → A.error T ≤ ε →
          ε ^ (α - 1) ≤ (A.copies T : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : FinalStateAlgorithm) (T : ℝ), 1 ≤ T →
      A.error T ≤ 0 → c * Real.exp (α * (1 - α) * T) ≤ (A.copies T : ℝ) := by
  refine ⟨1, one_pos, ?_⟩
  intro A T hT herr
  have hT0 : (0 : ℝ) < T := by linarith
  have hαT : 0 < α * T := mul_pos hα0 hT0
  set ε : ℝ := Real.exp (-(α * T)) with hεdef
  have hε0 : 0 < ε := Real.exp_pos _
  have hε1 : ε < 1 := by
    rw [hεdef, Real.exp_lt_one_iff]
    linarith
  have hlog : Real.log ε = -(α * T) := by
    rw [hεdef, Real.log_exp]
  have hlog2 : Real.log (1 / ε) = α * T := by
    rw [one_div, Real.log_inv, hlog]
    ring
  have hTle : T ≤ Real.log (1 / ε) / α := by
    rw [hlog2, mul_div_cancel_left₀ T (ne_of_gt hα0)]
  have hcop : ε ^ (α - 1) ≤ (A.copies T : ℝ) :=
    h11 ε hε0 hε1 A T hT hTle (le_trans herr (le_of_lt hε0))
  have hpow : ε ^ (α - 1) = Real.exp (α * (1 - α) * T) := by
    rw [Real.rpow_def_of_pos hε0, hlog]
    congr 1
    ring
  calc (1 : ℝ) * Real.exp (α * (1 - α) * T) = ε ^ (α - 1) := by
        rw [hpow]
        ring
    _ ≤ (A.copies T : ℝ) := hcop

/-! ## c025 — Corollary 27, p. 33 -/

/-- **c025, Corollary 27, p. 33**: any quantum algorithm producing the history state of
the KdV equation requires `Ω(T)` copies of the initial state.

Proof (paper, p. 33): apply Theorem 15 (c013) for the final-time state and Theorem 26
(c024) to convert the final-state bound `T²` into the history-state bound `T²/T = T`.
The post-selection step of Theorem 26 is the explicit hypothesis `hpost`.  This is fully
proved below from `theorem15_kdv_quadratic_lower_bound`'s lower-bound shape and
`theorem26_history_reduction` (the division by `T` uses `T ≥ 1`). -/
theorem corollary27_kdv_history_lower_bound
    (hpost : ∃ C : ℝ, 0 < C ∧ HistoryPostselection C)
    {err : ℝ → ℝ} (h15 : RequiresCopiesForError (fun T => T ^ 2) err) :
    HistoryRequiresCopiesForError (fun T => T) err := by
  obtain ⟨c, hc0, hc⟩ := h15
  obtain ⟨C, hC0, hpost⟩ := hpost
  refine ⟨c / C, div_pos hc0 hC0, ?_⟩
  intro H T hT herr
  obtain ⟨A, herrA, hcop⟩ := hpost H
  have hlow : c * T ^ 2 ≤ (A.copies T : ℝ) := hc A T hT (by rw [herrA]; exact herr)
  have hup : (A.copies T : ℝ) ≤ C * T * (H.copies T : ℝ) := hcop T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hCT : 0 < C * T := mul_pos hC0 hT0
  have hchain : c * T ^ 2 ≤ C * T * (H.copies T : ℝ) := le_trans hlow hup
  have hdiv : c * T ^ 2 / (C * T) ≤ (H.copies T : ℝ) := by
    rw [div_le_iff₀ hCT]
    linarith
  have heq : c / C * T = c * T ^ 2 / (C * T) := by
    field_simp
  rwa [heq]

end Qatlib.Papers.FluidDynamics26.MainResults
