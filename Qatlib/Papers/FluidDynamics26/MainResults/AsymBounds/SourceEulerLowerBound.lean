/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FluidDynamics26.MainResults.SourceModel
import Qatlib.Papers.FluidDynamics26.MainResults.AsymBounds.SourceHistoryReduction

set_option backward.isDefEq.respectTransparency false

/-!
# FluidDynamics26 — history-state lower bounds for the Euler equations

Fixed source: Ameri–Carolan–Childs–Krovi, *Quantum lower bounds for simulating fluid
dynamics*, arXiv:2603.12161v1 (12 March 2026).

Claims formalised here:

* c026 = Corollary 28, p. 33 — history state, tensor-product encoding, `e^{Ω(T)}` copies;
* c027 = Corollary 29, p. 33 — history state, direct-sum encoding, `e^{Ω(T)}` copies.

Both are the Theorem 26 reduction applied to a final-state exponential bound of
Theorem 24/25 shape: `history_reduction_exp_over_T` converts `e^{cT}` into `e^{cT}/T`,
and the elementary domination `T·a·e ≤ e^{aT}` (`exp_dominate_linear`, from
`Real.log_le_sub_one_of_pos`) converts `e^{cT}/T` into `e^{cT/2}`.  The final-state
input `h24`/`h25` and the post-selection step `hpost` are the explicit hypotheses; the
unformalized inputs are Theorem 17 (linear separation) and the norm barrier of
Lemmas 19–23 (c015, c017–c021).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FluidDynamics26.MainResults

open MeasureTheory Filter

open scoped BigOperators Topology

/-! ## Theorem 26 reduction for exponential lower bounds (support for c026/c027) -/

/-- Support lemma for c026/c027: Theorem 26 (c024) applied to an exponential final-state
bound converts `e^{cT}` into `e^{cT}/T`, preserving the accuracy promise.  This is the
provable part of Corollaries 28–29; the remaining step is `T ≤ e^{Ω(T)}`. -/
theorem history_reduction_exp_over_T
    {c : ℝ} {err : ℝ → ℝ}
    (hpost : ∃ C : ℝ, 0 < C ∧ HistoryPostselection C)
    (h24 : RequiresCopiesForError (fun T => Real.exp (c * T)) err) :
    HistoryRequiresCopiesForError (fun T => Real.exp (c * T) / T) err :=
  theorem26_history_reduction (fun T _ => (Real.exp_pos (c * T)).le) h24 hpost

/-- Support lemma for c026/c027: the elementary domination `T · a · e ≤ e^{aT}` for
`a > 0`, `0 ≤ T`.  From `Real.log_le_sub_one_of_pos` at `x = aT`: `log x ≤ x - 1`
exponentiates to `x ≤ e^{x-1} = e^x / e`.  This is the paper's `T ≤ e^{Ω(T)}` step. -/
theorem exp_dominate_linear {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    T * a * Real.exp 1 ≤ Real.exp (a * T) := by
  rcases eq_or_lt_of_le hT with rfl | hT0
  · simp
  have hx : 0 < a * T := mul_pos ha hT0
  have hlog : Real.log (a * T) ≤ a * T - 1 := Real.log_le_sub_one_of_pos hx
  have hexp : a * T ≤ Real.exp (a * T - 1) := by
    have hle := Real.exp_le_exp.2 hlog
    rwa [Real.exp_log hx] at hle
  rw [Real.exp_sub] at hexp
  have hkey : a * T * Real.exp 1 ≤ Real.exp (a * T) :=
    (le_div_iff₀ (Real.exp_pos 1)).1 hexp
  calc T * a * Real.exp 1 = a * T * Real.exp 1 := by ring
    _ ≤ Real.exp (a * T) := hkey

/-! ## Shared reduction for c026/c027 -/

/-- Support lemma for c026/c027: a final-state exponential bound of Theorem 24/25 shape
(the hypothesis `hfin`, with growth rate `cerr` and accuracy `e^{-Cerr·T}`) plus the
post-selection step `hpost` of Theorem 26 yield an `e^{Ω(T)}` history-state bound.

The witness is `c = min (cerr/2) (c₀·(cerr/2)·e)`: the first half of the `min` bounds the
exponent (`e^{cT} ≤ e^{(cerr/2)T}`), the second half bounds the constant through the
domination `T·(cerr/2)·e ≤ e^{(cerr/2)T}` of `exp_dominate_linear`, so
`c·e^{cT} ≤ c₀·e^{cerr·T}/T`. -/
theorem history_exp_bound_from_final
    {Cerr cerr : ℝ} (hC : 0 < Cerr) (hc : 0 < cerr)
    (hpost : ∃ C : ℝ, 0 < C ∧ HistoryPostselection C)
    (hfin : RequiresCopiesForError (fun T => Real.exp (cerr * T))
      (fun T => Real.exp (-(Cerr * T)))) :
    ∃ c : ℝ, 0 < c ∧
      HistoryRequiresCopiesForError (fun T => Real.exp (c * T))
        (fun T => Real.exp (-(Cerr * T))) := by
  obtain ⟨c₀, hc₀pos, hbound⟩ := history_reduction_exp_over_T hpost hfin
  obtain ⟨a, ha, hc2⟩ : ∃ a : ℝ, 0 < a ∧ cerr = 2 * a :=
    ⟨cerr / 2, by linarith, by ring⟩
  obtain ⟨c, hcpos, hca, hcc₀⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ a ∧ c ≤ c₀ * a * Real.exp 1 :=
    ⟨min a (c₀ * a * Real.exp 1),
      lt_min_iff.mpr ⟨ha, mul_pos (mul_pos hc₀pos ha) (Real.exp_pos 1)⟩,
      min_le_left _ _, min_le_right _ _⟩
  refine ⟨c, hcpos, ?_⟩
  refine ⟨c, hcpos, ?_⟩
  intro H T hT herr
  have hT0 : (0 : ℝ) < T := by linarith
  have hdom := exp_dominate_linear ha hT0.le
  have hboundT := hbound H T hT herr
  have hexp_le : Real.exp (c * T) ≤ Real.exp (a * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hca hT0.le)
  have hkey : c * T ≤ c₀ * Real.exp (a * T) := by
    calc c * T ≤ c₀ * a * Real.exp 1 * T := mul_le_mul_of_nonneg_right hcc₀ hT0.le
      _ = c₀ * (T * a * Real.exp 1) := by ring
      _ ≤ c₀ * Real.exp (a * T) := mul_le_mul_of_nonneg_left hdom hc₀pos.le
  have hsplit : Real.exp (cerr * T) = Real.exp (a * T) * Real.exp (a * T) := by
    rw [hc2]
    have h2 : 2 * a * T = a * T + a * T := by ring
    rw [h2, Real.exp_add]
  calc c * Real.exp (c * T) ≤ c₀ * (Real.exp (cerr * T) / T) := by
        rw [← mul_div_assoc, le_div_iff₀ hT0]
        have hAB : c * T * Real.exp (c * T) ≤ c * T * Real.exp (a * T) :=
          mul_le_mul_of_nonneg_left hexp_le (mul_nonneg hcpos.le hT0.le)
        have hB : c * T * Real.exp (a * T) ≤ c₀ * Real.exp (a * T) * Real.exp (a * T) :=
          mul_le_mul_of_nonneg_right hkey (Real.exp_pos (a * T)).le
        rw [hsplit]
        calc c * Real.exp (c * T) * T = c * T * Real.exp (c * T) := by ring
          _ ≤ c * T * Real.exp (a * T) := hAB
          _ ≤ c₀ * Real.exp (a * T) * Real.exp (a * T) := hB
          _ = c₀ * (Real.exp (a * T) * Real.exp (a * T)) := by ring
    _ ≤ (H.copies T : ℝ) := hboundT

/-! ## c026 — Corollary 28, p. 33 -/

/-- **c026, Corollary 28, p. 33**: any quantum algorithm producing the history state of
the Euler equations, as encoded in Problem 2 (tensor-product encoding), requires
`e^{Ω(T)}` copies of the initial state.

Fully proved reduction: `history_exp_bound_from_final` applies Theorem 26
(`theorem26_history_reduction`) to the final-state bound `h24` — an explicit hypothesis
carrying Theorem 24 (c022), which is itself not formalized — and converts `e^{cerr·T}/T`
into `e^{Ω(T)}` via `exp_dominate_linear`. -/
theorem corollary28_euler_history_exponential_tensor
    (hpost : ∃ C : ℝ, 0 < C ∧ HistoryPostselection C)
    {Cerr cerr : ℝ} (hC : 0 < Cerr) (hc : 0 < cerr)
    (h24 : RequiresCopiesForError (fun T => Real.exp (cerr * T))
      (fun T => Real.exp (-(Cerr * T)))) :
    ∃ c : ℝ, 0 < c ∧
      HistoryRequiresCopiesForError (fun T => Real.exp (c * T))
        (fun T => Real.exp (-(Cerr * T))) :=
  history_exp_bound_from_final hC hc hpost h24

/-! ## c027 — Corollary 29, p. 33 -/

/-- **c027, Corollary 29, p. 33**: any quantum algorithm producing the history state of
the Euler equations, as encoded in Problem 3 (direct-sum encoding), requires `e^{Ω(T)}`
copies of the initial state.

Fully proved reduction, identical to Corollary 28 (c026): the two encodings differ only
in the time-step bookkeeping, not in the copy count, so the same reduction applies to
`h25` (Theorem 25 shape, c023, not formalized). -/
theorem corollary29_euler_history_exponential_directsum
    (hpost : ∃ C : ℝ, 0 < C ∧ HistoryPostselection C)
    {Cerr cerr : ℝ} (hC : 0 < Cerr) (hc : 0 < cerr)
    (h25 : RequiresCopiesForError (fun T => Real.exp (cerr * T))
      (fun T => Real.exp (-(Cerr * T)))) :
    ∃ c : ℝ, 0 < c ∧
      HistoryRequiresCopiesForError (fun T => Real.exp (c * T))
        (fun T => Real.exp (-(Cerr * T))) :=
  history_exp_bound_from_final hC hc hpost h25

end Qatlib.Papers.FluidDynamics26.MainResults
