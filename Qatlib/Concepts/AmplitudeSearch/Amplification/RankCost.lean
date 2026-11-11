/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.Lemma1RankProcessSubgoalAqua
import Mathlib.Data.Real.Basic

/-!
# Expected costs of decreasing rank traces

This module extends finite uniform experiments with real-valued expectation and defines
`traceCost` and `expectedTraceCost` for the decreasing rank process. The recurrence and
visit-probability formulas express expected cost as a sum of rank costs weighted by reciprocal
ranks, supporting the minimum-finding analysis [DurrHoyer1996].

## Main statements

* `expectedTraceCost_step`: computes the cost increment when the initial rank bound increases.
* `expectedTraceCost_sum`: expresses expected cost as the sum of `cost r / r`.
* `expectedTraceCost_visits`: expresses the same cost using rank visit probabilities.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

namespace Experiment

variable {α β : Type}

/-- The real-valued expectation of a finite experiment, computed by evaluation at a pure outcome
and averaging over uniform branches. -/
noncomputable def expectReal : Experiment α → (α → ℝ) → ℝ
  | .pure a, f => f a
  | .uniform n branches, f => (∑ k, expectReal (branches k) f) / (n + 1 : ℝ)

/-- Taking real-valued expectation after mapping outcomes is equivalent to composing the
observable with the map. -/
@[simp] theorem expectReal_map (e : Experiment α) (g : α → β) (f : β → ℝ) :
    (e.map g).expectReal f = e.expectReal (fun a => f (g a)) := by
  induction e with
  | pure a => rfl
  | uniform n branches ih => simp only [map, expectReal, ih]

/-- The real-valued expectation of a constant observable is that constant. -/
@[simp] theorem expectReal_const (e : Experiment α) (c : ℝ) :
    e.expectReal (fun _ => c) = c := by
  induction e with
  | pure a => rfl
  | uniform n branches ih =>
    simp only [expectReal, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-- Real-valued expectation preserves the sum of two observables. -/
theorem expectReal_add (e : Experiment α) (f g : α → ℝ) :
    e.expectReal (fun a => f a + g a) = e.expectReal f + e.expectReal g := by
  induction e with
  | pure a => rfl
  | uniform n branches ih => simp only [expectReal, ih, Finset.sum_add_distrib, add_div]

/-- Observables agreeing at every outcome of an experiment have equal real-valued expectations. -/
theorem expectReal_congr (e : Experiment α) {f g : α → ℝ}
    (h : e.All (fun a => f a = g a)) : e.expectReal f = e.expectReal g := by
  induction e with
  | pure a => exact h
  | uniform n branches ih =>
    unfold expectReal
    congr 1
    exact Finset.sum_congr rfl (fun k _ => ih k (h k))

/-- An inequality holding at every outcome of an experiment is preserved by real-valued
expectation. -/
theorem expectReal_mono (e : Experiment α) {f g : α → ℝ}
    (h : e.All (fun a => f a ≤ g a)) : e.expectReal f ≤ e.expectReal g := by
  induction e with
  | pure a => exact h
  | uniform n branches ih =>
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun k _ => ih k (h k))) (by positivity)

/-- Real-valued expectation of a rational observable equals its rational expectation coerced to
a real number. -/
theorem expectReal_rat (e : Experiment α) (f : α → ℚ) :
    e.expectReal (fun a => (f a : ℝ)) = (e.expect f : ℝ) := by
  induction e with
  | pure a => rfl
  | uniform n branches ih => simp [expectReal, expect, ih]

end Experiment

/-- The sum of the supplied rank costs over the entries of a rank trace. -/
noncomputable def traceCost (cost : ℕ → ℝ) (trace : List ℕ) : ℝ :=
  (trace.map cost).sum

/-- The real-valued expected total cost of `rankExperiment t`. -/
noncomputable def expectedTraceCost (cost : ℕ → ℝ) (t : ℕ) : ℝ :=
  (rankExperiment t).expectReal (traceCost cost)

/-- The expected trace cost is zero when the initial rank bound is zero. -/
@[simp] theorem expectedTraceCost_zero (cost : ℕ → ℝ) : expectedTraceCost cost 0 = 0 := by
  simp [expectedTraceCost, rankExperiment, Experiment.expectReal, traceCost]

/-- The expected cost from bound `t + 1` is the uniform average of the first rank cost and the
expected continuation cost. -/
theorem expectedTraceCost_succ (cost : ℕ → ℝ) (t : ℕ) :
    expectedTraceCost cost (t + 1) =
      (∑ k : Fin (t + 1), (cost (k.val + 1) + expectedTraceCost cost k.val)) /
        (t + 1 : ℝ) := by
  simp only [expectedTraceCost, rankExperiment, Experiment.expectReal,
    Experiment.expectReal_map, traceCost, List.map_cons, List.sum_cons]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Experiment.expectReal_add, Experiment.expectReal_const]
  rfl

/-- Multiplying expected trace cost by the rank bound gives the finite sum of first-step costs
and continuation costs. -/
private theorem weighted_expectedTraceCost (cost : ℕ → ℝ) (t : ℕ) :
    (t : ℝ) * expectedTraceCost cost t =
      ∑ k : Fin t, (cost (k.val + 1) + expectedTraceCost cost k.val) := by
  cases t with
  | zero => simp
  | succ t =>
    rw [expectedTraceCost_succ]
    have hn : (t + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp

/-- Increasing the initial rank bound from `t` to `t + 1` adds `cost (t + 1) / (t + 1)` to the
expected cost. -/
theorem expectedTraceCost_step (cost : ℕ → ℝ) (t : ℕ) :
    expectedTraceCost cost (t + 1) =
      expectedTraceCost cost t + cost (t + 1) / (t + 1 : ℝ) := by
  have h := weighted_expectedTraceCost cost (t + 1)
  rw [Fin.sum_univ_castSucc] at h
  simp only [Nat.cast_add, Nat.cast_one, Fin.val_castSucc, Fin.val_last,
    ← weighted_expectedTraceCost] at h
  have hn : (t + 1 : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  rw [h]
  field_simp
  ring

/-- The expected cost from bound `N` equals the sum of `cost r / r` for ranks from one through
`N`. -/
theorem expectedTraceCost_sum (cost : ℕ → ℝ) (N : ℕ) :
    expectedTraceCost cost N = ∑ k ∈ Finset.range N, cost (k + 1) / (k + 1 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih => rw [expectedTraceCost_step, ih, Finset.sum_range_succ]

/-- The expected trace cost equals the sum of each rank cost multiplied by its visit
probability. -/
theorem expectedTraceCost_visits (cost : ℕ → ℝ) (N : ℕ) :
    expectedTraceCost cost N =
      ∑ k ∈ Finset.range N, (hitProbability N (k + 1) : ℝ) * cost (k + 1) := by
  rw [expectedTraceCost_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hitProbability_eq_inv N (k + 1) (by omega) (Finset.mem_range.mp hk)]
  push_cast
  ring

/-- Nonnegative rank costs give a nonnegative expected trace cost. -/
theorem expectedTraceCost_nonneg (cost : ℕ → ℝ) (N : ℕ)
    (hc : ∀ r, 0 ≤ cost r) : 0 ≤ expectedTraceCost cost N := by
  rw [expectedTraceCost_sum]
  exact Finset.sum_nonneg (fun k _ => div_nonneg (hc _) (by positivity))

end Qatlib.Concepts.AmplitudeSearch.Amplification
