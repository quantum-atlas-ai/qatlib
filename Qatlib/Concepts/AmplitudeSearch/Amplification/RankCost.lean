/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.Lemma1RankProcessSubgoalAqua
import Mathlib.Data.Real.Basic

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

namespace Experiment

variable {α β : Type}

noncomputable def expectReal : Experiment α → (α → ℝ) → ℝ
  | .pure a, f => f a
  | .uniform n branches, f => (∑ k, expectReal (branches k) f) / (n + 1 : ℝ)

@[simp] theorem expectReal_map (e : Experiment α) (g : α → β) (f : β → ℝ) :
    (e.map g).expectReal f = e.expectReal (fun a => f (g a)) := by
  induction e with
  | pure a => rfl
  | uniform n branches ih => simp only [map, expectReal, ih]

@[simp] theorem expectReal_const (e : Experiment α) (c : ℝ) :
    e.expectReal (fun _ => c) = c := by
  induction e with
  | pure a => rfl
  | uniform n branches ih =>
    simp only [expectReal, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp

theorem expectReal_add (e : Experiment α) (f g : α → ℝ) :
    e.expectReal (fun a => f a + g a) = e.expectReal f + e.expectReal g := by
  induction e with
  | pure a => rfl
  | uniform n branches ih => simp only [expectReal, ih, Finset.sum_add_distrib, add_div]

theorem expectReal_congr (e : Experiment α) {f g : α → ℝ}
    (h : e.All (fun a => f a = g a)) : e.expectReal f = e.expectReal g := by
  induction e with
  | pure a => exact h
  | uniform n branches ih =>
    unfold expectReal
    congr 1
    exact Finset.sum_congr rfl (fun k _ => ih k (h k))

theorem expectReal_mono (e : Experiment α) {f g : α → ℝ}
    (h : e.All (fun a => f a ≤ g a)) : e.expectReal f ≤ e.expectReal g := by
  induction e with
  | pure a => exact h
  | uniform n branches ih =>
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun k _ => ih k (h k))) (by positivity)

theorem expectReal_rat (e : Experiment α) (f : α → ℚ) :
    e.expectReal (fun a => (f a : ℝ)) = (e.expect f : ℝ) := by
  induction e with
  | pure a => rfl
  | uniform n branches ih => simp [expectReal, expect, ih]

end Experiment

noncomputable def traceCost (cost : ℕ → ℝ) (trace : List ℕ) : ℝ :=
  (trace.map cost).sum

noncomputable def expectedTraceCost (cost : ℕ → ℝ) (t : ℕ) : ℝ :=
  (rankExperiment t).expectReal (traceCost cost)

@[simp] theorem expectedTraceCost_zero (cost : ℕ → ℝ) : expectedTraceCost cost 0 = 0 := by
  simp [expectedTraceCost, rankExperiment, Experiment.expectReal, traceCost]

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

theorem expectedTraceCost_sum (cost : ℕ → ℝ) (N : ℕ) :
    expectedTraceCost cost N = ∑ k ∈ Finset.range N, cost (k + 1) / (k + 1 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih => rw [expectedTraceCost_step, ih, Finset.sum_range_succ]

theorem expectedTraceCost_visits (cost : ℕ → ℝ) (N : ℕ) :
    expectedTraceCost cost N =
      ∑ k ∈ Finset.range N, (hitProbability N (k + 1) : ℝ) * cost (k + 1) := by
  rw [expectedTraceCost_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hitProbability_eq_inv N (k + 1) (by omega) (Finset.mem_range.mp hk)]
  push_cast
  ring

theorem expectedTraceCost_nonneg (cost : ℕ → ℝ) (N : ℕ)
    (hc : ∀ r, 0 ≤ cost r) : 0 ≤ expectedTraceCost cost N := by
  rw [expectedTraceCost_sum]
  exact Finset.sum_nonneg (fun k _ => div_nonneg (hc _) (by positivity))

end Qatlib.Concepts.AmplitudeSearch.Amplification
