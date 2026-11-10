/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

open Finset
set_option autoImplicit false

namespace Qatlib.Papers.ArxivCs0506068.MarkovAmp

noncomputable section

variable {n : ℕ}

theorem sum_filter_gt_third_ge (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ((univ.filter (fun i => 1 / 3 < f i)).card : ℝ) * (1 / 3) ≤ ∑ i, f i := by
  have h₁ : ∑ i ∈ univ.filter (fun i => 1 / 3 < f i), (1 / 3 : ℝ) ≤
      ∑ i ∈ univ.filter (fun i => 1 / 3 < f i), f i := by
    apply Finset.sum_le_sum
    intro i hi
    exact (Finset.mem_filter.mp hi).2.le
  have h₂ : ∑ i ∈ univ.filter (fun i => 1 / 3 < f i), f i ≤ ∑ i, f i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    exact hf i
  calc ((univ.filter (fun i => 1 / 3 < f i)).card : ℝ) * (1 / 3)
      = ∑ i ∈ univ.filter (fun i => 1 / 3 < f i), (1 / 3 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ univ.filter (fun i => 1 / 3 < f i), f i := h₁
    _ ≤ ∑ i, f i := h₂

theorem card_gt_third_le (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i)
    (havg : (∑ i, f i) ≤ (n : ℝ) * (1 / 9)) :
    ((univ.filter (fun i => 1 / 3 < f i)).card : ℝ) ≤ (n : ℝ) / 3 := by
  have h := sum_filter_gt_third_ge f hf
  have hc : ((univ.filter (fun i => 1 / 3 < f i)).card : ℝ) * (1 / 3) ≤
      (n : ℝ) * (1 / 9) := le_trans h havg
  nlinarith [hc]

theorem card_le_third_ge_two_thirds (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i)
    (havg : (∑ i, f i) ≤ (n : ℝ) * (1 / 9)) :
    (2 * (n : ℝ) / 3) ≤ ((univ.filter (fun i => f i ≤ 1 / 3)).card : ℝ) := by
  let s := univ.filter (fun i => 1 / 3 < f i)
  let t := univ.filter (fun i => f i ≤ 1 / 3)
  have hst : s.card + t.card = n := by
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n))) (p := fun i => 1 / 3 < f i)
    simpa [s, t] using this
  have hs := card_gt_third_le f hf havg
  have hcast : (s.card : ℝ) + (t.card : ℝ) = (n : ℝ) := by
    exact_mod_cast hst
  linarith

theorem qam_yes_amplification (mu : Fin n → ℝ) (_hmu : ∀ i, 0 ≤ mu i)
    (hmu1 : ∀ i, mu i ≤ 1) (havg : (∑ i, (1 - mu i)) ≤ (n : ℝ) * (1 / 9)) :
    (2 * (n : ℝ) / 3) ≤ ((univ.filter (fun i => 2 / 3 ≤ mu i)).card : ℝ) := by
  have hf : ∀ i, 0 ≤ 1 - mu i := fun i => by linarith [hmu1 i]
  have key : (2 * (n : ℝ) / 3) ≤
      ((univ.filter (fun i => (fun j => 1 - mu j) i ≤ 1 / 3)).card : ℝ) :=
    card_le_third_ge_two_thirds (fun j => 1 - mu j) hf havg
  refine le_trans key (le_of_eq ?_)
  congr 2
  apply Finset.filter_congr
  intro i _
  constructor <;> intro h <;> linarith

theorem qam_no_amplification (mu : Fin n → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (havg : (∑ i, mu i) ≤ (n : ℝ) * (1 / 9)) :
    (2 * (n : ℝ) / 3) ≤ ((univ.filter (fun i => mu i ≤ 1 / 3)).card : ℝ) :=
  card_le_third_ge_two_thirds mu hmu havg

end

end Qatlib.Papers.ArxivCs0506068.MarkovAmp
