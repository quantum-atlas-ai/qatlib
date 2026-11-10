/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WeightEnum07.MainResults.Proposition1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeightEnum07.TraceWeights

open scoped BigOperators

theorem card_weight_eq_sum_rep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rep : ι → ι) (hidem : ∀ x, rep (rep x) = rep x) (W : ι → ℕ)
    (hinv : ∀ x, W x = W (rep x)) (w : ℕ) :
    (Finset.univ.filter (fun x => W x = w)).card =
      ∑ b ∈ Finset.univ.filter (fun b => rep b = b ∧ W b = w),
        (Finset.univ.filter (fun x => rep x = b)).card := by
  classical
  set T : Finset ι := Finset.univ.filter (fun b => rep b = b) with hT
  have hmap : ((Finset.univ.filter (fun x => W x = w) : Finset ι) : Set ι).MapsTo rep T := by
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hT] at hx ⊢
    exact hidem x
  rw [Finset.card_eq_sum_card_fiberwise hmap]

  have hzero : ∀ b ∈ T, W b ≠ w →
      ((Finset.univ.filter (fun x => W x = w)).filter (fun x => rep x = b)).card = 0 := by
    intro b _ hbw
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro x hx hrep
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hbw (by rw [← hrep, ← hinv x]; exact hx)
  have hstep : ∑ b ∈ T,
        ((Finset.univ.filter (fun x => W x = w)).filter (fun x => rep x = b)).card
      = ∑ b ∈ T.filter (fun b => W b = w),
          ((Finset.univ.filter (fun x => W x = w)).filter (fun x => rep x = b)).card := by
    calc ∑ b ∈ T,
          ((Finset.univ.filter (fun x => W x = w)).filter (fun x => rep x = b)).card
        = ∑ b ∈ T,
            (if W b = w then
              ((Finset.univ.filter (fun x => W x = w)).filter (fun x => rep x = b)).card
             else 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases h : W b = w
          · simp [h]
          · simp [h, hzero b hb h]
      _ = ∑ b ∈ T.filter (fun b => W b = w),
            ((Finset.univ.filter (fun x => W x = w)).filter (fun x => rep x = b)).card :=
          (Finset.sum_filter (s := T) (p := fun b => W b = w)
            (f := fun b => ((Finset.univ.filter (fun x => W x = w)).filter
              (fun x => rep x = b)).card)).symm
  calc ∑ b ∈ T,
        ((Finset.univ.filter (fun x => W x = w)).filter (fun x => rep x = b)).card
      = ∑ b ∈ T.filter (fun b => W b = w),
          ((Finset.univ.filter (fun x => W x = w)).filter (fun x => rep x = b)).card := hstep
    _ = ∑ b ∈ Finset.univ.filter (fun b => rep b = b ∧ W b = w),
          (Finset.univ.filter (fun x => rep x = b)).card := by
        rw [hT, Finset.filter_filter]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        obtain ⟨-, hbw⟩ := hb
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨-, hrep⟩
          exact hrep
        · intro hrep
          exact ⟨by rw [hinv x, hrep]; exact hbw, hrep⟩

theorem card_weight_eq_n_mul_reps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (rep : ι → ι) (hidem : ∀ x, rep (rep x) = rep x) (W : ι → ℕ)
    (hinv : ∀ x, W x = W (rep x))
    (hsize : ∀ b, rep b = b → (Finset.univ.filter (fun x => rep x = b)).card = n) (w : ℕ) :
    (Finset.univ.filter (fun x => W x = w)).card =
      n * (Finset.univ.filter (fun b => rep b = b ∧ W b = w)).card := by
  classical
  rw [card_weight_eq_sum_rep rep hidem W hinv w]
  rw [Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  rw [hsize b hb.1]
  simp

end Qatlib.Papers.WeightEnum07.TraceWeights
