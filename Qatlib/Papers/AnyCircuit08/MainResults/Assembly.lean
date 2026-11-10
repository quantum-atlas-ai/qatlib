/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AnyCircuit08.MainResults.Basic
import Qatlib.Papers.AnyCircuit08.MainResults.RandomAssembly

namespace Qatlib.Papers.AnyCircuit08.MainResults

set_option autoImplicit false

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem l1_ge_of_fourth_moment {X : Type} [Fintype X] (y : X → ℝ) (hy : ∀ x, 0 ≤ y x)
    {N β : ℝ} (hN : 0 < N) (hβ : 0 < β) (hunit : ∑ x, y x ^ 2 = 1)
    (hQ : ∑ x, y x ^ 4 ≤ 1 / (N * β ^ 2)) :
    β * Real.sqrt N ≤ ∑ x, y x := by
  have hmain := l1_ge_fourth_moment y hy
  rw [hunit] at hmain
  norm_num at hmain
  have hBnn : 0 ≤ ∑ x, y x := Finset.sum_nonneg (fun x _ => hy x)
  have hNβ : 0 < N * β ^ 2 := by positivity
  have hstep : (1 : ℝ) ≤ (∑ x, y x) ^ 2 * (1 / (N * β ^ 2)) := by
    calc (1 : ℝ) ≤ (∑ x, y x) ^ 2 * (∑ x, y x ^ 4) := hmain
      _ ≤ (∑ x, y x) ^ 2 * (1 / (N * β ^ 2)) :=
          mul_le_mul_of_nonneg_left hQ (sq_nonneg _)
  have h2 : N * β ^ 2 ≤ (∑ x, y x) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hstep (le_of_lt hNβ)
    have hsimp : (∑ x, y x) ^ 2 * (1 / (N * β ^ 2)) * (N * β ^ 2) = (∑ x, y x) ^ 2 := by
      field_simp
    calc N * β ^ 2 = 1 * (N * β ^ 2) := by ring
      _ ≤ ((∑ x, y x) ^ 2 * (1 / (N * β ^ 2))) * (N * β ^ 2) := hmul
      _ = (∑ x, y x) ^ 2 := hsimp
  calc β * Real.sqrt N = Real.sqrt N * β := by ring
    _ = Real.sqrt (N * β ^ 2) := by
        rw [Real.sqrt_mul hN.le, Real.sqrt_sq hβ.le]
    _ ≤ Real.sqrt ((∑ x, y x) ^ 2) := Real.sqrt_le_sqrt h2
    _ = ∑ x, y x := Real.sqrt_sq hBnn

theorem dispersing_of_row_bounds {X : Type} [Fintype X] [DecidableEq X]
    (U : X → X → ℂ) (A : Finset X) {α β : ℝ} (hβ : 0 < β)
    (hcard : (Fintype.card X : ℝ) ^ α ≤ (A.card : ℝ))
    (hN : 0 < (Fintype.card X : ℝ))
    (hunit : ∀ a ∈ A, ∑ x, ‖U a x‖ ^ 2 = 1)
    (hQ : ∀ a ∈ A, ∑ x, ‖U a x‖ ^ 4 ≤ 1 / ((Fintype.card X : ℝ) * β ^ 2)) :
    IsDispersing U α β := by
  refine ⟨A, hcard, ?_⟩
  intro a ha
  exact l1_ge_of_fourth_moment (fun x => ‖U a x‖) (fun x => norm_nonneg _)
    hN hβ (hunit a ha) (hQ a ha)

theorem exists_good_set {X : Type} [Fintype X] [DecidableEq X]
    (bad : X → Bool) {r : ℝ}
    (h : ((Finset.univ.filter (fun x => bad x = true)).card : ℝ) <
      (Fintype.card X : ℝ) - r) :
    ∃ A : Finset X, r < (A.card : ℝ) ∧ ∀ a ∈ A, bad a = false := by
  refine ⟨Finset.univ.filter (fun x => bad x = false), ?_, ?_⟩
  · have hneg : (Finset.univ.filter (fun x => ¬ (bad x = false)))
        = Finset.univ.filter (fun x => bad x = true) := by
      apply Finset.filter_congr
      intro x _
      cases bad x <;> simp
    have hsplit : (Finset.univ.filter (fun x => bad x = false)).card
        + (Finset.univ.filter (fun x => bad x = true)).card = Fintype.card X := by
      have hcard := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset X)) (p := fun x => bad x = false)
      rw [hneg, Finset.card_univ] at hcard
      exact hcard
    have hle : (Finset.univ.filter (fun x => bad x = true)).card ≤ Fintype.card X := by
      omega
    have hgoal : (Finset.univ.filter (fun x => bad x = false)).card
        = Fintype.card X - (Finset.univ.filter (fun x => bad x = true)).card := by
      omega
    have hcast : ((Fintype.card X -
          (Finset.univ.filter (fun x => bad x = true)).card : ℕ) : ℝ)
        = (Fintype.card X : ℝ) -
          ((Finset.univ.filter (fun x => bad x = true)).card : ℝ) := by
      rw [Nat.cast_sub hle]
    rw [hgoal, hcast]
    linarith
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

theorem fraction_lt_of_bad_fraction_le {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) {p s : ℝ}
    (hΩ : 0 < Fintype.card Ω)
    (h : (∑ ω, if s ≤ f ω then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) ≤ p / s) :
    1 - p / s ≤ (∑ ω, if f ω < s then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) := by
  have hpt : ∀ ω, (if s ≤ f ω then (1 : ℝ) else 0) + (if f ω < s then (1 : ℝ) else 0)
      = 1 := by
    intro ω
    by_cases hle : s ≤ f ω
    · rw [if_pos hle, if_neg (not_lt.mpr hle)]; ring
    · rw [if_neg hle, if_pos (not_le.mp hle)]; ring
  have hsum : (∑ ω, if s ≤ f ω then (1 : ℝ) else 0)
      + (∑ ω, if f ω < s then (1 : ℝ) else 0) = (Fintype.card Ω : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp only [hpt]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hΩ
  have hX : (∑ ω, if f ω < s then (1 : ℝ) else 0)
      = (Fintype.card Ω : ℝ) - (∑ ω, if s ≤ f ω then (1 : ℝ) else 0) := by
    linarith
  rw [hX, sub_div, div_self (ne_of_gt hcpos)]
  linarith

theorem fraction_dispersing_ge {Ω : Type*} {X : Type} [Fintype Ω] [Fintype X] [DecidableEq X]
    (U : Ω → X → X → ℂ) (bad : Ω → X → Bool) {p s α β : ℝ}
    (hβ : 0 < β) (hX1 : 1 ≤ Fintype.card X) (hs : 0 < s)
    (hsize : (Fintype.card X : ℝ) - s * (Fintype.card X : ℝ) ≥
      (Fintype.card X : ℝ) ^ α)
    (hp : ∀ a, (∑ ω, if bad ω a then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) ≤ p)
    (hΩ : 0 < Fintype.card Ω)
    (hunit : ∀ ω a, bad ω a = false → ∑ x, ‖U ω a x‖ ^ 2 = 1)
    (hQ : ∀ ω a, bad ω a = false →
      ∑ x, ‖U ω a x‖ ^ 4 ≤ 1 / ((Fintype.card X : ℝ) * β ^ 2)) :
    1 - p / s ≤ (∑ ω, if IsDispersing (U ω) α β then (1 : ℝ) else 0) /
      (Fintype.card Ω : ℝ) := by
  set f : Ω → ℝ := fun ω => (∑ a, if bad ω a then (1 : ℝ) else 0) /
    (Fintype.card X : ℝ) with hfdef
  have hXpos : 0 < Fintype.card X := Nat.lt_of_lt_of_le Nat.zero_lt_one hX1
  have hcardpos : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hXpos
  have hfrac : (∑ ω, if s ≤ f ω then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) ≤ p / s := by
    simpa [hfdef] using bad_circuit_fraction (Ω := Ω) (A := X) bad hp hs hXpos hΩ
  have hcomp := fraction_lt_of_bad_fraction_le f hΩ hfrac

  have hpt : ∀ ω, (if f ω < s then (1 : ℝ) else 0)
      ≤ (if IsDispersing (U ω) α β then (1 : ℝ) else 0) := by
    intro ω
    by_cases hf : f ω < s
    · rw [if_pos hf]
      have hdis : IsDispersing (U ω) α β := by
        have hbadeq : ((Finset.univ.filter (fun a => bad ω a = true)).card : ℝ)
            = ∑ a, if bad ω a then (1 : ℝ) else 0 := by
          rw [← Finset.natCast_card_filter (s := (Finset.univ : Finset X))
            (p := fun a => bad ω a = true)]
        have hlt : ((Finset.univ.filter (fun a => bad ω a = true)).card : ℝ)
            < s * (Fintype.card X : ℝ) := by
          have hmul := mul_lt_mul_of_pos_right hf hcardpos
          rw [div_mul_cancel₀ _ (ne_of_gt hcardpos)] at hmul
          rw [← hbadeq] at hmul
          exact hmul
        obtain ⟨A, hAcard, hAfalse⟩ :=
          exists_good_set (bad ω) (r := (Fintype.card X : ℝ) ^ α) (by linarith)
        exact dispersing_of_row_bounds (U ω) A hβ (le_of_lt hAcard) hcardpos
          (fun a ha => hunit ω a (hAfalse a ha))
          (fun a ha => hQ ω a (hAfalse a ha))
      rw [if_pos hdis]
    · rw [if_neg hf]
      split_ifs <;> norm_num
  have hsum_le : (∑ ω, if f ω < s then (1 : ℝ) else 0)
      ≤ ∑ ω, if IsDispersing (U ω) α β then (1 : ℝ) else 0 :=
    Finset.sum_le_sum (fun ω _ => hpt ω)
  have hc : (0 : ℝ) ≤ (Fintype.card Ω : ℝ) := by positivity
  calc 1 - p / s ≤ (∑ ω, if f ω < s then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) := hcomp
    _ ≤ (∑ ω, if IsDispersing (U ω) α β then (1 : ℝ) else 0) /
        (Fintype.card Ω : ℝ) := div_le_div_of_nonneg_right hsum_le hc

end Qatlib.Papers.AnyCircuit08.MainResults
