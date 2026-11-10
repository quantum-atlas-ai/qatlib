/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.MinMaxTree07.NoisyPivot

theorem shrink_of_middle_pivot {m k : ℕ} (hlo : m ≤ 4 * k) (hhi : 4 * k ≤ 3 * m) :
    4 * max k (m - k) ≤ 3 * m := by
  have hkm : k ≤ 3 * m / 4 := by omega
  have hmk : m - k ≤ 3 * m / 4 := by omega
  omega

theorem pivot_middle_half (m : ℕ) (hm : 1 ≤ m) :
    m / 2 ≤ ((Finset.Icc 1 m).filter (fun k => m ≤ 4 * k ∧ 4 * k ≤ 3 * m)).card := by
  have hset : (Finset.Icc 1 m).filter (fun k => m ≤ 4 * k ∧ 4 * k ≤ 3 * m)
      = Finset.Icc ((m - 1) / 4 + 1) (3 * m / 4) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hset, Nat.card_Icc]
  omega

section IteratedShrink

def pivotStep (m k : ℕ) : ℕ := max k (m - k)

theorem pivotStep_le_shrink {m k : ℕ} (hlo : m ≤ 4 * k) (hhi : 4 * k ≤ 3 * m) :
    pivotStep m k ≤ 3 * m / 4 := by
  have h := shrink_of_middle_pivot hlo hhi
  simp only [pivotStep]
  omega

theorem shrink_half_pivots (m : ℕ) (hm : 1 ≤ m) :
    m / 2 ≤ ((Finset.Icc 1 m).filter (fun k => pivotStep m k ≤ 3 * m / 4)).card := by
  refine le_trans (pivot_middle_half m hm) (Finset.card_le_card ?_)
  intro k hk
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, pivotStep_le_shrink hk.2.1 hk.2.2⟩

def rangeAfter (m : ℕ) (k : ℕ → ℕ) : ℕ → ℕ
  | 0 => m
  | t + 1 => pivotStep (rangeAfter m k t) (k t)

theorem shrink_mono {a b : ℕ} (h : a ≤ b) : 3 * a / 4 ≤ 3 * b / 4 := by omega

theorem rangeAfter_le_shrink_iterate (m : ℕ) (k : ℕ → ℕ)
    (hk : ∀ t, rangeAfter m k t ≤ 4 * k t ∧ 4 * k t ≤ 3 * rangeAfter m k t) (t : ℕ) :
    rangeAfter m k t ≤ (fun x => 3 * x / 4)^[t] m := by
  induction t with
  | zero => simp [rangeAfter]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans (pivotStep_le_shrink (hk t).1 (hk t).2) (shrink_mono ih)

theorem shrink_iterate_cast_le (m t : ℕ) :
    (((fun x => 3 * x / 4)^[t] m : ℕ) : ℝ) ≤ ((3 : ℝ) / 4) ^ t * m := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have hcast : ((3 * ((fun x => 3 * x / 4)^[t] m) / 4 : ℕ) : ℝ)
        ≤ (3 / 4 : ℝ) * (((fun x => 3 * x / 4)^[t] m : ℕ) : ℝ) := by
      have h := Nat.cast_div_le (α := ℝ) (m := 3 * ((fun x => 3 * x / 4)^[t] m)) (n := 4)
      push_cast at h
      calc ((3 * ((fun x => 3 * x / 4)^[t] m) / 4 : ℕ) : ℝ)
          ≤ (3 : ℝ) * (((fun x => 3 * x / 4)^[t] m : ℕ) : ℝ) / 4 := h
        _ = (3 / 4 : ℝ) * (((fun x => 3 * x / 4)^[t] m : ℕ) : ℝ) := by ring
    calc (((fun x => 3 * x / 4) ((fun x => 3 * x / 4)^[t] m) : ℕ) : ℝ)
        = ((3 * ((fun x => 3 * x / 4)^[t] m) / 4 : ℕ) : ℝ) := rfl
      _ ≤ (3 / 4 : ℝ) * (((fun x => 3 * x / 4)^[t] m : ℕ) : ℝ) := hcast
      _ ≤ (3 / 4 : ℝ) * (((3 : ℝ) / 4) ^ t * m) := by
          have h0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
          exact mul_le_mul_of_nonneg_left ih h0
      _ = (3 / 4 : ℝ) ^ (t + 1) * m := by ring

theorem rangeAfter_eq_zero_of_small (m : ℕ) (k : ℕ → ℕ)
    (hk : ∀ t, rangeAfter m k t ≤ 4 * k t ∧ 4 * k t ≤ 3 * rangeAfter m k t)
    {t : ℕ} (hsmall : ((3 : ℝ) / 4) ^ t * m < 1) :
    rangeAfter m k t = 0 := by
  have h1 : rangeAfter m k t ≤ (fun x => 3 * x / 4)^[t] m := rangeAfter_le_shrink_iterate m k hk t
  have h2 : (((fun x => 3 * x / 4)^[t] m : ℕ) : ℝ) ≤ ((3 : ℝ) / 4) ^ t * m :=
    shrink_iterate_cast_le m t
  have h3 : (((fun x => 3 * x / 4)^[t] m : ℕ) : ℝ) < 1 := lt_of_le_of_lt h2 hsmall
  have h4 : (fun x => 3 * x / 4)^[t] m = 0 := by
    have : (fun x => 3 * x / 4)^[t] m < 1 := by exact_mod_cast h3
    omega
  omega

end IteratedShrink

theorem card_biUnion_le_sum {Ω : Type*} [DecidableEq Ω] (n : ℕ) (S : Fin n → Finset Ω) :
    (Finset.univ.biUnion S).card ≤ ∑ i, (S i).card := by
  simpa using Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n))) (t := S)

theorem amplified_success_two_thirds (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (hn : 0 < n) (S : Fin n → Finset Ω)
    (hS : ∀ i, 3 * n * (S i).card ≤ Fintype.card Ω) :
    2 * Fintype.card Ω ≤ 3 * (Finset.univ \ Finset.univ.biUnion S).card := by
  have hsum : 3 * (∑ i, (S i).card : ℕ) ≤ Fintype.card Ω := by
    have hmul : n * (3 * (∑ i, (S i).card : ℕ)) = ∑ i : Fin n, 3 * n * (S i).card := by
      rw [show n * (3 * (∑ i, (S i).card : ℕ)) = (3 * n) * ∑ i, (S i).card by ring]
      simp [Finset.mul_sum]
    have hright : ∑ _i : Fin n, (Fintype.card Ω : ℕ) = n * Fintype.card Ω := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hle : ∑ i : Fin n, 3 * n * (S i).card ≤ ∑ _i : Fin n, (Fintype.card Ω : ℕ) :=
      Finset.sum_le_sum (fun i _ => hS i)
    have h1 : n * (3 * (∑ i, (S i).card : ℕ)) ≤ n * Fintype.card Ω := by
      rw [hmul, ← hright]
      exact hle
    exact Nat.le_of_mul_le_mul_left h1 hn
  have hcard : (Finset.univ.biUnion S).card ≤ ∑ i, (S i).card := card_biUnion_le_sum n S
  have hunion : (Finset.univ.biUnion S).card ≤ Fintype.card Ω := le_trans hcard (by omega)
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  omega

theorem net_progress (n incorrect : ℕ) (h : 3 * incorrect ≤ n) :
    n / 3 ≤ n - 2 * incorrect := by
  omega

theorem card_ge_le_sum {Ω : Type*} [Fintype Ω] (w : Ω → ℕ) {k : ℕ} (_hk : 0 < k) :
    k * (Finset.univ.filter (fun ω => k ≤ w ω)).card ≤ ∑ ω, w ω := by
  have h₁ : (Finset.univ.filter (fun ω => k ≤ w ω)).sum (fun _ => k)
      ≤ (Finset.univ.filter (fun ω => k ≤ w ω)).sum w := by
    apply Finset.sum_le_sum
    intro ω hω
    exact (Finset.mem_filter.mp hω).2
  have h₂ : (Finset.univ.filter (fun ω => k ≤ w ω)).sum (fun _ => k)
      = k * (Finset.univ.filter (fun ω => k ≤ w ω)).card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have h₃ : (Finset.univ.filter (fun ω => k ≤ w ω)).sum w ≤ Finset.univ.sum w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)
  rw [h₂] at h₁
  exact le_trans h₁ h₃

theorem bad_count_mul_le {Ω : Type*} [Fintype Ω] (errs : Ω → ℕ) {E k : ℕ} (hk : 0 < k)
    (hE : ∑ ω, errs ω ≤ E) :
    (Finset.univ.filter (fun ω => k ≤ errs ω)).card * k ≤ E := by
  calc (Finset.univ.filter (fun ω => k ≤ errs ω)).card * k
      = k * (Finset.univ.filter (fun ω => k ≤ errs ω)).card := Nat.mul_comm _ _
    _ ≤ ∑ ω, errs ω := card_ge_le_sum errs hk
    _ ≤ E := hE

theorem success_two_thirds_of_error_total {Ω : Type*} [Fintype Ω] (errs : Ω → ℕ)
    {E k : ℕ} (hk : 0 < k) (hE : ∑ ω, errs ω ≤ E)
    (hbudget : 3 * E ≤ k * Fintype.card Ω) :
    2 * Fintype.card Ω ≤ 3 * (Finset.univ.filter (fun ω => errs ω < k)).card := by
  have hbad := bad_count_mul_le errs hk hE
  have h3 : 3 * (Finset.univ.filter (fun ω => k ≤ errs ω)).card * k ≤ 3 * E := by
    have h := Nat.mul_le_mul_left 3 hbad
    simpa only [Nat.mul_assoc] using h
  have hle : 3 * (Finset.univ.filter (fun ω => k ≤ errs ω)).card ≤ Fintype.card Ω := by
    apply Nat.le_of_mul_le_mul_right _ hk
    calc 3 * (Finset.univ.filter (fun ω => k ≤ errs ω)).card * k
        ≤ 3 * E := h3
      _ ≤ Fintype.card Ω * k := by
          simpa only [Nat.mul_comm k (Fintype.card Ω)] using hbudget
  have hpart : (Finset.univ.filter (fun ω => errs ω < k)).card
      + (Finset.univ.filter (fun ω => ¬ errs ω < k)).card = Fintype.card Ω := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hsame : (Finset.univ.filter (fun ω => ¬ errs ω < k)).card
      = (Finset.univ.filter (fun ω => k ≤ errs ω)).card := by
    have hf : Finset.univ.filter (fun ω => ¬ errs ω < k)
        = Finset.univ.filter (fun ω => k ≤ errs ω) := by
      apply Finset.filter_congr
      intro ω _
      omega
    rw [hf]
  rw [hsame] at hpart
  omega

end Qatlib.Papers.MinMaxTree07.NoisyPivot
