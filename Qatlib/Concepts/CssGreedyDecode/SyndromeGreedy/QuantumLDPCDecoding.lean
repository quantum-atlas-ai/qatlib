/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy.QuantumLDPCDecodingDefs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy

open Matrix

open scoped BigOperators

theorem bitWeight_add_le {ι : Type*} [Fintype ι] (x y : ι → ZMod 2) :
    bitWeight (x + y) ≤ bitWeight x + bitWeight y := by
  classical
  apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply] at hi
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra h
  push Not at h
  exact hi (by simp [h.1, h.2])

theorem noisy_syndrome_update {ι κ : Type*} [Fintype ι]
    (H : Matrix κ ι (ZMod 2)) (e correction : ι → ZMod 2) (noise : κ → ZMod 2) :
    H *ᵥ (e + correction) + noise = H *ᵥ e + noise + H *ᵥ correction := by
  rw [Matrix.mulVec_add]
  abel

theorem correction_succeeds_below_half_distance
    {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ] [DecidableEq ι]
    (c : CssData ι κX κZ) (e correction : ι → ZMod 2)
    (hsyn : c.hX *ᵥ correction = c.hX *ᵥ e)
    (hweight : bitWeight correction ≤ bitWeight e)
    (hradius : ((2 * bitWeight e : ℕ) : ℕ∞) < cssDistance c) :
    e + correction ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ) := by
  classical
  by_contra hlogical
  have hcycle : c.hX *ᵥ (e + correction) = 0 := by
    rw [Matrix.mulVec_add, hsyn]
    ext i
    exact CharTwo.add_self_eq_zero _
  have hmem : (bitWeight (e + correction) : ℕ∞) ∈
      {w : ℕ∞ | ∃ z : ι → ZMod 2, c.hX *ᵥ z = 0 ∧
        z ∉ LinearMap.range (Matrix.mulVecLin c.hZᵀ) ∧ (bitWeight z : ℕ∞) = w} :=
    ⟨e + correction, hcycle, hlogical, rfl⟩
  have hd : cssDistance c ≤ (bitWeight (e + correction) : ℕ∞) :=
    (min_le_left _ _).trans (sInf_le hmem)
  have hw : bitWeight (e + correction) ≤ 2 * bitWeight e := by
    have h := bitWeight_add_le e correction
    omega
  have hw' : (bitWeight (e + correction) : ℕ∞) ≤ ((2 * bitWeight e : ℕ) : ℕ∞) := by
    exact_mod_cast hw
  exact (not_lt_of_ge (hd.trans hw')) hradius

theorem repeatedNoise_stable (α β R S A B C n : ℝ)
    (hα : 0 ≤ α) (hα1 : α < 1) (hβ : 0 ≤ β)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : 0 ≤ n)
    (hbudget : A * ((α * R + β * S) / (1 - α) + R) + B * S ≤ C)
    (residual data syndrome : ℕ → ℝ)
    (hzero : residual 0 = 0)
    (hdata : ∀ i, data i ≤ R * n)
    (hsyndrome : ∀ i, syndrome i ≤ S * n)
    (hstep : ∀ i, A * (residual i + data i) + B * syndrome i ≤ C * n →
      residual (i + 1) ≤ α * (residual i + data i) + β * syndrome i) :
    ∀ i, residual i ≤ (α * R + β * S) / (1 - α) * n := by
  have hden : 0 < 1 - α := by linarith
  let L : ℝ := (α * R + β * S) / (1 - α)
  have hL : 0 ≤ L := div_nonneg (add_nonneg (mul_nonneg hα hR) (mul_nonneg hβ hS)) hden.le
  have hfix : α * (L + R) + β * S = L := by
    dsimp [L]
    field_simp
    ring
  intro i
  induction i with
  | zero => simpa [hzero] using mul_nonneg hL hn
  | succ i ih =>
    have hb : A * (residual i + data i) + B * syndrome i ≤ C * n := calc
      _ ≤ A * (L * n + R * n) + B * (S * n) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add ih (hdata i)) hA)
          (mul_le_mul_of_nonneg_left (hsyndrome i) hB)
      _ = (A * (L + R) + B * S) * n := by ring
      _ ≤ C * n := mul_le_mul_of_nonneg_right hbudget hn
    calc
      residual (i + 1) ≤ α * (residual i + data i) + β * syndrome i := hstep i hb
      _ ≤ α * (L * n + R * n) + β * (S * n) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add ih (hdata i)) hα)
          (mul_le_mul_of_nonneg_left (hsyndrome i) hβ)
      _ = (α * (L + R) + β * S) * n := by ring
      _ = L * n := by rw [hfix]

theorem chooseReducingFlip_spec {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι (ZMod 2)) (s : κ → ZMod 2) (moves : List (ι → ZMod 2))
    (f : ι → ZMod 2) (h : (chooseReducingFlip H s moves).1 = some f) :
    f ∈ moves ∧ bitWeight (s + H *ᵥ f) < bitWeight s := by
  induction moves with
  | nil => simp [chooseReducingFlip] at h
  | cons g moves ih =>
    simp only [chooseReducingFlip] at h
    split at h
    · cases h
      exact ⟨List.mem_cons_self, ‹_›⟩
    · obtain ⟨hm, hw⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hw⟩

theorem chooseReducingFlip_checks {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι (ZMod 2)) (s : κ → ZMod 2) (moves : List (ι → ZMod 2)) :
    (chooseReducingFlip H s moves).2 ≤ moves.length := by
  induction moves with
  | nil => exact Nat.le_refl 0
  | cons f moves ih =>
    simp only [chooseReducingFlip]
    split
    · exact Nat.succ_le_succ (Nat.zero_le _)
    · exact Nat.succ_le_succ ih

theorem greedyDecode_syndrome {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι (ZMod 2)) (moves : List (ι → ZMod 2)) (fuel : ℕ) (s : κ → ZMod 2) :
    (greedyDecode H moves fuel s).syndrome = s + H *ᵥ (greedyDecode H moves fuel s).correction := by
  induction fuel generalizing s with
  | zero => simp [greedyDecode]
  | succ fuel ih =>
    simp only [greedyDecode]
    split
    · simp
    · rw [ih, Matrix.mulVec_add]
      abel

theorem greedyDecode_terminal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι (ZMod 2)) (moves : List (ι → ZMod 2)) (fuel : ℕ)
    (s : κ → ZMod 2) (hfuel : bitWeight s ≤ fuel) :
    (chooseReducingFlip H (greedyDecode H moves fuel s).syndrome moves).1 = none := by
  induction fuel generalizing s with
  | zero =>
    simp only [greedyDecode]
    cases h : (chooseReducingFlip H s moves).1 with
    | none => rfl
    | some f =>
      have hw := (chooseReducingFlip_spec H s moves f h).2
      omega
  | succ fuel ih =>
    simp only [greedyDecode]
    split
    · assumption
    · rename_i f h
      have hw := (chooseReducingFlip_spec H s moves f h).2
      exact ih _ (by omega)

theorem greedyDecode_checks {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι (ZMod 2)) (moves : List (ι → ZMod 2)) (fuel : ℕ) (s : κ → ZMod 2) :
    (greedyDecode H moves fuel s).candidateChecks ≤ fuel * moves.length := by
  induction fuel generalizing s with
  | zero => simp [greedyDecode]
  | succ fuel ih =>
    simp only [greedyDecode]
    split
    · exact (chooseReducingFlip_checks H s moves).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos fuel))
    · rename_i f _h
      have hc := chooseReducingFlip_checks H s moves
      have hr := ih (s + H *ᵥ f)
      simp only [Nat.succ_mul]
      omega

theorem repeatedNoise_source_budget (α β A B C R S : ℝ)
    (hα1 : α < 1) (hβ : 0 ≤ β) (hA : 0 < A) (hB : 0 < B)
    (hR : R ≤ (1 - α) * C / (2 * A))
    (hS : S ≤ (1 - α) * C / (2 * (β * A + (1 - α) * B))) :
    A * ((α * R + β * S) / (1 - α) + R) + B * S ≤ C := by
  have hden : 0 < 1 - α := by linarith
  have hR' := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hA)).mp hR
  have hSden : 0 < 2 * (β * A + (1 - α) * B) := by positivity
  have hS' := (le_div_iff₀ hSden).mp hS
  apply (mul_le_mul_iff_of_pos_right hden).mp
  have hid : (A * ((α * R + β * S) / (1 - α) + R) + B * S) * (1 - α) =
      A * R + (β * A + (1 - α) * B) * S := by
    field_simp
    ring
  rw [hid]
  nlinarith only [hR', hS']

theorem correlated_round_failure_bound {Ω : Type*} [Fintype Ω] (M : ℕ)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (bad : Fin M → Ω → Prop)
    [∀ i, DecidablePred (bad i)] (bound : Fin M → ℝ)
    (hround : ∀ i, (Finset.univ.filter (bad i)).sum p ≤ bound i) :
    (Finset.univ.filter fun ω => ∃ i, bad i ω).sum p ≤ ∑ i, bound i := by
  classical
  calc
    _ ≤ ∑ ω : Ω, ∑ i : Fin M, if bad i ω then p ω else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro ω _
      by_cases hb : ∃ i, bad i ω
      · rw [if_pos hb]
        obtain ⟨i, hi⟩ := hb
        have h := Finset.single_le_sum (s := Finset.univ) (a := i)
          (f := fun j : Fin M => if bad j ω then p ω else 0)
          (fun j _ => by
            change 0 ≤ (if bad j ω then p ω else 0)
            split_ifs
            · exact hp ω
            · exact le_refl 0)
          (Finset.mem_univ i)
        simpa [hi] using h
      · rw [if_neg hb]
        exact Finset.sum_nonneg fun i _ => by
          change 0 ≤ (if bad i ω then p ω else 0)
          split_ifs
          · exact hp ω
          · exact le_refl 0
    _ = ∑ i : Fin M, (Finset.univ.filter (bad i)).sum p := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_filter]
    _ ≤ ∑ i : Fin M, bound i := Finset.sum_le_sum fun i _ => hround i

end Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy
