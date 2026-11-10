/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Lemma63

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Finset
open Classical

variable {n : ℕ}

noncomputable def genProb (G : Type) [Fintype G] [Group G] (i : ℕ) : ℝ :=
  ((Finset.univ.filter (fun S : Fin i → G => Subgroup.closure (Set.range S) = ⊤)).card : ℝ)
    / ((Fintype.card G : ℝ) ^ i)

theorem closure_range_eq_top_iff (G : Type) [Fintype G] [Group G] {i : ℕ}
    (S : Fin i → G) :
    Subgroup.closure (Set.range S) = ⊤ ↔
      ∀ K : Subgroup G, K < ⊤ → ∃ j : Fin i, S j ∉ K := by
  classical
  constructor
  · intro h K hK
    by_contra hnot
    push_neg at hnot
    have hle : Subgroup.closure (Set.range S) ≤ K := by
      rw [Subgroup.closure_le]
      rintro x ⟨j, rfl⟩
      exact hnot j
    rw [h] at hle
    exact (not_le_of_gt hK) hle
  · intro h
    by_contra hne
    have hK : Subgroup.closure (Set.range S) < ⊤ := lt_of_le_of_ne le_top hne
    obtain ⟨j, hj⟩ := h _ hK
    exact hj (Subgroup.subset_closure ⟨j, rfl⟩)

theorem closure_range_ne_top_of_mem_proper (G : Type) [Fintype G] [Group G] {i : ℕ}
    (S : Fin i → G) (K : Subgroup G) (hK : K < ⊤) (hS : ∀ j, S j ∈ K) :
    Subgroup.closure (Set.range S) ≠ ⊤ := by
  classical
  intro htop
  have h := (closure_range_eq_top_iff G S).mp htop K hK
  obtain ⟨j, hj⟩ := h
  exact hj (hS j)

theorem genProb_nonneg (G : Type) [Fintype G] [Group G] (i : ℕ) :
    0 ≤ genProb G i := by
  unfold genProb
  positivity

theorem genProb_le_one (G : Type) [Fintype G] [Group G] (i : ℕ) :
    genProb G i ≤ 1 := by
  classical
  unfold genProb
  have hden : (0 : ℝ) < (Fintype.card G : ℝ) ^ i :=
    pow_pos (by exact_mod_cast Fintype.card_pos) i
  rw [div_le_one hden]
  have hle : (Finset.univ.filter
      (fun S : Fin i → G => Subgroup.closure (Set.range S) = ⊤)).card
      ≤ Fintype.card (Fin i → G) := Finset.card_filter_le _ _
  have hle' : ((Finset.univ.filter
      (fun S : Fin i → G => Subgroup.closure (Set.range S) = ⊤)).card : ℝ)
      ≤ (Fintype.card (Fin i → G) : ℝ) := by exact_mod_cast hle
  simpa [Fintype.card_fun] using hle'

end Qatlib.Papers.NonabelianHSP98.MainResults.Lemma63
