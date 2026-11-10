/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.SearchTools.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.AugmentCore

open Qatlib.Papers.QMatchingFlow05.SearchTools

theorem disjointPaths_card_le {V : Type} [Fintype V] [DecidableEq V]
    {ι : Type} [Fintype ι] (P : ι → Finset V) (L : ℕ)
    (hcard : ∀ i, L + 1 ≤ (P i).card)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) :
    Fintype.card ι * (L + 1) ≤ Fintype.card V := by
  have hbunion : (Finset.univ.biUnion P).card = ∑ i : ι, (P i).card := by
    rw [Finset.card_biUnion]
    intro i _ j _ hij
    exact hdisj i j hij
  have hle_card : (Finset.univ.biUnion P).card ≤ Fintype.card V := by
    have hsub : (Finset.univ.biUnion P) ⊆ (Finset.univ : Finset V) := by
      intro x _
      simp
    simpa [Finset.card_univ] using Finset.card_le_card hsub
  have hsum : (∑ _i : ι, (L + 1)) ≤ ∑ i : ι, (P i).card :=
    Finset.sum_le_sum fun i _ => hcard i
  have hone : (∑ _i : ι, (L + 1)) = Fintype.card ι * (L + 1) := by
    simp [Finset.card_univ]
  calc Fintype.card ι * (L + 1) = ∑ _i : ι, (L + 1) := hone.symm
    _ ≤ ∑ i : ι, (P i).card := hsum
    _ = (Finset.univ.biUnion P).card := hbunion.symm
    _ ≤ Fintype.card V := hle_card

theorem hk_phase_vertex_bound {V : Type} [Fintype V] [DecidableEq V]
    (j g : ℕ) (P : Fin g → Finset V)
    (hcard : ∀ i, j + 3 ≤ (P i).card)
    (hdisj : ∀ i k, i ≠ k → Disjoint (P i) (P k)) :
    (j + 3) * g ≤ Fintype.card V := by
  have h := disjointPaths_card_le (V := V) (ι := Fin g) P (j + 2) ?_ ?_
  · simpa [Fintype.card_fin, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.mul_comm] using h
  · intro i
    have hi := hcard i
    omega
  · intro i k hik
    exact hdisj i k hik

theorem phase_length_growth (len : ℕ → ℕ) (hmono : ∀ j, len j < len (j + 1))
    (h0 : 1 ≤ len 0) : ∀ j, j + 1 ≤ len j := by
  intro j
  induction j with
  | zero => simpa using h0
  | succ j ih =>
      have hstep := hmono j
      omega

theorem hk_phase_sqrt_bound (n j g : ℕ) (hn : 0 < n)
    (hbound : (j + 3) * g ≤ n) (hg : Real.sqrt (n : ℝ) ≤ (g : ℝ)) :
    (j : ℝ) + 3 ≤ Real.sqrt (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hbound' : ((j + 3 : ℕ) : ℝ) * (g : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbound
  have hcast : ((j + 3 : ℕ) : ℝ) = (j : ℝ) + 3 := by push_cast; ring
  rw [hcast] at hbound'
  have hstep : ((j : ℝ) + 3) * Real.sqrt (n : ℝ) ≤ ((j : ℝ) + 3) * (g : ℝ) :=
    mul_le_mul_of_nonneg_left hg (by positivity)
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn'.le
  have hchain : ((j : ℝ) + 3) * Real.sqrt (n : ℝ) ≤
      Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
    calc ((j : ℝ) + 3) * Real.sqrt (n : ℝ) ≤ ((j : ℝ) + 3) * (g : ℝ) := hstep
      _ ≤ (n : ℝ) := hbound'
      _ = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := hsq.symm
  exact (mul_le_mul_iff_left₀ hs).1 hchain

theorem hk_iteration_bound (n j g T : ℕ) (hn : 0 < n)
    (hfirst : Real.sqrt (n : ℝ) < (g : ℝ) + 1)
    (hlen : ((g : ℝ) + 1) * ((j : ℝ) + 2) ≤ (n : ℝ))
    (hg : (g : ℝ) ≤ Real.sqrt (n : ℝ))
    (hT : T ≤ j + g) : (T : ℝ) ≤ 2 * Real.sqrt (n : ℝ) + 1 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hj2 : ((j : ℝ) + 2) ≤ Real.sqrt (n : ℝ) := by
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn'.le
    have hmul : Real.sqrt (n : ℝ) * ((j : ℝ) + 2) ≤
        Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
      calc Real.sqrt (n : ℝ) * ((j : ℝ) + 2) ≤ ((g : ℝ) + 1) * ((j : ℝ) + 2) :=
              mul_le_mul_of_nonneg_right hfirst.le (by positivity)
        _ ≤ (n : ℝ) := hlen
        _ = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := hsq.symm
    exact le_of_mul_le_mul_left hmul hs
  have hT' : (T : ℝ) ≤ (j : ℝ) + (g : ℝ) := by exact_mod_cast hT
  linarith

theorem hk_gap_le_vertices {V : Type} [Fintype V] [DecidableEq V]
    (j g : ℕ) (P : Fin g → Finset V)
    (hcard : ∀ i, j + 3 ≤ (P i).card)
    (hdisj : ∀ i k, i ≠ k → Disjoint (P i) (P k)) :
    g ≤ Fintype.card V := by
  have h := hk_phase_vertex_bound j g P hcard hdisj
  have hpos : 1 ≤ j + 3 := by omega
  nlinarith [h, hpos, Nat.zero_le g]

end Qatlib.Papers.QMatchingFlow05.AugmentCore

end
