/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators Classical

namespace Qatlib.Papers.ExactSimon97.MainResults

def bitZero {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n)) (i : Fin n) : Finset (BoolVec n) :=
  Finset.univ.filter (fun k => k ∈ K ∧ k i = 0)

def bitOne {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n)) (i : Fin n) : Finset (BoolVec n) :=
  Finset.univ.filter (fun k => k ∈ K ∧ k i = 1)

theorem coordinate_balance {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n))
    (g0 : BoolVec n) (hg0K : g0 ∈ K) (i : Fin n) (hg0 : g0 i = 1) :
    (bitZero K i).card = (bitOne K i).card := by
  classical
  refine Finset.card_bij (fun a _ => a + g0) ?_ ?_ ?_
  · intro a ha
    simp only [bitZero, bitOne, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    refine ⟨K.add_mem ha.1 hg0K, ?_⟩
    have hbit : (a + g0) i = a i + g0 i := rfl
    rw [hbit, ha.2, hg0]
    exact zero_add 1
  · intro a₁ _ a₂ _ h
    exact add_right_cancel h
  · intro b hb
    simp only [bitOne, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨b + g0, ?_, ?_⟩
    · simp only [bitZero, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨K.add_mem hb.1 hg0K, ?_⟩
      have hbit : (b + g0) i = b i + g0 i := rfl
      rw [hbit, hb.2, hg0]
      exact CharTwo.add_self_eq_zero (1 : ZMod 2)
    · have h2 : g0 + g0 = 0 := by
        funext j
        exact CharTwo.add_self_eq_zero (g0 j)
      calc (b + g0) + g0 = b + (g0 + g0) := by rw [add_assoc]
        _ = b + 0 := by rw [h2]
        _ = b := add_zero b

theorem coordinate_dichotomy {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n))
    (i : Fin n) :
    (∀ k ∈ K, k i = 0) ∨
      ∃ g0 : BoolVec n, g0 ∈ K ∧ g0 i = 1 ∧ (bitZero K i).card = (bitOne K i).card := by
  classical
  by_cases h : ∃ g0 ∈ K, g0 i = 1
  · obtain ⟨g0, hg0K, hg0⟩ := h
    exact Or.inr ⟨g0, hg0K, hg0, coordinate_balance K g0 hg0K i hg0⟩
  · push Not at h
    apply Or.inl
    intro k hk
    have hv : k i = 0 ∨ k i = 1 := by
      have : (k i).val < 2 := (k i).val_lt
      interval_cases hval : (k i).val
      · exact Or.inl ((ZMod.val_eq_zero _).mp hval)
      · apply Or.inr
        apply ZMod.val_injective
        simpa using! hval
    exact hv.resolve_right (h k hk)

end Qatlib.Papers.ExactSimon97.MainResults
