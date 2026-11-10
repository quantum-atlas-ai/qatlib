/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BinaryOptEncode.ExactGadgets.LocalGadgets

set_option autoImplicit false
namespace Qatlib.Concepts.BinaryOptEncode.ExactGadgets
open scoped BigOperators

def poolValue {I : Type*} [Fintype I] (a : I → ℝ) (selector : I → Bool) : ℝ :=
  ∑ i, bitValue (selector i) * a i

theorem maxpool_correct {I : Type*} [Fintype I] (a : I → ℝ) (selector : I → Bool)
    (M : ℝ) (hone : (∑ i, if selector i then (1 : ℕ) else 0) = 1)
    (hc : ∀ i j, a j ≤ bitValue (selector i) * a i + (1 - bitValue (selector i)) * M) :
    ∃ k, selector k = true ∧ poolValue a selector = a k ∧
      ∀ j, a j ≤ poolValue a selector := by
  classical
  let chosen : Finset I := Finset.univ.filter fun i => selector i = true
  have hcard : chosen.card = 1 := by
    rw [Finset.card_eq_sum_ones]
    simpa [chosen, Finset.sum_filter] using hone
  obtain ⟨k, hkset⟩ := Finset.card_eq_one.mp hcard
  have hkm : k ∈ chosen := by rw [hkset]; simp
  have hk : selector k = true := (Finset.mem_filter.mp hkm).2
  have huniq : ∀ i, selector i = true → i = k := by
    intro i hi
    have hm : i ∈ chosen := by simp [chosen, hi]
    rw [hkset] at hm
    exact Finset.mem_singleton.mp hm
  have hsel : ∀ i, selector i = decide (i = k) := by
    intro i
    by_cases hi : i = k
    · subst i
      simp [hk]
    · cases hs : selector i
      · simp [hi]
      · exact False.elim (hi (huniq i hs))
  have hvalue : poolValue a selector = a k := by simp [poolValue, hsel, bitValue]
  refine ⟨k, hk, hvalue, ?_⟩
  intro j
  rw [hvalue]
  simpa [bitValue, hk] using hc k j

theorem maxpool_witness {I : Type*} [Fintype I] (a : I → ℝ) (M : ℝ) (k : I)
    (hmax : ∀ j, a j ≤ a k) (hM : ∀ j, a j ≤ M) :
    ∃ selector : I → Bool, (∑ i, if selector i then (1 : ℕ) else 0) = 1 ∧
      ∀ i j, a j ≤ bitValue (selector i) * a i + (1 - bitValue (selector i)) * M := by
  classical
  refine ⟨fun i => decide (i = k), by simp, ?_⟩
  intro i j
  by_cases hi : i = k
  · subst i
    simpa [bitValue] using hmax j
  · simpa [bitValue, hi] using hM j

theorem maxpool_feasible_exists {I : Type*} [Fintype I] [Nonempty I]
    (a : I → ℝ) (M : ℝ) (hM : ∀ j, a j ≤ M) :
    ∃ selector : I → Bool, (∑ i, if selector i then (1 : ℕ) else 0) = 1 ∧
      ∀ i j, a j ≤ bitValue (selector i) * a i + (1 - bitValue (selector i)) * M := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  exact maxpool_witness a M k (fun j => hk j (Finset.mem_univ j)) hM

theorem maxpool_with_explicit_ceiling {I : Type*} [Fintype I] [Nonempty I] (a : I → ℝ) :
    ∃ selector : I → Bool, (∑ i, if selector i then (1 : ℕ) else 0) = 1 ∧
      ∀ i j, a j ≤ bitValue (selector i) * a i +
        (1 - bitValue (selector i)) * (∑ k, |a k|) := by
  classical
  apply maxpool_feasible_exists
  intro j
  exact (le_abs_self (a j)).trans
    (Finset.single_le_sum (fun k _ => abs_nonneg (a k)) (Finset.mem_univ j))

end Qatlib.Concepts.BinaryOptEncode.ExactGadgets
