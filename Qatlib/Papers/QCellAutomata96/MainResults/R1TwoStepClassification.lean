/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.PairWeights

set_option autoImplicit false
noncomputable section
open Complex Qatlib.Concepts.QcaDynamics.PairWeights

namespace Qatlib.Papers.QCellAutomata96.MainResults

theorem eq6_classification (a b c d e f : ℂ) (h : Eq6 a b c d e f) :
    (b = 0 ∧ c = 0 ∧ e = 0 ∧ f = 0 ∧ ‖a‖ = 1 ∧ ‖d‖ = 1) ∨
    (a = 0 ∧ b = 0 ∧ d = 0 ∧ e = 0 ∧ ‖c‖ = 1 ∧ ‖f‖ = 1) ∨
    (c = 0 ∧ d = 0 ∧ blockS1 e f a b ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∨
    (a = 0 ∧ f = 0 ∧ blockS2 b c d e ∈ Matrix.unitaryGroup (Fin 2) ℂ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  by_cases ha : a = 0
  · by_cases hd : d = 0
    · by_cases hc : c = 0
      · have h1' : a * star a + b * star b = 1 := by simpa [hc] using h1
        have h2' : e * star e + f * star f = 1 := by simpa [hd] using h2
        exact Or.inr (Or.inr (Or.inl ⟨hc, hd, blockS1_mem_unitaryGroup e f a b h2' h1' h4⟩))
      · have he : e = 0 := by
          have h3' : c * star e = 0 := by simpa [hd] using h3
          rcases mul_eq_zero.mp h3' with h | h
          · exact absurd h hc
          · exact star_eq_zero.mp h
        have hf1 : f * star f = 1 := by
          have := h2
          rw [hd, he] at this
          simpa using this
        have hfne : f ≠ 0 := by
          intro hf0
          rw [hf0] at hf1
          simp at hf1
        have hb : b = 0 := by
          have h4' : f * star b = 0 := by simpa [ha] using h4
          rcases mul_eq_zero.mp h4' with h | h
          · exact absurd h hfne
          · exact star_eq_zero.mp h
        have hc1 : c * star c = 1 := by
          have := h1
          rw [ha, hb] at this
          simpa using this
        exact Or.inr (Or.inl
          ⟨ha, hb, hd, he, norm_eq_one_of_mul_star hc1, norm_eq_one_of_mul_star hf1⟩)
    · have hf : f = 0 := by
        rcases mul_eq_zero.mp h6 with h | h
        · exact h
        · exact absurd (star_eq_zero.mp h) hd
      have h1' : b * star b + c * star c = 1 := by simpa [ha] using h1
      have h2' : d * star d + e * star e = 1 := by simpa [hf] using h2
      exact Or.inr (Or.inr (Or.inr ⟨ha, hf, blockS2_mem_unitaryGroup b c d e h1' h2' h3⟩))
  · by_cases hd : d = 0
    · have hc : c = 0 := by
        rcases mul_eq_zero.mp h5 with h | h
        · exact h
        · exact absurd (star_eq_zero.mp h) ha
      have h1' : a * star a + b * star b = 1 := by simpa [hc] using h1
      have h2' : e * star e + f * star f = 1 := by simpa [hd] using h2
      exact Or.inr (Or.inr (Or.inl ⟨hc, hd, blockS1_mem_unitaryGroup e f a b h2' h1' h4⟩))
    · have hc : c = 0 := by
        rcases mul_eq_zero.mp h5 with h | h
        · exact h
        · exact absurd (star_eq_zero.mp h) ha
      have hf : f = 0 := by
        rcases mul_eq_zero.mp h6 with h | h
        · exact h
        · exact absurd (star_eq_zero.mp h) hd
      have hb : b = 0 := by
        have h3' : b * star d = 0 := by simpa [hc] using h3
        rcases mul_eq_zero.mp h3' with h | h
        · exact h
        · exact absurd (star_eq_zero.mp h) hd
      have he : e = 0 := by
        have h4' : e * star a = 0 := by simpa [hf] using h4
        rcases mul_eq_zero.mp h4' with h | h
        · exact h
        · exact absurd (star_eq_zero.mp h) ha
      have ha1 : a * star a = 1 := by
        have := h1
        rw [hb, hc] at this
        simpa using this
      have hd1 : d * star d = 1 := by
        have := h2
        rw [he, hf] at this
        simpa using this
      exact Or.inl
        ⟨hb, hc, he, hf, norm_eq_one_of_mul_star ha1, norm_eq_one_of_mul_star hd1⟩

end Qatlib.Papers.QCellAutomata96.MainResults
