/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.GroverSuccess.Lemma1CorrectedStat
import Qatlib.Concepts.SearchStopping.GroverSuccess.Lemma1RestrictedTigh

namespace Qatlib.Concepts.SearchStopping.GroverSuccess
open scoped BigOperators

theorem lemma1_cosine_sum_singular (α β : ℝ) (m : ℕ) (hβ : Real.sin β = 0) :
    (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) = (m : ℝ) * Real.cos α := by
  have hs : Real.sin (2 * β) = 0 := by rw [Real.sin_two_mul, hβ]; ring
  have hc : Real.cos (2 * β) = 1 := by
    have h := Real.sin_sq_add_cos_sq β
    rw [Real.cos_two_mul]
    rw [hβ] at h
    nlinarith
  have hconst (j : ℕ) : Real.cos (α + 2 * β * j) = Real.cos α := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show α + 2 * β * (j + 1 : ℕ) = (α + 2 * β * j) + 2 * β by push_cast; ring]
      rw [Real.cos_add, hc, hs]
      simpa using ih
  simp_rw [hconst]
  simp

theorem lemma1_cosine_sum_total (α β : ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      if Real.sin β = 0 then (m : ℝ) * Real.cos α
      else Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) / Real.sin β := by
  by_cases hβ : Real.sin β = 0
  · rw [if_pos hβ]
    exact lemma1_cosine_sum_singular α β m hβ
  · rw [if_neg hβ]
    exact lemma1_cosine_sum α β m hβ

theorem lemma1_odd_cosine_sum_total (α : ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      if Real.sin α = 0 then (m : ℝ) * Real.cos α
      else Real.sin (2 * m * α) / (2 * Real.sin α) := by
  by_cases hα : Real.sin α = 0
  · rw [if_pos hα]
    convert lemma1_cosine_sum_singular α α m hα using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  · rw [if_neg hα]
    exact lemma1_odd_cosine_sum α m hα

theorem lemma1Corrected : Lemma1Corrected :=
  ⟨fun α β m _ => lemma1_cosine_sum_total α β m,
    fun α m _ => lemma1_odd_cosine_sum_total α m⟩

end Qatlib.Concepts.SearchStopping.GroverSuccess
