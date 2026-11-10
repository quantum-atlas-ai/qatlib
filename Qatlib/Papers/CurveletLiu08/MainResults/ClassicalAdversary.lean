/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CurveletLiu08.MainResults

theorem source_theorem8
    (n R δ μ m ℓ : ℝ) (_hR : 0 < R) (_hμ : 0 < μ)
    (_hm : m = Real.log (R / μ) / Real.log 2)
    (_hℓ : ℓ ≤ (1 / 2 * n * m) / (Real.log (1 / 2 * n * m) / Real.log 2))
    (_hnm : 4 ≤ n * m)
    {I A : Type*} [Fintype I] [Fintype A]
    (hI : 0 < Fintype.card I)
    (ν : A → ℝ) (hν0 : ∀ a, 0 ≤ ν a) (hνsum : (∑ a, ν a) = 1)
    (fail : A → I → ℝ)
    (_hfail01 : ∀ a i, fail a i ∈ Set.Icc (0 : ℝ) 1)
    (hdet : ∀ a, 1 - (2 : ℝ) ^ (-(n * m / 2)) ≤
      (1 / (Fintype.card I : ℝ)) * ∑ i, fail a i) :
    ∃ i : I, 1 - (2 : ℝ) ^ (-(n * m / 2)) ≤ ∑ a, ν a * fail a i := by
  classical
  set ε : ℝ := (2 : ℝ) ^ (-(n * m / 2)) with hεdef

  have hAne : Nonempty A := by
    by_contra h
    rw [not_nonempty_iff] at h
    haveI : IsEmpty A := h
    have hz : (∑ a : A, ν a) = 0 := by simp
    rw [hνsum] at hz
    norm_num at hz
  haveI := hAne
  set g : I → ℝ := fun i => ∑ a, ν a * fail a i with hgdef
  have hcardI : (0 : ℝ) < (Fintype.card I : ℝ) := by
    exact_mod_cast hI

  have hstep : 1 - ε ≤ (1 / (Fintype.card I : ℝ)) * ∑ i, g i := by
    have hmul : ∑ a, ν a * (1 - ε) ≤
        ∑ a, ν a * ((1 / (Fintype.card I : ℝ)) * ∑ i, fail a i) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hdet a) (hν0 a))
    have hL : ∑ a, ν a * (1 - ε) = 1 - ε := by
      rw [← Finset.sum_mul, hνsum, one_mul]
    have hR : ∑ a, ν a * ((1 / (Fintype.card I : ℝ)) * ∑ i, fail a i)
        = (1 / (Fintype.card I : ℝ)) * ∑ i, g i := by
      simp only [hgdef]
      calc ∑ a, ν a * ((1 / (Fintype.card I : ℝ)) * ∑ i, fail a i)
          = ∑ a, ∑ i, (1 / (Fintype.card I : ℝ)) * (ν a * fail a i) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = ∑ i, ∑ a, (1 / (Fintype.card I : ℝ)) * (ν a * fail a i) := by
              rw [Finset.sum_comm]
        _ = (1 / (Fintype.card I : ℝ)) * ∑ i, ∑ a, ν a * fail a i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
    rw [hL, hR] at hmul
    exact hmul

  have hex : ∃ i, 1 - ε ≤ g i := by
    by_contra h
    push Not at h
    have hlt : ∑ i, g i < ∑ _i : I, (1 - ε) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact le_of_lt (h i)
      · have hne : (Finset.univ : Finset I).Nonempty :=
          Finset.card_pos.mp (by rw [Finset.card_univ]; exact hI)
        obtain ⟨i, hi⟩ := hne
        exact ⟨i, hi, h i⟩
    have hconst : ∑ _i : I, (1 - ε) = (Fintype.card I : ℝ) * (1 - ε) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hmul : (1 / (Fintype.card I : ℝ)) * ∑ i, g i
        < (1 / (Fintype.card I : ℝ)) * ((Fintype.card I : ℝ) * (1 - ε)) := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      rw [← hconst]
      exact hlt
    have heq : (1 / (Fintype.card I : ℝ)) * ((Fintype.card I : ℝ) * (1 - ε)) = 1 - ε := by
      field_simp
    linarith [hstep, hmul, heq]
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, by simpa only [hgdef] using hi⟩

end Qatlib.Papers.CurveletLiu08.MainResults
