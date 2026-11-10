/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.GaussSumCore
import Qatlib.Papers.GaussSumEst02.MainResults.Source.Cost
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.MainResults.Claims

open Qatlib.Papers.GaussSumEst02.MainResults.Source

theorem lemma1_chiStatePreparation {K : Type*} [Field K] [Fintype K] (χ : MultChar K)
    (hnt : χ.IsNontrivial)
    (dlog qft : ℕ → ℕ) (hdlog : PolyLog dlog) (hqft : PolyLog qft) :
    (∑ x : K, ‖chiState χ x‖ ^ 2 = 1) ∧
    (∀ x : K, chiState χ x
      = χ.toFun x / ((Real.sqrt ((Fintype.card K - 1 : ℕ) : ℝ)) : ℂ)) ∧
    PolyLog (fun n => dlog n + qft n + 2) := by
  classical
  refine ⟨?_, fun x => rfl, ?_⟩
  · have hcard : 2 ≤ Fintype.card K := by
      have := Fintype.one_lt_card (α := K)
      omega
    have hden_pos : 0 < Real.sqrt ((Fintype.card K - 1 : ℕ) : ℝ) := by
      apply Real.sqrt_pos.mpr
      have hpos : (0 : ℝ) < ((Fintype.card K - 1 : ℕ) : ℝ) := by
        have : 0 < Fintype.card K - 1 := by omega
        exact_mod_cast this
      exact hpos
    have hterm : ∀ x : K, x ≠ 0 → ‖chiState χ x‖ ^ 2
        = 1 / ((Fintype.card K - 1 : ℕ) : ℝ) := by
      intro x hx
      simp only [chiState]
      rw [norm_div, χ.norm_eq_one x hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hden_pos, div_pow, one_pow, Real.sq_sqrt (by positivity)]
    have hzero : ‖chiState χ 0‖ ^ 2 = 0 := by
      simp [chiState, χ.map_zero']
    have hsum : (∑ x : K, ‖chiState χ x‖ ^ 2)
        = ((Fintype.card K - 1 : ℕ) : ℝ)
            * (1 / ((Fintype.card K - 1 : ℕ) : ℝ)) := by
      have hsub : (∑ x ∈ Finset.univ.erase (0 : K), ‖chiState χ x‖ ^ 2)
          = ∑ x : K, ‖chiState χ x‖ ^ 2 := by
        refine Finset.sum_subset (Finset.erase_subset _ _) ?_
        intro x _ hx
        have hx0 : x = 0 := by
          by_contra h
          exact hx (Finset.mem_erase.mpr ⟨h, Finset.mem_univ x⟩)
        rw [hx0]
        exact hzero
      rw [← hsub]
      rw [Finset.sum_congr rfl
        (fun x hx => hterm x (Finset.mem_erase.mp hx).1)]
      rw [Finset.sum_const, nsmul_eq_mul,
        Finset.card_erase_of_mem (Finset.mem_univ (0 : K)), Finset.card_univ]
    rw [hsum]
    have hne : ((Fintype.card K - 1 : ℕ) : ℝ) ≠ 0 := by
      have : 0 < Fintype.card K - 1 := by omega
      exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
    field_simp
  · exact polyLog_add (polyLog_add hdlog hqft) (polyLog_const 2 (by norm_num))

end Qatlib.Papers.GaussSumEst02.MainResults.Claims
