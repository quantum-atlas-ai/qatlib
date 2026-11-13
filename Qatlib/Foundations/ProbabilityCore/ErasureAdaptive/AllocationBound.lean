/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.SurvivalDP
import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.Allocation

/-!
# Exponential survival bounds for adaptive erasure policies

This module compares the survival probability of an `ErasurePolicy` with a deterministic width
allocation, then bounds the allocation product by an exponential using its total budget. The
resulting estimate controls adaptive survival in terms of the number of steps and available
spacetime cost [BhartiHaugTanggara2026].

## Main statements

* `execute_le_allocation`: Some deterministic allocation bounds an adaptive policy's survival.
* `execute_survival_le_exp`: The survival probability is at most exp(-S p^(C/S)).

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option autoImplicit false
open scoped NNReal ENNReal BigOperators
open Finset
namespace Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

/-- For `S > 0` and `0 < p < 1`, a width allocation with total real cost at most `C` has
survival product at most `Real.exp (-(S : ℝ) * p ^ (C / (S : ℝ)))`. -/
theorem survival_product_le_exp
    (S m : ℕ) (hS : 0 < S) (p C : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (n : Fin S → Fin (m + 1))
    (hn : (∑ s, ((n s : ℕ) : ℝ)) ≤ C) :
    (∏ s, (1 - p ^ (((n s : ℕ) : ℝ)))) ≤
      Real.exp (-(S : ℝ) * p ^ (C / (S : ℝ))) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS

  have hfactor_nonneg : ∀ s : Fin S, 0 ≤ 1 - p ^ (((n s : ℕ) : ℝ)) := by
    intro s
    have h1 : p ^ (((n s : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one hp.le hp1.le (by positivity)
    linarith

  have hstep : ∏ s : Fin S, (1 - p ^ (((n s : ℕ) : ℝ)))
      ≤ ∏ s : Fin S, Real.exp (-(p ^ (((n s : ℕ) : ℝ)))) := by
    refine Finset.prod_le_prod₀ (fun s _ => hfactor_nonneg s) (fun s _ => ?_)
    simpa using Real.one_sub_le_exp_neg (p ^ (((n s : ℕ) : ℝ)))

  have hprodexp : (∏ s : Fin S, Real.exp (-(p ^ (((n s : ℕ) : ℝ)))))
      = Real.exp (-(∑ s : Fin S, p ^ (((n s : ℕ) : ℝ)))) := by
    rw [← Real.exp_sum]
    congr 1
    simp [Finset.sum_neg_distrib]

  have hmean : (S : ℝ) * p ^ ((∑ s, ((n s : ℕ) : ℝ)) / (S : ℝ))
      ≤ ∑ s, p ^ (((n s : ℕ) : ℝ)) := by
    have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => p ^ x) := convexOn_rpow_left hp
    have hjensen : p ^ (∑ s : Fin S, (1 / (S : ℝ)) • ((n s : ℕ) : ℝ))
        ≤ ∑ s : Fin S, (1 / (S : ℝ)) • p ^ (((n s : ℕ) : ℝ)) := by
      refine hconv.map_sum_le (t := Finset.univ)
        (w := fun _ : Fin S => 1 / (S : ℝ))
        (p := fun s : Fin S => ((n s : ℕ) : ℝ)) ?_ ?_ ?_
      · intro i _
        positivity
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [ne_of_gt hSpos]
      · intro i _
        exact Set.mem_univ _
    simp only [smul_eq_mul] at hjensen

    have hsum1 : (∑ s : Fin S, (1 / (S : ℝ)) * ((n s : ℕ) : ℝ))
        = (∑ s, ((n s : ℕ) : ℝ)) / (S : ℝ) := by
      rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
    have hsum2 : (∑ s : Fin S, (1 / (S : ℝ)) * p ^ (((n s : ℕ) : ℝ)))
        = (1 / (S : ℝ)) * ∑ s, p ^ (((n s : ℕ) : ℝ)) := by
      rw [← Finset.mul_sum]
    rw [hsum1, hsum2] at hjensen

    have hS1 : (S : ℝ) * (1 / (S : ℝ)) = 1 := by
      rw [one_div, mul_inv_cancel₀ (ne_of_gt hSpos)]
    have := mul_le_mul_of_nonneg_left hjensen hSpos.le
    rw [← mul_assoc, hS1, one_mul] at this
    exact this

  have hmono : p ^ (C / (S : ℝ)) ≤ p ^ ((∑ s, ((n s : ℕ) : ℝ)) / (S : ℝ)) := by
    have hdiv : (∑ s, ((n s : ℕ) : ℝ)) / (S : ℝ) ≤ C / (S : ℝ) := by
      apply div_le_div_of_nonneg_right hn hSpos.le
    exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hp hp1).2 hdiv
  have hsum_ge : (S : ℝ) * p ^ (C / (S : ℝ))
      ≤ ∑ s, p ^ (((n s : ℕ) : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hmono hSpos.le
    linarith [hmean]

  calc ∏ s, (1 - p ^ (((n s : ℕ) : ℝ)))
      ≤ ∏ s, Real.exp (-(p ^ (((n s : ℕ) : ℝ)))) := hstep
    _ = Real.exp (-(∑ s, p ^ (((n s : ℕ) : ℝ)))) := hprodexp
    _ ≤ Real.exp (-(S : ℝ) * p ^ (C / (S : ℝ))) := by
        apply Real.exp_le_exp_of_le
        linarith [hsum_ge]

/-- For `p ≤ 1`, every adaptive erasure policy has survival probability bounded by the survival
product of some deterministic width allocation with the same step count and budget. -/
theorem execute_le_allocation {R : Type*} (p : ℝ≥0) (hp : p ≤ 1) {S C : ℕ}
    (policy : ErasurePolicy R S C) :
    ∃ widths : Fin S → ℕ, (∑ i, widths i) ≤ C ∧
      execute p hp policy true ≤ (↑(∏ i, (1-p^(widths i)) : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨w,hw,he⟩ := bestProduct_attained p S C
  exact ⟨w,hw,he ▸ execute_le_best p hp policy⟩

/-- For `0 < p < 1` and `S > 0`, the real survival probability of a policy with `S` noise steps
and budget `C` is at most exp(-S p^(C/S)). -/
theorem execute_survival_le_exp {R : Type*} (p : ℝ≥0) (hp : 0 < p) (hp1 : p < 1)
    {S C : ℕ} (hS : 0 < S) (policy : ErasurePolicy R S C) :
    (execute p hp1.le policy true).toReal ≤
      Real.exp (-(S : ℝ) * (p : ℝ) ^ ((C : ℝ)/(S : ℝ))) := by
  obtain ⟨w,hw,he⟩ := execute_le_allocation p hp1.le policy
  have hle : (execute p hp1.le policy true).toReal ≤
      ((∏ i, (1-p^(w i)) : ℝ≥0) : ℝ) := by
    exact ENNReal.toReal_le_coe_of_le_coe he
  let widths : Fin S → Fin (C+1) := fun i => ⟨w i, Nat.lt_succ_of_le (allocation_width_le w hw i)⟩
  have hsum : (∑ i, ((widths i).val : ℝ)) ≤ (C : ℝ) := by
    change (∑ i, (w i : ℝ)) ≤ _
    exact_mod_cast hw
  have hb := survival_product_le_exp S C hS p C (by exact_mod_cast hp)
    (by exact_mod_cast hp1) widths hsum
  apply hle.trans
  have hcoe : ∀ i : Fin S, ((1-p^(w i) : ℝ≥0) : ℝ) = 1-(p : ℝ)^(w i) := by
    intro i
    rw [NNReal.coe_sub (pow_le_one₀ (by positivity) hp1.le), NNReal.coe_one, NNReal.coe_pow]
  simpa only [NNReal.coe_prod, hcoe, Real.rpow_natCast, widths] using hb

end Qatlib.Foundations.ProbabilityCore.ErasureAdaptive
