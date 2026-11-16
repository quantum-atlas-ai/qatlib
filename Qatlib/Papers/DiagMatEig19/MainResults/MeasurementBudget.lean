/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Measurement budget for seeing every outcome

This premise repair preserves all three theorem names from the supplied
DiagMatEig19 unit. The positive estimates use a lower bound on outcome masses;
the counterexample records the failure of the original upper-bound premise.
The estimate controls the coupon-collector union-bound sum, without asserting
an unmodelled sampling process.

Fixed source: Changpeng Shao, *Computing eigenvalues of diagonalizable matrices
in a quantum computer*, arXiv:1912.08015v3, Lemma 14 (printed p. 12) and
Appendix C (printed pp. 25–26). The source uses a maximum mass where a minimum
is needed. This file proves the corrected estimate and retains a counterexample
to the source's maximum-mass estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiagMatEig19.MainResults

open scoped BigOperators

/-- A lower bound on all outcome masses gives the logarithmic measurement
budget in the corrected coupon-collector estimate associated with Lemma 14
of fixed arXiv:1912.08015v3, p. 12 and Appendix C, pp. 25–26. -/
theorem lemma14_measurement_budget_of_min
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (pmin δ : ℝ)
    (hle : ∀ j, pmin ≤ p j) (hpmax1 : ∀ j, p j ≤ 1)
    (hδ : 0 < δ) (m : ℕ)
    (hm : Real.log ((n : ℝ) / δ) ≤ (m : ℝ) * pmin) :
    ∑ j : Fin n, (1 - p j) ^ m ≤ δ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnd : 0 < (n : ℝ) / δ := div_pos hnpos hδ
  calc
    ∑ j : Fin n, (1 - p j) ^ m
        ≤ ∑ _j : Fin n, (1 - pmin) ^ m := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          apply pow_le_pow_left₀
          · linarith [hpmax1 j]
          · linarith [hle j]
    _ = (n : ℝ) * (1 - pmin) ^ m := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (Real.exp (-pmin)) ^ m := by
          have hbase : 1 - pmin ≤ Real.exp (-pmin) := Real.one_sub_le_exp_neg pmin
          have hb0 : 0 ≤ 1 - pmin := by linarith [hle ⟨0, hn⟩, hpmax1 ⟨0, hn⟩]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbase m) hnpos.le
    _ = (n : ℝ) * Real.exp (-((m : ℝ) * pmin)) := by
          rw [← Real.exp_nat_mul, mul_neg]
    _ ≤ (n : ℝ) * Real.exp (-Real.log ((n : ℝ) / δ)) := by
          have h1 : -((m : ℝ) * pmin) ≤ -Real.log ((n : ℝ) / δ) := by linarith
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hnpos.le
    _ = δ := by
          rw [Real.exp_neg, Real.exp_log hnd]
          field_simp [ne_of_gt hnpos, ne_of_gt hδ]

/-- The original positive theorem is retained with the repaired lower-mass
premise: the logarithmic budget bounds the total probability of missing an
outcome as estimated by the union-bound sum. -/
theorem lemma14_measurement_budget
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (pmin δ : ℝ)
    (hle : ∀ j, pmin ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hδ : 0 < δ) (m : ℕ)
    (hm : Real.log ((n : ℝ) / δ) ≤ (m : ℝ) * pmin) :
    ∑ j : Fin n, (1 - p j) ^ m ≤ δ := by
  exact lemma14_measurement_budget_of_min hn p pmin δ hle hp1 hδ m hm

/-- The upper-mass version fails even for a probability distribution on two
outcomes: nine samples have a union-bound sum greater than one percent. -/
theorem lemma14_counterexample :
    ∃ (p : Fin 2 → ℝ) (pmax δ : ℝ) (m : ℕ),
      (∀ j, 0 ≤ p j) ∧ (∀ j, p j ≤ pmax) ∧ 0 ≤ pmax ∧ pmax ≤ 1 ∧
      0 < δ ∧ Real.log ((2 : ℝ) / δ) ≤ (m : ℝ) * pmax ∧
      δ < ∑ j : Fin 2, (1 - p j) ^ m := by
  refine ⟨![99/100, 1/100], 99/100, 1/100, 9, ?_, ?_, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num
  · intro j
    fin_cases j <;> norm_num
  · rw [show ((2 : ℝ) / (1/100)) = 200 by norm_num]
    have hlog : Real.log 200 ≤ 8 := by
      have h200 : (200 : ℝ) ≤ Real.exp 8 := by
        have hpow : (2 : ℝ) ^ 8 ≤ (Real.exp 1) ^ 8 :=
          pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 8
        have hexp8 : (Real.exp 1) ^ 8 = Real.exp 8 := by
          rw [← Real.exp_nat_mul]
          norm_num
        have h256 : (200 : ℝ) ≤ 2 ^ 8 := by norm_num
        linarith
      calc
        Real.log 200 ≤ Real.log (Real.exp 8) := Real.log_le_log (by norm_num) h200
        _ = 8 := Real.log_exp 8
    norm_num
    linarith
  · norm_num [Fin.sum_univ_two]

/-- The repaired hypotheses are realizable by a normalized two-outcome
distribution with positive masses and a failure tolerance strictly below one. -/
theorem lemma14_repair_satisfiable :
    ∃ (p : Fin 2 → ℝ) (pmin δ : ℝ) (m : ℕ),
      (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧ 0 < pmin ∧
      (∀ j, pmin ≤ p j) ∧ (∀ j, p j ≤ 1) ∧ 0 < δ ∧ δ < 1 ∧
      Real.log ((2 : ℝ) / δ) ≤ (m : ℝ) * pmin ∧
      ∑ j : Fin 2, (1 - p j) ^ m ≤ δ := by
  refine ⟨fun _ => 1 / 2, 1 / 2, 1 / 2, 8, ?_, ?_, by norm_num, ?_, ?_,
    by norm_num, by norm_num, ?_, ?_⟩
  · intro j
    norm_num
  · norm_num [Fin.sum_univ_two]
  · intro j
    norm_num
  · intro j
    norm_num
  · have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at ⊢
    linarith
  · norm_num [Fin.sum_univ_two]

end Qatlib.Papers.DiagMatEig19.MainResults
