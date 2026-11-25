/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut.SourceSampling
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-!
# A concrete repetition budget for sampling a threshold cut

Section 4 after Eq. (12) combines a single-sample success probability of
at least one over the number of edges with independent repetition.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut

namespace Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut

/-- Twice the positive edge count trials suffice to bound the probability
of missing the threshold cut on every independent trial by one third. -/
theorem two_mul_repetition_failure_le (M : ℕ) (hM : 1 ≤ M) :
    (1 - (1 : ℝ) / M) ^ (2 * M) ≤ 1 / 3 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpos : (0 : ℝ) < M := by linarith
  have hbase : 0 ≤ 1 - (1 : ℝ) / M := sub_nonneg.mpr ((div_le_one hpos).2 hm)
  have hstep : 1 - (1 : ℝ) / M ≤ Real.exp (-(1 : ℝ) / M) := by
    calc
      _ = -(1 : ℝ) / M + 1 := by
        rw [neg_div]
        ring
      _ ≤ _ := Real.add_one_le_exp _
  have hexp : (3 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
    linarith
  calc
    _ ≤ Real.exp (-(1 : ℝ) / M) ^ (2 * M) := pow_le_pow_left₀ hbase hstep _
    _ = Real.exp (-2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp [ne_of_gt hpos]
    _ ≤ 1 / 3 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) hexp.le

/-- At the same explicit sample budget, a threshold cut is found with
probability at least two thirds under the paper's cut-law hypotheses,
and the repeated rounds fit the per-round gate budget. -/
theorem threshold_cut_at_repetition_budget {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (C : Ω → ℕ) (M C0 K : ℕ)
    (hP0 : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1)
    (hCtop : ∀ ω, C ω ≤ M) (hExp : (C0 : ℝ) ≤ ∑ ω, P ω * (C ω : ℝ))
    (hC0le : C0 ≤ M) (hM : 1 ≤ M) :
    (2 : ℝ) / 3 ≤ 1 - (1 - ∑ ω ∈ (Finset.univ.filter fun ω => C0 ≤ C ω), P ω) ^ (2 * M) ∧
      K * M * (2 * M) ≤ 2 * K * M ^ 2 :=
  ⟨paper_two_thirds_guarantee P C M C0 (2 * M) hP0 hP1 hCtop hExp hC0le hM
    (two_mul_repetition_failure_le M hM), repetition_gate_bound K M (2 * M) le_rfl⟩

end Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut
