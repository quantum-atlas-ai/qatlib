/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TensorPCA19.MainResults.Source.Polynomial
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section


open MeasureTheory

set_option autoImplicit false

namespace Qatlib.Papers.TensorPCA19.MainResults
noncomputable section

/-- A point mass at a polynomial root satisfies interval support but defeats the random-point bound. -/
theorem lemma10_random_point_counterexample :
    (Polynomial.X - 1 : Polynomial ℝ).natDegree ≤ 2 * (1 : ℕ) ∧
    (1 : ℝ) < 2 ∧ (0 : ℝ) ∉ Set.Icc 1 2 ∧ (0 : ℝ) < 1 ∧
    IsProbabilityMeasure (Measure.dirac (1 : ℝ)) ∧
    Measurable (id : ℝ → ℝ) ∧
    Measure.dirac (1 : ℝ) {ω : ℝ | id ω ∉ Set.Icc (1 : ℝ) 2} = 0 ∧
    ¬ (1 / 2 : ℝ) ≤
      ((Measure.dirac (1 : ℝ)) {ω : ℝ |
        |Polynomial.eval 0 (Polynomial.X - 1 : Polynomial ℝ)| *
          (((1 : ℝ) + 2) / (2 - 1)) ^ (-(2 * (1 : ℝ))) *
          Real.exp (-(1 * (1 : ℝ))) ≤
            |Polynomial.eval (id ω) (Polynomial.X - 1 : Polynomial ℝ)|}).toReal := by
  have hp : 0 <
      |Polynomial.eval 0 (Polynomial.X - 1 : Polynomial ℝ)| *
        (((1 : ℝ) + 2) / (2 - 1)) ^ (-(2 * (1 : ℝ))) *
        Real.exp (-(1 * (1 : ℝ))) := by
    norm_num only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
      zero_sub, abs_neg, abs_one]
    positivity
  refine ⟨?_, by norm_num, by norm_num [Set.mem_Icc], one_pos,
    inferInstance, measurable_id, ?_, ?_⟩
  · simpa using (Polynomial.natDegree_X_sub_C (1 : ℝ)).le.trans (by norm_num : 1 ≤ 2)
  · norm_num [Measure.dirac_apply, Set.mem_Icc]
  · have hnot : (1 : ℝ) ∉ {ω : ℝ |
        |Polynomial.eval 0 (Polynomial.X - 1 : Polynomial ℝ)| *
          (((1 : ℝ) + 2) / (2 - 1)) ^ (-(2 * (1 : ℝ))) *
          Real.exp (-(1 * (1 : ℝ))) ≤
            |Polynomial.eval (id ω) (Polynomial.X - 1 : Polynomial ℝ)|} := by
      simp only [Set.mem_ofPred_eq, id_eq, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_one, sub_self, abs_zero]
      simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one] using
        (not_le_of_gt hp)
    rw [Measure.dirac_apply, Set.indicator_of_notMem hnot]
    norm_num

end
end Qatlib.Papers.TensorPCA19.MainResults
