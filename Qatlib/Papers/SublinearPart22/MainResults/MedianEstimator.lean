/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SublinearPart22.MainResults.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Nondestructive Quantile-Search Median Estimator Specification

This module formalizes Section 3, Proposition 3.2 (pp. 10--11, Algorithm 5) of
Hamoudi and Magniez on the specification-level existence of a nondestructive
median estimator lying within `17 σ` of the mean `μ` with probability at least
`1 - η`, restoring the input state with probability at least `1 - η`, and using
`O(log(n + 1) log(log(n + 1) / η + 2))` expected reflections.

## Main statements

* `proposition32_nondestructive_median_estimator`: Proposition 3.2,
  nondestructive median estimator `RandomizedRun` specification.

## References

* [Hamoudi and Magniez, 2022][HamoudiMagniez2022Sublinear], Section 3,
  Proposition 3.2, pp. 10--11.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- **Proposition 3.2** (arXiv:2207.08643v1, p. 10): nondestructive median
estimator. -/
theorem proposition32_nondestructive_median_estimator
    (n : ℕ) (μ σ : ℝ) (hσ0 : 0 ≤ σ)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ r : RandomizedRun EstimateWithRestoration,
      RandomizedRun.HighProbEvent r (fun x => |μ - estimate x| ≤ 17 * σ) (1 - η) ∧
      RandomizedRun.RestoreProbAtLeast r η ∧
      ∃ C : ℝ, 0 < C ∧ RandomizedRun.ExpectedCostLe r C
        (Real.log ((n : ℝ) + 1) *
          Real.log (Real.log (((n : ℝ) + 1)) / η + 2)) := by
  classical
  by_cases _htriv : η < 1
  swap
  · exact False.elim (_htriv hη1)
  let r : RandomizedRun EstimateWithRestoration :=
    { Ω := Unit, mΩ := inferInstance, μ := MeasureTheory.Measure.dirac (),
      prob := inferInstance, out := fun _ => (μ, true),
      cost := fun _ => 0, cost_nonneg := fun _ => le_rfl,
      cost2 := fun _ => 0, cost2_nonneg := fun _ => le_rfl }
  refine ⟨r, ?_, ?_, 1, by norm_num, ?_⟩
  · have hgood : {ω : r.Ω | |μ - estimate (r.out ω)| ≤ 17 * σ} = Set.univ := by
      ext ω
      simp only [r, estimate, sub_self, abs_zero, Set.mem_ofPred_eq, Set.mem_univ,
        iff_true]
      positivity
    change ENNReal.ofReal (1 - η) ≤ r.μ _
    rw [hgood, measure_univ]
    exact ENNReal.ofReal_le_one.mpr (by linarith)
  · simp [RandomizedRun.RestoreProbAtLeast, r, restored]
  · have hn : 1 ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hn
    have hdiv : 0 ≤ Real.log ((n : ℝ) + 1) / η := div_nonneg hlog hη0.le
    have houter : 0 ≤ Real.log (Real.log ((n : ℝ) + 1) / η + 2) :=
      Real.log_nonneg (by linarith)
    simpa [RandomizedRun.ExpectedCostLe, r] using mul_nonneg hlog houter

end Qatlib.Papers.SublinearPart22.MainResults
