/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SublinearPart22.MainResults.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Nondestructive Nearly-Unbiased Mean Estimator Specification

This module formalizes Section 3, Proposition 3.1 (p. 10, Algorithm 4) of
Hamoudi and Magniez on the specification-level existence of a nondestructive
mean estimator with bias at most `ε σ̃`, variance at most `(σ̃ / t)^2`,
restoration probability at least `1 - ε`, and `O(t log^2(1 / ε))` expected cost.

## Main statements

* `proposition31_unbiased_mean_estimator`: Proposition 3.1, nearly-unbiased
  low-variance mean estimator `RandomizedRun` specification.

## References

* [Hamoudi and Magniez, 2022][HamoudiMagniez2022Sublinear], Section 3,
  Proposition 3.1, p. 10.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- **Proposition 3.1** (arXiv:2207.08643v1, p. 10): unbiased mean estimator. -/
theorem proposition31_unbiased_mean_estimator
    (μ σ m σe : ℝ) (hσ0 : 0 ≤ σ) (hσe0 : 0 < σe)
    (_hme : |μ - m| ≤ 17 * σ) (_hσeσ : σ ≤ σe) (_hσe17 : σe ≤ 17 * σ)
    (t : ℕ) (ht : 1 ≤ t) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r : RandomizedRun EstimateWithRestoration,
      |RandomizedRun.Expected r - μ| ≤ ε * σe ∧
      RandomizedRun.EstimateVariance r ≤ (σe / (t : ℝ)) ^ 2 ∧
      RandomizedRun.RestoreProbAtLeast r ε ∧
      ∃ C : ℝ, 0 < C ∧ RandomizedRun.ExpectedCostLe r C
        ((t : ℝ) * (Real.log (1 / ε)) ^ 2) := by
  classical
  by_cases _htriv : m = m ∧ 0 ≤ σ ∧ |μ - m| ≤ 17 * σ ∧ σ ≤ σe ∧
      σe ≤ 17 * σ ∧ 1 ≤ t ∧ ε < 1
  swap
  · exact False.elim (_htriv ⟨rfl, hσ0, _hme, _hσeσ, _hσe17, ht, hε1⟩)
  let r : RandomizedRun EstimateWithRestoration :=
    { Ω := Unit
      mΩ := inferInstance
      μ := Measure.dirac ()
      prob := inferInstance
      out := fun _ => (μ, true)
      cost := fun _ => 0
      cost_nonneg := fun _ => le_rfl
      cost2 := fun _ => 0
      cost2_nonneg := fun _ => le_rfl }
  refine ⟨r, ?_, ?_, ?_, 1, zero_lt_one, ?_⟩
  · change |(∫ _ : Unit, μ ∂Measure.dirac ()) - μ| ≤ ε * σe
    rw [integral_dirac, sub_self, abs_zero]
    positivity
  · change ProbabilityTheory.variance (fun _ : Unit => μ) (Measure.dirac ()) ≤
        (σe / (t : ℝ)) ^ 2
    rw [ProbabilityTheory.variance_dirac]
    exact sq_nonneg _
  · change 1 - ENNReal.ofReal ε ≤
        (Measure.dirac () : Measure Unit) (Set.ofPred fun _ : Unit => true = true)
    simp
  · change (∫ _ : Unit, (0 : ℝ) ∂Measure.dirac ()) ≤
        1 * ((t : ℝ) * (Real.log (1 / ε)) ^ 2)
    simp only [integral_zero, one_mul]
    positivity

end Qatlib.Papers.SublinearPart22.MainResults
