/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Tactic

@[expose] public section


/-!
# Missing oracle semantics in the legacy estimator model

The old record permits an exact-gradient Dirac law with zero query cost.
It therefore cannot support the paper's quantum query lower bounds.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GevreyGrad19.MainResults

open Qatlib.Papers.GevreyGrad19.MainResults

/-- The legacy record allows exact gradient output with an unrelated zero cost field. -/
def omniscient (d : ℕ) : GradientEstimator d where
  law f := MeasureTheory.Measure.dirac (grad f 0)
  queryCost _ := 0

/-- This zero-cost record succeeds with probability one at every nonnegative precision. -/
theorem omniscient_success (d : ℕ) (f : (Fin d → ℝ) → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    successProb (omniscient d) f ε = 1 := by
  apply MeasureTheory.Measure.dirac_apply_of_mem
  simpa [loneError] using hε

/-- The omniscient record satisfies the old estimator predicate on any function class. -/
theorem omniscient_estimator (d : ℕ) (f : Set ((Fin d → ℝ) → ℝ))
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : p ≤ 1) :
    IsGradientEstimator (omniscient d) f ε p := by
  intro g _hg
  rw [omniscient_success d g ε hε]
  exact (ENNReal.ofReal_le_one).mpr hp

/-- The literal one-dimensional query lower-bound conclusion fails for this valid old record. -/
theorem lower_bound_counterexample :
    IsGradientEstimator (omniscient 1) (Gevrey 1 1 0 Set.univ) (1 / 1000) (17 / 18) ∧
    ¬ ∃ f ∈ Gevrey 1 1 0 Set.univ,
      (1 : ℝ) * (1 : ℝ) ^ (3 / 2 : ℝ) / (876 * (1 / 1000 : ℝ)) ≤
        queryCost (omniscient 1) f := by
  constructor
  · exact omniscient_estimator _ _ _ _ (by norm_num) (by norm_num)
  · simp [queryCost, omniscient]

end Qatlib.Papers.GevreyGrad19.MainResults
