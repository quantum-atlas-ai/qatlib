/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SublinearPart22.MainResults.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Nondestructive Product-of-Means Estimator Specification

This module formalizes Section 3.2, Theorem 3.3 (pp. 12--14) of Hamoudi and
Magniez on the specification-level existence of a nondestructive estimator for
the product `∏_i m_i` of `ℓ` bounded means in `[0, B]` achieving relative error
at most `ε` with probability at least `2 / 3`.

## Main statements

* `theorem33_nondestructive_product_estimator`: Theorem 3.3, product-of-means
  `RandomizedRun` specification and primary/secondary expected-cost bounds.

## References

* [Hamoudi and Magniez, 2022][HamoudiMagniez2022Sublinear], Section 3.2,
  Theorem 3.3, pp. 12--14.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- **Theorem 3.3** (arXiv:2207.08643v1, p. 12): nondestructive estimator for a
product of `ℓ` means.  The vector `m : Fin ℓ → ℝ` holds the true means, `B` a
common known upper bound. -/
theorem theorem33_nondestructive_product_estimator
    (ℓ : ℕ) (m : Fin ℓ → ℝ) (B : ℝ) (hB : 0 < B)
    (hm : ∀ i, 0 ≤ m i ∧ m i ≤ B)
    (n : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r : RandomizedRun ℝ,
      RandomizedRun.HighProbEvent r
        (fun v => |v - ∏ i, m i| ≤ ε * ∏ i, m i) (2 / 3) ∧
      (∃ C : ℝ, 0 < C ∧ RandomizedRun.ExpectedCostLe r C (B * 1)) ∧
      (∃ C : ℝ, 0 < C ∧ RandomizedRun.ExpectedCost2Le r C
        (B ^ 2 * (ℓ : ℝ) ^ (3 / 2 : ℝ) / ε +
          B * (ℓ : ℝ) * Real.log ((n : ℝ) + 1))) := by
  classical
  by_cases _htriv : ε < 1
  swap
  · exact False.elim (_htriv hε1)
  let r : RandomizedRun ℝ :=
    { Ω := Unit
      mΩ := inferInstance
      μ := Measure.dirac ()
      prob := inferInstance
      out := fun _ => ∏ i, m i
      cost := fun _ => 0
      cost_nonneg := fun _ => le_rfl
      cost2 := fun _ => 0
      cost2_nonneg := fun _ => le_rfl }
  have hprod : 0 ≤ ∏ i, m i := Finset.prod_nonneg fun i _ => (hm i).1
  have hgood : |(∏ i, m i) - ∏ i, m i| ≤ ε * ∏ i, m i := by
    simpa only [sub_self, abs_zero] using mul_nonneg hε0.le hprod
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
  refine ⟨r, ?_, ⟨1, by norm_num, ?_⟩, ⟨1, by norm_num, ?_⟩⟩
  · change ENNReal.ofReal (2 / 3 : ℝ) ≤
      (Measure.dirac ()) {_ω : Unit | |(∏ i, m i) - ∏ i, m i| ≤ ε * ∏ i, m i}
    simp only [hgood, Set.ofPred_true, measure_univ]
    exact ENNReal.ofReal_le_one.mpr (by norm_num)
  · simpa [RandomizedRun.ExpectedCostLe, r] using hB.le
  · have hscale : 0 ≤ B ^ 2 * (ℓ : ℝ) ^ (3 / 2 : ℝ) / ε +
        B * (ℓ : ℝ) * Real.log ((n : ℝ) + 1) := by positivity
    simpa [RandomizedRun.ExpectedCost2Le, r] using hscale

end Qatlib.Papers.SublinearPart22.MainResults
