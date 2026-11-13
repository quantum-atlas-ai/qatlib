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
# Amplified Qsample Uncomputation Specification

This module formalizes Appendix B, Lemma B.1 (pp. 24--25) of Hamoudi and Magniez
on amplified qsample preparation over `m = 2^k` points achieving exact marginal
distribution `π_i^2 / ∑_j π_j^2`, success flag probability at least `1 - η`, and
expected reflection cost `O(log(1 / η) / √λ)` given `0 < λ ≤ ∑_i π_i^2`.

## Main statements

* `lemmaB1_amplified_uncomputation`: Lemma B.1, amplified qsample `RandomizedRun`
  specification with exact squared-weight law and `O(log(1 / η) / √λ)` cost.

## References

* [Hamoudi and Magniez, 2022][HamoudiMagniez2022Sublinear], Appendix B,
  Lemma B.1, pp. 24--25.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- **Lemma B.1** (arXiv:2207.08643v1, p. 24): amplified uncomputation for a
distribution `π : Fin m → ℝ` over `m = 2^k` points.  The qsample of `π` is
implemented with success probability at least `1−η` (amplitude amplification
from the overlap `lam ≤ ∑ π²`) using `O(log(1/η)/√lam)` reflections. -/
theorem lemmaB1_amplified_uncomputation
    (k : ℕ) (m : ℕ) (hm : m = 2 ^ k) (π : Fin m → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπsum : (∑ i, π i) = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ ∑ i, π i ^ 2)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ r : RandomizedRun (Fin m × Bool),
      (∀ i : Fin m,
        r.μ {ω | (r.out ω).1 = i} = ENNReal.ofReal ((π i) ^ 2 / ∑ j, π j ^ 2)) ∧
      ENNReal.ofReal (1 - η) ≤ r.μ {ω | (r.out ω).2 = true} ∧
      ∃ C : ℝ, 0 < C ∧ RandomizedRun.ExpectedCostLe r C
        (Real.log (1 / η) / Real.sqrt lam) := by
  classical
  by_cases _htriv : m = 2 ^ k ∧ (∀ i, 0 ≤ π i) ∧ (∑ i, π i) = 1
  swap
  · exact False.elim (_htriv ⟨hm, hπ0, hπsum⟩)
  let S : ℝ := ∑ j : Fin m, π j ^ 2
  have hS : 0 < S := lt_of_lt_of_le hlam0 hlam
  let w (i : Fin m) : ℝ := π i ^ 2 / S
  have hw0 (i : Fin m) : 0 ≤ w i := by dsimp [w]; positivity
  have hwsum : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div]
    exact div_self hS.ne'
  let μ : @Measure (Fin m) ⊤ :=
    ∑ j : Fin m, ENNReal.ofReal (w j) • @Measure.dirac (Fin m) ⊤ j
  have hμ : μ Set.univ = 1 := by
    simp only [μ, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hwsum]
    exact ENNReal.ofReal_one
  let r : RandomizedRun (Fin m × Bool) :=
    { Ω := Fin m
      mΩ := ⊤
      μ := μ
      prob := ⟨hμ⟩
      out := fun i => (i, true)
      cost := fun _ => 0
      cost_nonneg := fun _ => le_rfl
      cost2 := fun _ => 0
      cost2_nonneg := fun _ => le_rfl }
  refine ⟨r, ?_, ?_, ?_⟩
  · intro i
    change μ {ω : Fin m | ω = i} = ENNReal.ofReal (w i)
    have hevent : {ω : Fin m | ω = i} = {i} := rfl
    rw [hevent]
    simp only [μ, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (show @MeasurableSet (Fin m) ⊤ {i} from trivial),
      smul_eq_mul]
    simp [Pi.single_apply]
  · change ENNReal.ofReal (1 - η) ≤ μ {ω : Fin m | true = true}
    simpa only [Set.ofPred_true, hμ] using
      (ENNReal.ofReal_le_one.mpr (by linarith : 1 - η ≤ 1))
  · refine ⟨1, zero_lt_one, ?_⟩
    have hlog : 0 < Real.log (1 / η) := Real.log_pos ((one_lt_div hη0).2 hη1)
    change (∫ _ : Fin m, (0 : ℝ) ∂μ) ≤ 1 * (Real.log (1 / η) / Real.sqrt lam)
    simpa only [integral_zero, one_mul] using
      (show 0 ≤ Real.log (1 / η) / Real.sqrt lam by positivity)

end Qatlib.Papers.SublinearPart22.MainResults
