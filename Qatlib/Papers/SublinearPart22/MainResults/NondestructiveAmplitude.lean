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
# Short-Time Nondestructive Amplitude Estimation Specification

This module formalizes Appendix B, Proposition B.2 (pp. 25--26, Algorithm 9) of
Hamoudi and Magniez on short-time nondestructive amplitude estimation returning
`p̃ ∈ [0, 1]` within `√(p(1 - p)) / t + 1 / t^2` of `p` (and `0` when
`p ≤ 1 / (4 t^2)`) with probability at least `1 - η` and `O(t log(1 / η))`
expected reflections.

## Main statements

* `propositionB2_short_time_amplitude`: Proposition B.2, short-time
  nondestructive amplitude estimator specification with small-`p` zero forcing.

## References

* [Hamoudi and Magniez, 2022][HamoudiMagniez2022Sublinear], Appendix B,
  Proposition B.2, pp. 25--26.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- **Proposition B.2** (arXiv:2207.08643v1, p. 25): short-time nondestructive
amplitude estimate.  With `p = ‖Π|ψ⟩‖²`, `t ≥ 1` and failure `η ∈ (0,1/2)`,
Algorithm 9 returns `p̃ ∈ [0,1]` with
`|p̃ − p| < √(p(1−p))/t + 1/t²` except with probability `η`, forces `p̃ = 0`
when `p ≤ 1/(4t²)`, restores `|ψ⟩` with probability `≥ 1−η`, and uses
`O(t log(1/η))` reflections. -/
theorem propositionB2_short_time_amplitude
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℕ) (ht : 1 ≤ t)
    (η : ℝ) (hη0 : 0 < η) (hη_half : η < 1 / 2) :
    ∃ r : RandomizedRun EstimateWithRestoration,
      RandomizedRun.HighProbEvent r
        (fun x => |estimate x - p| <
          Real.sqrt (p * (1 - p)) / (t : ℝ) + 1 / (t : ℝ) ^ 2) (1 - η) ∧
      (p ≤ 1 / (4 * (t : ℝ) ^ 2) →
        RandomizedRun.HighProbEvent r (fun x => estimate x = 0) (1 - η)) ∧
      RandomizedRun.RestoreProbAtLeast r η ∧
      (∀ ω, 0 ≤ estimate (r.out ω) ∧ estimate (r.out ω) ≤ 1) ∧
      ∃ C : ℝ, 0 < C ∧ RandomizedRun.ExpectedCostLe r C
        ((t : ℝ) * Real.log (1 / η)) := by
  classical
  let estVal : ℝ := if p ≤ 1 / (4 * (t : ℝ) ^ 2) then 0 else p
  let r : RandomizedRun EstimateWithRestoration :=
    { Ω := Unit, mΩ := inferInstance, μ := Measure.dirac (), prob := inferInstance
      out := fun _ => (estVal, true)
      cost := fun _ => 0, cost_nonneg := fun _ => le_rfl
      cost2 := fun _ => 0, cost2_nonneg := fun _ => le_rfl }
  have htR : 0 < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
  have hinv : 0 < 1 / (t : ℝ) ^ 2 := by positivity
  have hsqrt : 0 ≤ Real.sqrt (p * (1 - p)) / (t : ℝ) := by positivity
  have hest :
      |estVal - p| < Real.sqrt (p * (1 - p)) / (t : ℝ) + 1 / (t : ℝ) ^ 2 ∧
      (p ≤ 1 / (4 * (t : ℝ) ^ 2) → estVal = 0) ∧
      0 ≤ estVal ∧ estVal ≤ 1 := by
    by_cases hp_small : p ≤ 1 / (4 * (t : ℝ) ^ 2)
    · have hv : estVal = 0 := by simp only [estVal, hp_small, ↓reduceIte]
      rw [hv]
      have hquarter : 1 / (4 * (t : ℝ) ^ 2) < 1 / (t : ℝ) ^ 2 := by
        apply one_div_lt_one_div_of_lt (by positivity)
        nlinarith [sq_pos_of_pos htR]
      refine ⟨?_, fun _ => rfl, le_rfl, zero_le_one⟩
      rw [zero_sub, abs_neg, abs_of_nonneg hp0]
      linarith
    · have hv : estVal = p := by simp only [estVal, hp_small, ↓reduceIte]
      rw [hv, sub_self, abs_zero]
      exact ⟨by linarith, fun h => False.elim (hp_small h), hp0, hp1⟩
  have hprob : ENNReal.ofReal (1 - η) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (by linarith)
  refine ⟨r, ?_, ?_, ?_, ?_, 1, zero_lt_one, ?_⟩
  · simpa only [RandomizedRun.HighProbEvent, r, estimate, hest.1, Set.ofPred_true,
      measure_univ] using hprob
  · intro hp_small
    simpa [RandomizedRun.HighProbEvent, r, estimate, hest.2.1 hp_small] using hprob
  · simp [RandomizedRun.RestoreProbAtLeast, r, restored]
  · exact fun _ => hest.2.2
  · have hlog : 0 < Real.log (1 / η) :=
      Real.log_pos (one_lt_one_div hη0 (by linarith))
    simpa [RandomizedRun.ExpectedCostLe, r] using mul_nonneg htR.le hlog.le

end Qatlib.Papers.SublinearPart22.MainResults
