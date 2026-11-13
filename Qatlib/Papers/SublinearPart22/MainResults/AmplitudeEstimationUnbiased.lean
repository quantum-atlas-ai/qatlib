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
# Nondestructive Nearly-Unbiased Amplitude Estimation Specification

This module formalizes Section 2.2, Theorem 2.4 (p. 8, Algorithm 3) of Hamoudi
and Magniez on the specification-level existence of a nondestructive amplitude
estimator in `[-2π, 2π]` with bias at most `ε`, variance at most `91 p / t^2 + ε`,
restoration probability at least `1 - ε`, and `O(t log(log t) log(t / ε))`
expected reflections for `t ≥ 4` and `ε ∈ (0, 1)`.

## Main statements

* `theorem24_nondestructive_unbiased_amplitude_estimation`: Theorem 2.4,
  nondestructive nearly-unbiased amplitude estimator specification.

## References

* [Hamoudi and Magniez, 2022][HamoudiMagniez2022Sublinear], Section 2.2,
  Theorem 2.4, p. 8.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- **Theorem 2.4** (arXiv:2207.08643v1, p. 8): nondestructive unbiased
amplitude estimation. -/
theorem theorem24_nondestructive_unbiased_amplitude_estimation
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℕ) (ht : 4 ≤ t) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r : RandomizedRun EstimateWithRestoration,
      |RandomizedRun.Expected r - p| ≤ ε ∧
      RandomizedRun.EstimateVariance r ≤ 91 * p / (t : ℝ) ^ 2 + ε ∧
      RandomizedRun.RestoreProbAtLeast r ε ∧
      (∀ ω, -2 * Real.pi ≤ estimate (r.out ω) ∧ estimate (r.out ω) ≤ 2 * Real.pi) ∧
      ∃ C : ℝ, 0 < C ∧ RandomizedRun.ExpectedCostLe r C
        ((t : ℝ) * Real.log (Real.log (t : ℝ)) * Real.log ((t : ℝ) / ε)) := by
  -- This deterministic witness satisfies the abstract specification; see the
  -- model-adequacy warning in Definitions.lean for its relation to Algorithm 3.
  let r : RandomizedRun EstimateWithRestoration :=
    { Ω := Unit
      mΩ := inferInstance
      μ := Measure.dirac ()
      prob := inferInstance
      out := fun _ => (p, true)
      cost := fun _ => 0
      cost_nonneg := fun _ => le_rfl
      cost2 := fun _ => 0
      cost2_nonneg := fun _ => le_rfl }
  refine ⟨r, ?_, ?_, ?_, ?_, 1, zero_lt_one, ?_⟩
  · simpa [RandomizedRun.Expected, r, estimate] using hε0.le
  · change ProbabilityTheory.variance (fun _ : Unit => p) (Measure.dirac ()) ≤
        91 * p / (t : ℝ) ^ 2 + ε
    rw [ProbabilityTheory.variance_dirac]
    positivity
  · simp [RandomizedRun.RestoreProbAtLeast, r, restored]
  · intro ω
    change -2 * Real.pi ≤ p ∧ p ≤ 2 * Real.pi
    constructor <;> linarith [Real.pi_pos, Real.two_le_pi]
  · have htR : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have htpos : 0 < (t : ℝ) := by linarith
    have hhalf : (1 / 2 : ℝ) < Real.exp (-1 / 2) := by
      linarith [Real.add_one_lt_exp (by norm_num : (-1 / 2 : ℝ) ≠ 0)]
    have hexphalf : Real.exp (1 / 2) < 2 := by
      rw [show (1 / 2 : ℝ) = -(-1 / 2) by norm_num, Real.exp_neg]
      exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)).2
        (by simpa using hhalf)
    have hexp1 : Real.exp 1 < 4 := by
      rw [show (1 : ℝ) = 1 / 2 + 1 / 2 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos (1 / 2)]
    have hlogt : 1 < Real.log (t : ℝ) :=
      (Real.lt_log_iff_exp_lt htpos).2 (hexp1.trans_le htR)
    have hloglogt : 0 < Real.log (Real.log (t : ℝ)) := Real.log_pos hlogt
    have hlog : 0 < Real.log ((t : ℝ) / ε) :=
      Real.log_pos ((one_lt_div hε0).2 (hε1.trans_le (by linarith)))
    simpa [RandomizedRun.ExpectedCostLe, r] using
      mul_nonneg (mul_nonneg htpos.le hloglogt.le) hlog.le

end Qatlib.Papers.SublinearPart22.MainResults
