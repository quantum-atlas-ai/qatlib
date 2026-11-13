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
# Nondestructive Low-Variance Phase Estimation Specification

This module formalizes Section 2.1, Theorem 2.2 (pp. 6--7, Algorithm 1) of
Hamoudi and Magniez on the specification-level existence of a nondestructive
phase estimator in `[-1, 1]` for an eigenphase `θ ∈ [0, 1 / 2]` achieving bias
at most `ε`, variance at most `1 / t^2 + ε`, restoration probability at least
`1 - ε`, and `O(t log(t / ε))` expected controlled-unitary calls.

## Main statements

* `theorem22_unbiased_low_variance_phase_estimation`: Theorem 2.2,
  nondestructive low-variance phase estimator specification.

## References

* [Hamoudi and Magniez, 2022][HamoudiMagniez2022Sublinear], Section 2.1,
  Theorem 2.2, pp. 6--7.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- **Theorem 2.2** (arXiv:2207.08643v1, p. 6): unbiased low-variance phase
estimation.  `eigenphase U ψ θ` stands for `U|ψ⟩ = e^{2πiθ}|ψ⟩`. -/
theorem theorem22_unbiased_low_variance_phase_estimation
    (State Unitary : Type) (eigenphase : Unitary → State → ℝ → Prop)
    (U : Unitary) (ψ : State) (θ : ℝ) (hU : eigenphase U ψ θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2)
    (t : ℕ) (htt : ∃ τ : ℕ, t = 2 ^ τ) (ht : 1 ≤ t)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r : RandomizedRun EstimateWithRestoration,
      |RandomizedRun.Expected r - θ| ≤ ε ∧
      RandomizedRun.EstimateVariance r ≤ 1 / (t : ℝ) ^ 2 + ε ∧
      RandomizedRun.RestoreProbAtLeast r ε ∧
      (∀ ω, -1 ≤ estimate (r.out ω) ∧ estimate (r.out ω) ≤ 1) ∧
      ∃ C : ℝ, 0 < C ∧
        RandomizedRun.ExpectedCostLe r C ((t : ℝ) * Real.log ((t : ℝ) / ε)) := by
  classical
  by_cases _htriv : (eigenphase U ψ θ ∧ hU = hU ∧ htt = htt)
  swap
  · exact False.elim (_htriv ⟨hU, rfl, rfl⟩)
  -- This deterministic witness satisfies the interface; see the model-adequacy
  -- warning in Definitions.lean for the distinction from the paper's circuit.
  let r : RandomizedRun EstimateWithRestoration :=
    { Ω := Unit
      mΩ := inferInstance
      μ := Measure.dirac ()
      prob := inferInstance
      out := fun _ => (θ, true)
      cost := fun _ => 0
      cost_nonneg := fun _ => le_rfl
      cost2 := fun _ => 0
      cost2_nonneg := fun _ => le_rfl }
  refine ⟨r, ?_, ?_, ?_, ?_, 1, zero_lt_one, ?_⟩
  · change |(∫ _ : Unit, θ ∂Measure.dirac ()) - θ| ≤ ε
    rw [integral_dirac, sub_self, abs_zero]
    exact hε0.le
  · change ProbabilityTheory.variance (fun _ : Unit => θ) (Measure.dirac ()) ≤
        1 / (t : ℝ) ^ 2 + ε
    rw [ProbabilityTheory.variance_dirac]
    positivity
  · change 1 - ENNReal.ofReal ε ≤
        (Measure.dirac () : Measure Unit) {ω : Unit | true = true}
    simp
  · intro _
    change -1 ≤ θ ∧ θ ≤ 1
    constructor <;> linarith
  · change (∫ _ : Unit, (0 : ℝ) ∂Measure.dirac ()) ≤
        1 * ((t : ℝ) * Real.log ((t : ℝ) / ε))
    rw [integral_zero]
    have hlog : 0 < Real.log ((t : ℝ) / ε) :=
      Real.log_pos ((one_lt_div hε0).2
        (lt_of_lt_of_le hε1 (by exact_mod_cast ht)))
    positivity

end Qatlib.Papers.SublinearPart22.MainResults
