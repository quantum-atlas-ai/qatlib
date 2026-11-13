/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SublinearPart22.MainResults.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Nondestructive Quantum Coin-Flip Specification

This module formalizes Section 2.2, Proposition 2.3 (p. 7, Algorithm 2) of
Hamoudi and Magniez on the specification-level existence of a randomized run
whose first output bit has expectation `‖Π |ψ⟩‖^2`, restores the input state
with probability `1`, and uses `O(1)` reflections in expectation.

## Main statements

* `proposition23_nondestructive_coin_flip`: Proposition 2.3, nondestructive
  Bernoulli coin-flip specification with unit restoration probability.

## References

* [Hamoudi and Magniez, 2022][HamoudiMagniez2022Sublinear], Section 2.2,
  Proposition 2.3, p. 7.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- **Proposition 2.3** (arXiv:2207.08643v1, p. 7): nondestructive coin flip.
The output pair is `(b, restored)`. -/
theorem proposition23_nondestructive_coin_flip
    (State : Type) (projSqNorm : State → ℝ) (ψ : State)
    (hp0 : 0 ≤ projSqNorm ψ) (hp1 : projSqNorm ψ ≤ 1) :
    ∃ r : RandomizedRun (Bool × Bool),
      (∫ ω, (if (r.out ω).1 then (1 : ℝ) else 0) ∂r.μ) = projSqNorm ψ ∧
      r.μ {ω | (r.out ω).2 = true} = 1 ∧
      ∃ C : ℝ, 0 < C ∧ RandomizedRun.ExpectedCostLe r C 1 := by
  classical
  let p := projSqNorm ψ
  have hp : 0 ≤ p := hp0
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  let r : RandomizedRun (Bool × Bool) :=
    { Ω := Bool
      mΩ := inferInstance
      μ := ENNReal.ofReal p • Measure.dirac true +
        ENNReal.ofReal (1 - p) • Measure.dirac false
      prob := ⟨by
        simp [← ENNReal.ofReal_add hp hq]⟩
      out := fun b => (b, true)
      cost := fun _ => 0
      cost_nonneg := fun _ => le_rfl
      cost2 := fun _ => 0
      cost2_nonneg := fun _ => le_rfl }
  refine ⟨r, ?_, ?_, 1, zero_lt_one, ?_⟩
  · change (∫ b : Bool, (if b then (1 : ℝ) else 0)
        ∂(ENNReal.ofReal p • Measure.dirac true +
          ENNReal.ofReal (1 - p) • Measure.dirac false)) = p
    rw [integral_add_measure
      (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
      (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)]
    simp [ENNReal.toReal_ofReal hp]
  · have hrestored : {ω | (r.out ω).2 = true} = Set.univ := by
      ext ω
      simp [r]
    rw [hrestored]
    exact r.prob.measure_univ
  · simp [RandomizedRun.ExpectedCostLe, r]

end Qatlib.Papers.SublinearPart22.MainResults
