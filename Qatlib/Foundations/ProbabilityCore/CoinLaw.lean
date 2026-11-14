/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Bernoulli probability mass functions from Bernoulli measures

`bernoulli` presents Mathlib's measure-valued Bernoulli law as a probability mass
function on `Bool`. Its point-mass formula supports finite sums and existing
`PMF.bind` and `PMF.map` constructions. `bernoulli_toMeasure` identifies the
result with the original measure. These are distributional identities; they do
not describe random-bit consumption or an implementation's running time.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Qatlib.Foundations.ProbabilityCore.CoinLaw

/-- The probability mass function assigning mass `p` to `true` and `1 - p` to
`false`, obtained from Mathlib's Bernoulli measure. -/
noncomputable def bernoulli (p : ℝ≥0) (hp : p ≤ 1) : PMF Bool :=
  (ProbabilityTheory.bernoulliMeasure true false
    (⟨(p : ℝ), p.coe_nonneg, by exact_mod_cast hp⟩ : unitInterval)).toPMF

/-- The two point masses of the Bernoulli probability mass function. -/
theorem bernoulli_apply {p : ℝ≥0} (hp : p ≤ 1) (b : Bool) :
    bernoulli p hp b = cond b (p : ℝ≥0∞) ((1 - p : ℝ≥0) : ℝ≥0∞) := by
  have hparam : unitInterval.toNNReal
      (⟨(p : ℝ), p.coe_nonneg, by exact_mod_cast hp⟩ : unitInterval) = p := rfl
  have hsym : unitInterval.toNNReal (unitInterval.symm
      (⟨(p : ℝ), p.coe_nonneg, by exact_mod_cast hp⟩ : unitInterval)) = 1 - p := by
    apply NNReal.coe_injective
    simp [NNReal.coe_sub hp]
  cases b <;> simp [bernoulli, MeasureTheory.Measure.toPMF_apply, hparam, hsym]

/-- Converting the probability mass function back to a measure recovers the
native Bernoulli measure. -/
theorem bernoulli_toMeasure (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulli p hp).toMeasure = ProbabilityTheory.bernoulliMeasure true false
      (⟨(p : ℝ), p.coe_nonneg, by exact_mod_cast hp⟩ : unitInterval) :=
  MeasureTheory.Measure.toPMF_toMeasure _

end Qatlib.Foundations.ProbabilityCore.CoinLaw
