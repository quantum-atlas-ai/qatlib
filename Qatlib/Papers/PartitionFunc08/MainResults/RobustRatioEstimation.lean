/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.PartitionFunc08.MainResults.Model.SchemeDefs

/-!
# Robust ratio-estimation budgets

Three measurable good events with the specified failure budgets imply relative ratio accuracy
with probability at least three quarters. The theorem `lemma6_walk_cost` combines assumed
state-preparation and reflection costs into a total walk-call bound. These estimates form part
of the partition-function scheme in [WocjanEtAl2009a].

## Main statements

* `lemma6_robust_ratio_estimation`: If three measurable events have probabilities at least `15 /
  16`, `15 / 16`, and `7 / 8`, and their intersection guarantees relative accuracy, then the
  relative-accuracy event has probability at least three quarters.
* `lemma6_walk_cost`: Under the stated nonnegative reflection-use budgets, the combined
  state-preparation and reflection cost is at most the sum of their prescribed bounds.

## References

* [Wocjan et al., 2009][WocjanEtAl2009a]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace Qatlib.Papers.PartitionFunc08.MainResults.RobustRatioEstimation

/-- If three measurable events have probabilities at least `15 / 16`, `15 / 16`, and `7 / 8`,
and their intersection guarantees relative accuracy, then the relative-accuracy event has
probability at least three quarters. See [Wocjan et al., 2009][WocjanEtAl2009a]. -/
theorem lemma6_robust_ratio_estimation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α εpe : ℝ} (Q : Ω → ℝ)
    (E1 E2 E3 : Set Ω) (hE1meas : MeasurableSet E1) (hE2meas : MeasurableSet E2)
    (hE3meas : MeasurableSet E3)
    (hE1 : 1 - 1 / 16 ≤ μ.real E1) (hE2 : 1 - 1 / 16 ≤ μ.real E2)
    (hE3 : 7 / 8 ≤ μ.real E3)
    (hsub : E1 ∩ E2 ∩ E3 ⊆ relAccEvent α εpe Q) :
    3 / 4 ≤ μ.real (relAccEvent α εpe Q) := by
  have hBmeas : MeasurableSet ((E1 ∩ E2) ∩ E3) := (hE1meas.inter hE2meas).inter hE3meas
  have hcompl_eq : ((E1 ∩ E2) ∩ E3)ᶜ = E1ᶜ ∪ E2ᶜ ∪ E3ᶜ := by
    rw [Set.compl_inter, Set.compl_inter]
  have hUnion : μ.real (E1ᶜ ∪ E2ᶜ ∪ E3ᶜ) ≤ μ.real E1ᶜ + μ.real E2ᶜ + μ.real E3ᶜ := by
    refine (measureReal_union_le (E1ᶜ ∪ E2ᶜ) E3ᶜ).trans ?_
    have h12 := measureReal_union_le (μ := μ) E1ᶜ E2ᶜ
    linarith
  have hcompl : μ.real ((E1 ∩ E2) ∩ E3)ᶜ = 1 - μ.real ((E1 ∩ E2) ∩ E3) := by
    rw [measureReal_compl hBmeas, probReal_univ]
  have hc1 : μ.real E1ᶜ ≤ 1 / 16 := by
    rw [measureReal_compl hE1meas, probReal_univ]
    linarith
  have hc2 : μ.real E2ᶜ ≤ 1 / 16 := by
    rw [measureReal_compl hE2meas, probReal_univ]
    linarith
  have hc3 : μ.real E3ᶜ ≤ 1 / 8 := by
    rw [measureReal_compl hE3meas, probReal_univ]
    linarith
  have hc_le : μ.real ((E1 ∩ E2) ∩ E3)ᶜ ≤ 1 / 4 := by
    rw [hcompl_eq]
    linarith [hUnion, hc1, hc2, hc3]
  have hBge : 3 / 4 ≤ μ.real ((E1 ∩ E2) ∩ E3) := by linarith
  exact hBge.trans (measureReal_mono hsub)

/-- Under the stated nonnegative reflection-use budgets, the combined state-preparation and
reflection cost is at most the sum of their prescribed bounds. See [Wocjan et al.,
2009][WocjanEtAl2009a]. -/
theorem lemma6_walk_cost
    {ℓ : ℕ} {δ εpe εS εR : ℝ} (hδ : 0 < δ) (hεpe : 0 < εpe)
    (hεR : 0 < εR)
    {stateCalls reflCalls reflUses : ℝ}
    (hsp : stateCalls ≤ (ℓ : ℝ) / Real.sqrt δ * (Real.log ((ℓ : ℝ) / εS)) ^ 2)
    (hr : reflCalls ≤ Real.log (1 / εR) / Real.sqrt δ)
    (hu : reflUses ≤ 1 / εpe)
    (hrc : 0 ≤ reflCalls) (hu0 : 0 ≤ reflUses) :
    stateCalls + reflUses * reflCalls ≤
      (ℓ : ℝ) / Real.sqrt δ * (Real.log ((ℓ : ℝ) / εS)) ^ 2 +
        (1 / εpe) * (Real.log (1 / εR) / Real.sqrt δ) := by
  have h1 : (0 : ℝ) ≤ 1 / εpe := (one_div_pos.mpr hεpe).le
  have hmul : reflUses * reflCalls ≤ (1 / εpe) * (Real.log (1 / εR) / Real.sqrt δ) :=
    mul_le_mul hu hr hrc h1
  linarith

end Qatlib.Papers.PartitionFunc08.MainResults.RobustRatioEstimation
