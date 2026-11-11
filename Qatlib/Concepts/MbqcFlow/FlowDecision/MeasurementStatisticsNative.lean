/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNativeDefs

/-!
# Independent measurement statistics and campaign costs

Collects the independent-outcome moment identities and the operation bounds for
`NativeCampaign`. The theorem `clause6_complete` combines product-law factorization, unbiased
pairwise U-statistics, higher statistic moments, and the variance interpretation of diagonal
bias.

The theorem `thresholdGoal_complete` gives quantum operation counts and machine-dependent time
and space formulas for the counted Pauli campaign. The measurement-statistic setting is related
to [HuangKuengPreskill2020].

## Main statements

* `clause6_complete`: joint-law, moment, and pairwise-statistic identities.
* `thresholdGoal_complete`: campaign counts and bit-cost formulas.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNative
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
namespace MeasurementStatisticsNative

open Matrix
open scoped Classical BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

/-- For at least two samples, collects product-law factorization, independent and diagonal
kernel expectations, pairwise U-statistic unbiasedness, higher moment identities, and the
variance formula for diagonal product bias. -/
theorem clause6_complete (E : FinitePOVM O D) (hM : Function.Bijective (povmMeasurementMap E))
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (A : Operator D) (h : O → O → ℝ)
    {n : ℕ} (hn : 2 ≤ n) :

    (∀ o₁ o₂ : O,
      (povmJointLaw E ρ hρ).prob (o₁, o₂)
        = (povmRecordLaw E ρ hρ).prob o₁ * (povmRecordLaw E ρ hρ).prob o₂) ∧

    (∀ f g : O → ℝ,
      (povmJointLaw E ρ hρ).expect (fun o => f o.1 * g o.2)
        = (povmRecordLaw E ρ hρ).expect f * (povmRecordLaw E ρ hρ).expect g) ∧

    (∀ (i j : Fin n), i ≠ j →
      (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω j)
        = povmKernelMeanIndependent E ρ hρ h) ∧
      (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω i)
        = povmKernelMeanDiagonal E ρ hρ h)) ∧

    (povmKernelMeanDiagonal E ρ hρ h - povmKernelMeanIndependent E ρ hρ h
      = (povmJointLaw E ρ hρ).expect (fun o => h o.1 o.1 - h o.1 o.2)) ∧

    ((∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * povmUStatistic h ω)
      = povmKernelMeanIndependent E ρ hρ h) ∧

    (∀ k : ℕ,
      (povmRecordLaw E ρ hρ).expect (fun o => (povmStatistic E hM A o) ^ k)
        = (Matrix.trace (povmMomentEffectK E hM A k * ρ)).re) ∧

    (povmKernelMeanDiagonal E ρ hρ
        (fun o₁ o₂ => povmStatistic E hM A o₁ * povmStatistic E hM A o₂)
      - povmKernelMeanIndependent E ρ hρ
        (fun o₁ o₂ => povmStatistic E hM A o₁ * povmStatistic E hM A o₂)
      = (povmRecordLaw E ρ hρ).expect (fun o => (povmStatistic E hM A o) ^ 2)
        - (povmRecordLaw E ρ hρ).expect (povmStatistic E hM A) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o₁ o₂
    exact povmJointLaw_prob E ρ hρ o₁ o₂
  · intro f g
    exact povmJointLaw_expect_separable E ρ hρ f g
  · intro i j hij
    exact ⟨povm_expect_two_records E ρ hρ h i j hij,
      povm_expect_one_record E ρ hρ h i⟩
  · exact povmKernelMean_bias E ρ hρ h
  · exact povm_expect_UStatistic E ρ hρ h hn
  · intro k
    exact povm_expect_statistic_pow E hM ρ hρ A k
  · exact povmKernelMean_bias_variance E ρ hρ A hM

/-- Collects the exact quantum and classical counts, comparison bounds, and machine-dependent
bit-time and peak-space formulas of a native Pauli campaign. -/
theorem thresholdGoal_complete {K L : ℕ} (c : NativeCampaign K L) (m : NativeMachine) :

    (nativeLedger c m).copies = K * L ∧
    (nativeLedger c m).gates = 2 * (K * L) ∧
    (nativeLedger c m).measurements = K * L ∧
    (nativeLedger c m).queries = 0 ∧

    (nativeLedger c m).axisDraws = (campaignFlatten c.records).length ∧

    (nativeLedger c m).tableReads = (campaignFlatten c.records).length ∧
    (nativeLedger c m).statisticReads = (campaignFlatten c.records).length ∧
    (nativeLedger c m).rationalAdditions = (campaignFlatten c.records).length ∧
    (nativeLedger c m).medianComparisons ≤ K * K ∧

    (nativeLedger c m).axisComparisons
        ≤ (campaignFlatten c.records).length
            * (nativeAxisTable.length + nativeAxisTable.length) ∧

    (nativeLedger c m).bitTime
        = (nativeLedger c m).axisDraws * m.axisDrawBits
          + (nativeLedger c m).axisComparisons * m.comparisonBits
          + (nativeLedger c m).tableReads * (m.addressBits + m.wordBits)
          + (nativeLedger c m).statisticReads * m.wordBits
          + (nativeLedger c m).rationalAdditions * m.additionBits
          + (nativeLedger c m).medianComparisons * m.comparisonBits ∧
    (nativeLedger c m).peakSpace
        = (campaignFlatten c.records).length * m.recordBits
          + K * m.wordBits + K * m.wordBits := by
  exact nativeLedger_spec c m

end MeasurementStatisticsNative
end Qatlib.Concepts.MbqcFlow.FlowDecision
