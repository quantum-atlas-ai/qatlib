/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.FairBitRecords.RandomBitsDefs

/-!
# Fair-bit sampling and measurement probabilities

This module records the uniform accepted-label masses, rejected mass, and per-attempt charge of
finite fair-bit sampling. It also proves that a POVM distribution with unequal outcome
probabilities cannot have the same fair-bit atom mass at every outcome. Measurement and
classical randomness are discussed in [NielsenChuang2010].

## Main statements

* `clause23_endpoint`: collects the fair-bit sampling identities.
* `clause24_born_not_fair_bit`: distinguishes unequal Born probabilities from a common atom
  mass.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.ShadowModels.FairBitRecords
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.ShadowModels.FairBitRecords

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- When `m ≤ 2 ^ k`, each accepted label of the finite-coin transition has mass `fairBitMass
k`, and its retry state has mass `fairBitRejectedMass k m`. -/
theorem clause23_fair_bit_uniform (k m : ℕ) (hm : m ≤ 2 ^ k) :
    (∀ i : Fin m, finiteCoinNext k m () (Sum.inl i) = fairBitMass k) ∧
    finiteCoinNext k m () (Sum.inr ()) = fairBitRejectedMass k m := by
  have h := finite_coin_step_distribution k m hm
  exact ⟨fun i => h.1 i, h.2⟩

/-- The fair-bit program uses `finiteCoinNext` as its transition law and charges exactly `k` per
attempt. -/
theorem clause23_fair_bit_program {D E : ℕ} (k m : ℕ) {X : Type} [Fintype X]
    (I : Instrument X D E) :
    (fairBitProgram k m I).next () = finiteCoinNext k m () ∧
    (fairBitProgram k m I).cost () = k :=
  ⟨rfl, rfl⟩

/-- If two POVM outcome probabilities differ, at least one outcome probability differs from the
common fair-bit atom mass. -/
theorem clause24_born_not_fair_bit {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (E : FinitePOVM O D) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (k m : ℕ) (hm : m ≤ 2 ^ k)
    (hne : ∃ o₁ o₂ : O,
      (povmRecordLaw E ρ hρ).prob o₁ ≠ (povmRecordLaw E ρ hρ).prob o₂) :
    ∃ o : O, (povmRecordLaw E ρ hρ).prob o ≠ fairBitMassReal k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨o₁, o₂, hdiff⟩ := hne
  exact hdiff ((hcon o₁).trans (hcon o₂).symm)

/-- Collects the accepted and rejected finite-coin masses, the fair-bit program transition and
cost, and the reciprocal-power-of-two formula for `fairBitMass`. -/
theorem clause23_endpoint :
    (∀ (k m : ℕ) (hm : m ≤ 2 ^ k),
      (∀ i : Fin m, finiteCoinNext k m () (Sum.inl i) = fairBitMass k) ∧
      finiteCoinNext k m () (Sum.inr ()) = fairBitRejectedMass k m) ∧
    (∀ {D E : ℕ} (k m : ℕ) {X : Type} [Fintype X] (I : Instrument X D E),
      (fairBitProgram k m I).next () = finiteCoinNext k m () ∧
      (fairBitProgram k m I).cost () = k) ∧
    (∀ (k : ℕ), fairBitMass k = ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k m hm
    exact clause23_fair_bit_uniform k m hm
  · intro D E k m X inst I
    exact clause23_fair_bit_program k m I
  · intro k
    rfl

/-- A POVM law with unequal outcome probabilities has an outcome whose probability differs from
the uniform fair-bit atom mass. -/
theorem clause24_endpoint :
    (∀ {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
      (E : FinitePOVM O D) (ρ : Operator D) (hρ : IsDensityOperator ρ)
      (k m : ℕ) (hm : m ≤ 2 ^ k)
      (hne : ∃ o₁ o₂ : O,
        (povmRecordLaw E ρ hρ).prob o₁ ≠ (povmRecordLaw E ρ hρ).prob o₂),
      ∃ o : O, (povmRecordLaw E ρ hρ).prob o ≠ fairBitMassReal k) := by
  intro O instF instD D E ρ hρ k m hm hne
  exact clause24_born_not_fair_bit E ρ hρ k m hm hne

end Qatlib.Concepts.MixedInstrument.ClockBridge
