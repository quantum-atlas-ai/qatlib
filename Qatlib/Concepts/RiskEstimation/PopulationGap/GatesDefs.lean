/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.SimTaylorDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GibbsMetropolisDefs
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# Gate synthesis and implementation resource specifications

This module defines specifications for finite gate synthesis, greatest common divisor resource
accounting, live workspace schedules, and dyadic preparation precision. `UnifiedSynthesis`
separates approximation correctness from word length bounds, while `IntegerBitGcd` records
machine data and arithmetic costs. These specifications support the circuit resource framework
described in [NielsenChuang2010].

## Main definitions

* `UnifiedSynthesis.Correct`: basis state approximation by legal finite gate words.
* `gcdLedgersSeparate`: separate Euclidean iteration, bit operation, and space costs.
* `SpaceSchedule.peakSpace`: maximum recorded live word count times word length.
* `PrepareDigits.roundComplex`: componentwise dyadic quantization.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Concepts.RiskEstimation.PopulationGap Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib.Concepts.RiskEstimation.PopulationGap Matrix
open scoped BigOperators Classical

/-- A generator of finite gate words for matrices on `w` qubits, together with a gate budget
indexed by inverse precision. -/
structure UnifiedSynthesis (w : ℕ) where

  generate : Matrix (Reg w) (Reg w) ℂ → ℝ → List FiniteGateCode

  gateBudget : ℕ → ℕ

/-- Requires legal generated words whose outputs on every computational basis state approximate
the corresponding unitary image with squared Euclidean error at most `ε ^ 2`. -/
def UnifiedSynthesis.Correct (w : ℕ) (S : UnifiedSynthesis w) : Prop :=
  ∀ (U : Matrix (Reg w) (Reg w) ℂ), U ∈ Matrix.unitaryGroup (Reg w) ℂ →
    ∀ (ε : ℝ), 0 < ε →
      finiteWordLegal w (S.generate U ε) = true ∧
        ∀ r : Reg w, ∃ φ : QState (Reg w),
          finiteWordRun w (S.generate U ε) (Ket r) = some φ ∧
            ∑ i, ‖φ i - (U *ᵥ Ket r) i‖ ^ 2 ≤ ε ^ 2

/-- Requires the generated word length to be bounded by `gateBudget` evaluated at the ceiling of
inverse precision. -/
def UnifiedSynthesis.Stable (w : ℕ) (S : UnifiedSynthesis w) : Prop :=
  ∀ (U : Matrix (Reg w) (Reg w) ℂ), U ∈ Matrix.unitaryGroup (Reg w) ℂ →
    ∀ (ε : ℝ), 0 < ε →
      (S.generate U ε).length ≤ S.gateBudget (Nat.ceil ((1 : ℝ) / ε))

/-- Requires a polynomial upper bound on the gate budget as a function of its natural number
argument. -/
def UnifiedSynthesis.PolyBounded (w : ℕ) (S : UnifiedSynthesis w) : Prop :=
  ∃ C e : ℕ, ∀ d : ℕ, S.gateBudget d ≤ C * (d + 1) ^ e

/-- A Turing machine with an integer size parameter and recorded bit time and bit space costs. -/
structure IntegerBitGcd (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where

  N : ℕ

  machine : Turing.TM0.Machine Γ Λ

  bitTime : ℕ

  bitSpace : ℕ

/-- Requires the recorded time and space to equal `gcdBitCost` and `gcdSpaceCost` at the stored
size parameter. -/
def IntegerBitGcd.Correct {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (x : IntegerBitGcd Γ Λ) : Prop :=
  x.bitTime = gcdBitCost x.N ∧ x.bitSpace = gcdSpaceCost x.N

/-- Requires the stored Turing machine to satisfy `BitMachinePolynomialTime`. -/
def IntegerBitGcd.PolyTime {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    [Fintype Γ] [Fintype Λ] (x : IntegerBitGcd Γ Λ) : Prop :=
  BitMachinePolynomialTime x.machine

/-- Specifies the comparison between Euclidean step and bit costs, the two word space cost, and
the factorization of total bit cost into step count and step cost. -/
def gcdLedgersSeparate (N : ℕ) : Prop :=
  euclidStepBound N ≤ gcdBitCost N ∧ gcdSpaceCost N = 2 * shorBitLength N ∧
    gcdBitCost N = euclidStepBound N * euclidStepBitCost N

/-- A workspace schedule recording word length, event count, and the number of live words at
each event. -/
structure SpaceSchedule where

  wordLen : ℕ

  events : ℕ

  live : ℕ → ℕ

/-- The maximum live word count over the recorded events, multiplied by the word length. -/
def SpaceSchedule.peakSpace (S : SpaceSchedule) : ℕ :=
  (List.range S.events).foldr (fun i acc => max (S.live i) acc) 0 * S.wordLen

/-- Requires zero initial live words and changes of at most one live word between consecutive
recorded events. -/
def SpaceSchedule.Correct (S : SpaceSchedule) : Prop :=
  S.live 0 = 0 ∧
    ∀ i, i + 1 < S.events →
      S.live (i + 1) = S.live i ∨ S.live (i + 1) + 1 = S.live i ∨
        S.live i + 1 = S.live (i + 1)

/-- Parameters recording dyadic precision and a preparation width. -/
structure PrepareDigits where

  digits : ℕ

  width : ℕ

/-- Requires the dyadic precision to be positive. -/
def PrepareDigits.Correct (x : PrepareDigits) : Prop := 0 < x.digits

/-- Quantizes the real and imaginary components of a complex number using `dyadicRat` at the
stored precision. -/
noncomputable def PrepareDigits.roundComplex (x : PrepareDigits) (z : ℂ) : ℂ :=
  ((dyadicRat x.digits z.re : ℂ) + (dyadicRat x.digits z.im : ℂ) * Complex.I)

end Qatlib.Concepts.RiskEstimation.PopulationGap
