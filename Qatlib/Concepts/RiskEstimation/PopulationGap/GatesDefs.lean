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

structure UnifiedSynthesis (w : ℕ) where

  generate : Matrix (Reg w) (Reg w) ℂ → ℝ → List FiniteGateCode

  gateBudget : ℕ → ℕ

def UnifiedSynthesis.Correct (w : ℕ) (S : UnifiedSynthesis w) : Prop :=
  ∀ (U : Matrix (Reg w) (Reg w) ℂ), U ∈ Matrix.unitaryGroup (Reg w) ℂ →
    ∀ (ε : ℝ), 0 < ε →
      finiteWordLegal w (S.generate U ε) = true ∧
        ∀ r : Reg w, ∃ φ : QState (Reg w),
          finiteWordRun w (S.generate U ε) (Ket r) = some φ ∧
            ∑ i, ‖φ i - (U *ᵥ Ket r) i‖ ^ 2 ≤ ε ^ 2

def UnifiedSynthesis.Stable (w : ℕ) (S : UnifiedSynthesis w) : Prop :=
  ∀ (U : Matrix (Reg w) (Reg w) ℂ), U ∈ Matrix.unitaryGroup (Reg w) ℂ →
    ∀ (ε : ℝ), 0 < ε →
      (S.generate U ε).length ≤ S.gateBudget (Nat.ceil ((1 : ℝ) / ε))

def UnifiedSynthesis.PolyBounded (w : ℕ) (S : UnifiedSynthesis w) : Prop :=
  ∃ C e : ℕ, ∀ d : ℕ, S.gateBudget d ≤ C * (d + 1) ^ e

structure IntegerBitGcd (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where

  N : ℕ

  machine : Turing.TM0.Machine Γ Λ

  bitTime : ℕ

  bitSpace : ℕ

def IntegerBitGcd.Correct {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (x : IntegerBitGcd Γ Λ) : Prop :=
  x.bitTime = gcdBitCost x.N ∧ x.bitSpace = gcdSpaceCost x.N

def IntegerBitGcd.PolyTime {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    [Fintype Γ] [Fintype Λ] (x : IntegerBitGcd Γ Λ) : Prop :=
  BitMachinePolynomialTime x.machine

def gcdLedgersSeparate (N : ℕ) : Prop :=
  euclidStepBound N ≤ gcdBitCost N ∧ gcdSpaceCost N = 2 * shorBitLength N ∧
    gcdBitCost N = euclidStepBound N * euclidStepBitCost N

structure SpaceSchedule where

  wordLen : ℕ

  events : ℕ

  live : ℕ → ℕ

def SpaceSchedule.peakSpace (S : SpaceSchedule) : ℕ :=
  (List.range S.events).foldr (fun i acc => max (S.live i) acc) 0 * S.wordLen

def SpaceSchedule.Correct (S : SpaceSchedule) : Prop :=
  S.live 0 = 0 ∧
    ∀ i, i + 1 < S.events →
      S.live (i + 1) = S.live i ∨ S.live (i + 1) + 1 = S.live i ∨
        S.live i + 1 = S.live (i + 1)

structure PrepareDigits where

  digits : ℕ

  width : ℕ

def PrepareDigits.Correct (x : PrepareDigits) : Prop := 0 < x.digits

noncomputable def PrepareDigits.roundComplex (x : PrepareDigits) (z : ℂ) : ℂ :=
  ((dyadicRat x.digits z.re : ℂ) + (dyadicRat x.digits z.im : ℂ) * Complex.I)

end Qatlib.Concepts.RiskEstimation.PopulationGap
