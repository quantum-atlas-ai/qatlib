/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.RiskEstimation.PopulationGap.Implementation
import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.FiniteBitAccessDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.FiniteBitLedgerDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib
open Matrix
open scoped ENNReal Classical BigOperators
open Qatlib
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]
variable {n N : ℕ}

namespace Qatlib.Concepts.RiskEstimation.PopulationGap
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.RiskEstimation.PopulationGap (clause11 euclid_gcd_fuel)
open Qatlib.Concepts.RiskEstimation.PopulationGap (shorBitLength euclidGcd euclidStepBound)
open Qatlib.Concepts.RiskEstimation.PopulationGap (SpaceSchedule)

structure RiskEmitterRecord where

  threshold : ℚ

  numerator : ℤ

  reduction : ℕ

  decision : Bool

noncomputable def riskEmitter (k : ℕ) (t : ℝ) (readout : ℚ) : RiskEmitterRecord where
  threshold := loadReal k t
  numerator := loadNumerator k t
  reduction := Nat.gcd (loadNumerator k t).natAbs (2 ^ k)
  decision := decide (readout ≤ loadReal k t)

theorem riskEmitter_threshold (k : ℕ) (t : ℝ) (readout : ℚ) :
    (riskEmitter k t readout).threshold = loadReal k t := rfl

theorem riskEmitter_threshold_error (k : ℕ) (t : ℝ) (readout : ℚ) :
    |((riskEmitter k t readout).threshold : ℝ) - t| < (1/2 : ℝ)^k := by
  rw [riskEmitter_threshold]
  exact loadReal_error k t

theorem riskEmitter_reduction (k : ℕ) {t : ℝ} :
    (riskEmitter k t 0).reduction = Nat.gcd ((loadNumerator k t).natAbs) (2 ^ k) := rfl

theorem riskEmitter_decision (k : ℕ) (t : ℝ) (readout : ℚ) :
    (riskEmitter k t readout).decision = decide (readout ≤ loadReal k t) := rfl

theorem riskEmitter_decision_of_le_load (k : ℕ) {t : ℝ} (readout : ℚ)
    (hreadout : (readout : ℝ) ≤ (loadReal k t : ℝ)) :
    (riskEmitter k t readout).decision = true := by
  rw [riskEmitter_decision]
  have hq : readout ≤ loadReal k t := (rat_le_iff _ _).mpr hreadout
  simp [hq]

theorem riskEmitter_decision_sound (k : ℕ) {t : ℝ} (readout : ℚ)
    (hdec : (riskEmitter k t readout).decision = true) :
    (readout : ℝ) ≤ t := by
  rw [riskEmitter_decision] at hdec
  have hq : readout ≤ loadReal k t := by
    by_contra hc
    simp [hc] at hdec
  have hle : (loadReal k t : ℝ) ≤ t := loadReal_le k t
  have hq' : (readout : ℝ) ≤ (loadReal k t : ℝ) := (rat_le_iff _ _).mp hq
  exact le_trans hq' hle

theorem riskEmitter_decision_of_gt (k : ℕ) {t : ℝ} (readout : ℚ)
    (hreadout : (readout : ℝ) > t) :
    (riskEmitter k t readout).decision = false := by
  rw [riskEmitter_decision]
  have hq : ¬ readout ≤ loadReal k t := by
    intro hc
    have hc' : (readout : ℝ) ≤ (loadReal k t : ℝ) := (rat_le_iff _ _).mp hc
    exact (not_le_of_gt hreadout) (le_trans hc' (loadReal_le k t))
  simp [hq]

theorem riskEmitter_decision_window (k : ℕ) {t : ℝ} (readout : ℚ)
    (hdec : (riskEmitter k t readout).decision = false)
    (hreadout : (readout : ℝ) ≤ t) :
    (loadReal k t : ℝ) < (readout : ℝ) ∧ (readout : ℝ) - (loadReal k t : ℝ) < (1/2 : ℝ)^k := by
  rw [riskEmitter_decision] at hdec
  have hq : ¬ readout ≤ loadReal k t := by
    by_contra hc
    simp [hc] at hdec
  have hle : (loadReal k t : ℝ) ≤ t := loadReal_le k t
  have herr : |((loadReal k t : ℝ) - t)| < (1/2 : ℝ)^k := loadReal_error k t
  have hq' : (loadReal k t : ℝ) < (readout : ℝ) :=
    lt_of_not_ge ((rat_le_iff _ _).not.mp hq)
  have habs : |((loadReal k t : ℝ) - t)| = t - (loadReal k t : ℝ) := by
    have h1 : (loadReal k t : ℝ) - t ≤ 0 := by linarith
    rw [abs_of_nonpos h1]
    ring
  constructor
  · exact hq'
  · linarith
end Qatlib.Concepts.RiskEstimation.PopulationGap
