/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.LinearSystemCostModelDefs
import Qatlib.Concepts.HhlErrorBridge.FilterStability

/-!
# HHL budget comparisons and specification counterexamples

`first_power_budget_window` compares the defined sine-envelope and uniform-grid budgets and
identifies the former with `nearOptimalKappaEpsBudget (1 / d) η`. The definitions concern the
phase-estimation and cost accounting of the HHL framework [HarrowHassidimLloyd2009].

`quantizeReal_neg_one` records the behavior of the natural-floor quantizer on a negative input.
`not_clause30` and `not_clause31` refute the displayed bundled specifications, including their
universal quantization requirements.

## Main statements

* `first_power_budget_window`: positivity and strict comparison of the budget expressions.
* `quantizeReal_neg_one`: the natural-floor quantizer maps `-1` to zero.
* `not_clause31`: the bundled access, retry, backend, and quantization specification is false.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Classical BigOperators

/-- The natural-floor quantizer sends `-1` to zero at every precision. -/
theorem quantizeReal_neg_one (k : ℕ) : quantizeReal k (-1) = 0 := by
  unfold quantizeReal
  rw [Nat.floor_of_nonpos (by have h := pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) k; nlinarith)]
  norm_num

/-- For `0 < d ≤ 1 / 4` and `0 < η ≤ 1`, the sine-envelope budget is positive, strictly below
the uniform-grid budget, and equal to the defined `κ / ε` budget at `κ = 1 / d`. -/
theorem first_power_budget_window (d η : ℝ) (hd : 0 < d) (hd1 : d ≤ 1 / 4)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    0 < sinEnvelopeFirstPowerBudget d η ∧
      sinEnvelopeFirstPowerBudget d η < uniformQPEGridBudget d η ∧
      sinEnvelopeFirstPowerBudget d η = nearOptimalKappaEpsBudget (1 / d) η := by
  refine ⟨by unfold sinEnvelopeFirstPowerBudget; positivity, ?_, ?_⟩
  · unfold sinEnvelopeFirstPowerBudget uniformQPEGridBudget
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    have hpow : η^3 ≤ 1 := by simpa using! pow_le_pow_left₀ hη.le hη1 3
    have hmul : d * η^3 ≤ (1 / 4 : ℝ) := by
      simpa using! mul_le_mul hd1 hpow (pow_nonneg hη.le _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hsmall : 21 * d * η^3 < 4096 := by nlinarith
    have hp := mul_pos (sub_pos.mpr hsmall) (mul_pos hd hη)
    nlinarith
  · unfold sinEnvelopeFirstPowerBudget nearOptimalKappaEpsBudget
    field_simp

/-- The displayed conjunction of filter, runtime, backend, dilation, and quantization
requirements is false. -/
theorem not_clause30 : ¬ (

  (∀ (d η : ℝ), 0 < d → d ≤ 1 / 4 → 0 < η → η ≤ 1 →
    0 < sinEnvelopeFirstPowerBudget d η ∧
      sinEnvelopeFirstPowerBudget d η < uniformQPEGridBudget d η ∧
      sinEnvelopeFirstPowerBudget d η = nearOptimalKappaEpsBudget (1 / d) η) ∧

  (∀ (d : ℝ), 0 < d →
    sinEnvelopeFilterF d (2 * d) = 1 / 2 ∧ sinEnvelopeFilterG d (2 * d) = 0 ∧
      sinEnvelopeFilterF d d = 0 ∧ sinEnvelopeFilterG d d = 1 / 2 ∧
      sinEnvelopeFilterF d 0 = 0 ∧ sinEnvelopeFilterG d 0 = 1 / 2 ∧
      sinEnvelopeFilterF d (-1 / 4) = 0 ∧ sinEnvelopeFilterG d (-1 / 4) = 1 / 2 ∧
      (∀ θ, 2 * d ≤ θ → sinEnvelopeFilterF d θ = d / θ ∧
        sinEnvelopeFilterG d θ = 0)) ∧

  ((∀ (d θ : ℝ), 0 < d →
      sinEnvelopeFlagRotation d θ ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
        sinEnvelopeFlagRotation d θ *ᵥ Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) = sinEnvelopeHVector d θ) ∧
    (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
        (d η : ℝ),
      V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      0 < d → 0 < η → η ≤ 1 →
      (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
      21 / (d * η) ≤ (M : ℝ) →
      ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
          sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤ η)) ∧

  (∀ (S : SparseAccessSystem) (s : ℕ), S.Legal s →
    ∃ (k : ℕ) (B : HamiltonianBackend),
      B.access = S ∧ B.sparsity = s ∧ B.precision = k ∧ B.Complete) ∧

  (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ),
    nonHermitianDilation A =
      Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) ((1 / 4 : ℂ) • A)
        (((1 / 4 : ℂ) • A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ) ∧
      (nonHermitianDilation A)ᴴ = nonHermitianDilation A ∧
      nonHermitianDilation A * nonHermitianDilation A =
        Matrix.fromBlocks ((1 / 16 : ℂ) • (A * Aᴴ)) (0 : Matrix (Fin m) (Fin n) ℂ)
          (0 : Matrix (Fin n) (Fin m) ℂ) ((1 / 16 : ℂ) • (Aᴴ * A))) ∧

  ((∀ (k : ℕ) (t : ℝ),
      0 ≤ (t : ℝ) - ((quantizeReal k t : ℚ) : ℝ) ∧
        (t : ℝ) - ((quantizeReal k t : ℚ) : ℝ) < (1 / 2 : ℝ) ^ k) ∧
    (∀ (k : ℕ) (z : ℂ),
      |z.re - (quantizeComplex k z).re| < (1 / 2 : ℝ) ^ k ∧
        |z.im - (quantizeComplex k z).im| < (1 / 2 : ℝ) ^ k)) ∧

  (∀ (w : ℕ), ∃ B : IntegerBitBackend,
    B.wires = w ∧ B.Legal ∧ B.PolyBounded) ∧

  (∀ (f : SinThreeStateFilter), f.Budgeted →
    ∃ L : NumericBackendLedger, L.Complete f) ∧

  (∀ (d η : ℝ), 0 < d → d ≤ 1 / 4 → 0 < η → η ≤ 1 →
    sinEnvelopeFirstPowerBudget d η ≤ uniformQPEGridBudget d η)
) := by
  intro h
  have hneg := (h.2.2.2.2.2.1.1 1 (-1)).1
  rw [quantizeReal_neg_one] at hneg
  norm_num at hneg

/-- The displayed conjunction of circuit, paid-access, retry, preparation-backend, and universal
system-quantization requirements is false. -/
theorem not_clause31 : ¬ (

  (∀ (H : Type) [Fintype H] [DecidableEq H] (U : Matrix H H ℂ)
      (cs : List (AdjointStep H)),
    U ∈ Matrix.unitaryGroup H ℂ → WellFormedAdjointCircuit cs →
    WellFormedAdjointCircuit (cs ++ adjointCircuit cs) ∧
      evaluate U (cs ++ adjointCircuit cs) = 1 ∧
      adjointQueryCount (cs ++ adjointCircuit cs) = 2 * adjointQueryCount cs ∧
      adjointGateCount (cs ++ adjointCircuit cs) = 2 * adjointGateCount cs) ∧

  (∀ (a : PaidAccess), a.Explicit →
    (finiteWordAdjoint a.forward).length = a.forward.length ∧
      a.forward.length ≤ a.inverseGates ∧
      a.forward.length ≤ a.controlledGates ∧
      a.prepGates ≤ a.prepInverseGates ∧
      a.RoundTrip = 2 * a.forward.length) ∧

  (∀ (D M : ℕ) (d : ℝ) (B : Operator D), 2 ≤ M → 0 < d →
    B ∈ Matrix.unitaryGroup (Fin D) ℂ →
    WellFormedAdjointCircuit (uniformHHLWord M d B) ∧
      adjointQueryCount (uniformHHLWord M d B) = 2 * (M - 1) ∧
      adjointGateCount (uniformHHLWord M d B) = 4 * (M - 1) + 6) ∧

  (uniformGridChargedAtFullScale ∧
    (∀ (d η : ℝ), 0 < d → 0 < η →
      4096 / (d ^ 2 * η ^ 4) = uniformQPEGridBudget d η)) ∧

  (freshRetryIsNotAmplification ∧
    (∀ (s : FreshRetrySchedule), 0 < s.trials →
      s.totalCost = s.trials * s.perTrialCost ∧
        s.jointFailure = (1 - s.perTrialSuccess) ^ s.trials)) ∧

  (∀ (S : SparseAccessSystem) (s : ℕ), S.Legal s →
    ∃ (k : ℕ) (B : EffectivePreparationBackend),
      B.access = S ∧ B.Complete s k) ∧

  (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ), 0 < k →
    ∃ D : SystemDecomputation, D.digits = k ∧ D.Complete A)
) := by
  intro h
  obtain ⟨D, hD, hcomplete⟩ := h.2.2.2.2.2.2 1 1 (fun _ _ => -1) 1 (by decide)
  have he := (hcomplete.2 0 0).1
  rw [hD] at he
  norm_num [quantizeReal_neg_one] at he

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
