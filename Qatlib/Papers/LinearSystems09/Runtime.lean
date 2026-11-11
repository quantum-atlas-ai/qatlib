/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SectionIIAmplifiedRuntimeCorrectedStat
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SectionIIAmplifiedRuntimeCorrectedHarr
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.NearGridHHLOutput
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# HHL amplification and runtime accounting

The corrected sine-envelope filter contract yields an amplified good-event
probability of at least one quarter with at most `4 * κ` amplification steps,
under the stated spectral and precision hypotheses. The module records the
associated oracle budget, simplifies the precision requirement, and expands
the runtime expression to display input-state preparation cost separately.

The source analysis is [HarrowHassidimLloyd2009], specifically
[Harrow, Hassidim & Lloyd, Section II][HarrowHassidimLloyd2009]. The corrected
filter and explicit numerical constants are those of this development.
-/
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinearSystems09.Runtime

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open scoped Real

/-- The corrected amplified Section II runtime contract for the sine-envelope HHL construction
in [HarrowHassidimLloyd2009]. -/
theorem source_sectionII_amplified_runtime_contract :
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SectionIIAmplifiedRuntimeCorrected :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.sectionIIAmplifiedRuntime

/-- The corrected HHL filter admits the stated amplified success and query
ledger under its spectral and precision assumptions; compare
[Harrow, Hassidim & Lloyd, Section II][HarrowHassidimLloyd2009]. -/
theorem source_sectionII_runtime_ledger
    {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
    (κ η d : ℝ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hκ : 4 ≤ κ) (hdκ : d = 1 / (2 * κ))
    (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1 / 4)
    (hbudget : 420 / (d * η) ≤ (M : ℝ)) :
    sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B ∈
        Matrix.unitaryGroup (Fin M × (Bool × (Fin 3 × Fin D))) ℂ ∧
      ∃ k : ℕ,
        (k : ℝ) ≤ 4 * κ ∧
        MeasureProb (Run (preparedMark (sinEnvelopeWellSetCorrected D M))
            (preparedAACircuit (sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B)
              (sinEnvelopeCleanInputPoint hM j) k)
            (Ket (sinEnvelopeCleanInputPoint hM j)))
            (sinEnvelopeWellSetCorrected D M) ≥ 1 / 4 ∧
        (k : ℝ) * (2 * ((M : ℝ) - 1)) ≤ 8 * κ * (M : ℝ) := by
  have hκpos : (0 : ℝ) < κ := by linarith
  have hdpos : 0 < d := by rw [hdκ]; positivity
  have h2d : 2 * d ≤ 1 / 4 := by
    rw [hdκ, mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * κ)]
    nlinarith
  obtain ⟨hU, k, hk, hsucc, _⟩ :=
    sin_envelope_aa_success_and_cost M hM eig V B j d η hV hB hdpos h2d hη hη1 heig hbudget
  rw [hdκ] at hk
  have harg : (1 : ℝ) / (5 * (1 / (2 * κ))) = 2 * κ / 5 := by
    field_simp
  rw [harg] at hk
  have hk1 : (k : ℝ) ≤ (Nat.ceil (2 * κ / 5) : ℝ) + 1 := by exact_mod_cast hk
  have hk2 : (Nat.ceil (2 * κ / 5) : ℝ) < 2 * κ / 5 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hk4 : (k : ℝ) ≤ 4 * κ := by nlinarith
  have hMone : (0 : ℝ) ≤ 2 * ((M : ℝ) - 1) := by
    have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
    nlinarith
  have hMle : 2 * ((M : ℝ) - 1) ≤ 2 * (M : ℝ) := by nlinarith
  refine ⟨hU, k, hk4, hsucc, ?_⟩
  calc
    (k : ℝ) * (2 * ((M : ℝ) - 1)) ≤ (4 * κ) * (2 * ((M : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right hk4 hMone
    _ ≤ (4 * κ) * (2 * (M : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hMle
      nlinarith
    _ = 8 * κ * (M : ℝ) := by ring

/-- For positive `κ` and `η`, the precision-budget expression `420 / ((1 / (2 * κ)) * η)`
simplifies to `840 * κ / η` [HarrowHassidimLloyd2009]. -/
theorem source_sectionII_precision_budget_eq (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) :
    (420 : ℝ) / ((1 / (2 * κ)) * η) = 840 * κ / η := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hη0 : η ≠ 0 := ne_of_gt hη
  field_simp
  ring

/-- Expand the modeled HHL runtime to expose the amplified preparation term
`κ * TB` alongside the solve term [HarrowHassidimLloyd2009]. -/
theorem source_sectionII_runtime_composition (κ TB C s logN ε : ℝ) (hε : ε ≠ 0) :
    κ * (TB + (C * κ / ε) * s ^ 2 * logN) =
      κ * TB + C * κ ^ 2 * s ^ 2 * logN / ε := by
  field_simp

end Qatlib.Papers.LinearSystems09.Runtime
