/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.NearGridHHLOutput
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed

/-!
# Sine-envelope HHL pipeline guarantees

`source_A1_word_legality_and_counts` records well-formedness, unitary evaluation, and exact
query and fixed-gate counts for the assembled sine-envelope HHL word.
`source_A1_aa_success_and_four_kappa_repetitions` gives the corrected filter-event success
guarantee with amplification depth at most `4 * κ`, corresponding to the pipeline in Appendix
A.1 of [HarrowHassidimLloyd2009].

## Main statements

* `source_A1_word_legality_and_counts`: `2 * (M - 1)` queries and `4 * (M - 1) + 6` fixed gates.
* `source_A1_aa_success_and_four_kappa_repetitions`: a unitary preparation and success
  probability at least `1 / 4` within depth `4 * κ`.

## References

* [Harrow et al., 2009, Appendix A.1][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.Pipeline

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open scoped Real

/-- The sine-envelope HHL word is well formed, evaluates to a unitary, and uses `2 * (M - 1)`
queries and `4 * (M - 1) + 6` fixed gates under the stated unitary assumptions. See [Harrow
et al., Appendix A.1][HarrowHassidimLloyd2009]. -/
theorem source_A1_word_legality_and_counts (D M : ℕ) (hM : 2 ≤ M) (d : ℝ)
    (hd : 0 < d) (B U : Operator D)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    WellFormedAdjointCircuit (sinEnvelopeHHLWord M hM d B) ∧
      evaluate (sinEnvelopeOracleLift (D := D) (M := M) U) (sinEnvelopeHHLWord M hM d B)
        ∈ Matrix.unitaryGroup _ ℂ ∧
      adjointQueryCount (sinEnvelopeHHLWord M hM d B) = 2*(M-1) ∧
      adjointGateCount (sinEnvelopeHHLWord M hM d B) = 4*(M-1)+6 :=
  sin_envelope_word_legality_and_counts D M hM d hd B U hB hU

/-- Under the spectral and grid assumptions with `d = 1 / (2 * κ)` and `κ ≥ 4`, the HHL
preparation is unitary and some amplification depth at most `4 * κ` achieves success
probability at least `1 / 4` on the corrected well-conditioned event. See [Harrow et al.,
Appendix A.1][HarrowHassidimLloyd2009]. -/
theorem source_A1_aa_success_and_four_kappa_repetitions
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
            (sinEnvelopeWellSetCorrected D M) ≥ 1 / 4 := by
  have hκpos : (0 : ℝ) < κ := by linarith
  have hdpos : 0 < d := by rw [hdκ]; positivity
  have h2d : 2 * d ≤ 1 / 4 := by
    rw [hdκ, mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * κ)]
    nlinarith
  obtain ⟨hU, k, hk, hsucc, _⟩ :=
    sin_envelope_aa_success_and_cost M hM eig V B j d η hV hB hdpos h2d hη hη1 heig hbudget
  refine ⟨hU, k, ?_, hsucc⟩
  rw [hdκ] at hk
  have harg : (1 : ℝ) / (5 * (1 / (2 * κ))) = 2 * κ / 5 := by
    field_simp
  rw [harg] at hk
  have h1 : (k : ℝ) ≤ (Nat.ceil (2 * κ / 5) : ℝ) + 1 := by exact_mod_cast hk
  have h2 : (Nat.ceil (2 * κ / 5) : ℝ) < 2 * κ / 5 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  nlinarith

end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.Pipeline
