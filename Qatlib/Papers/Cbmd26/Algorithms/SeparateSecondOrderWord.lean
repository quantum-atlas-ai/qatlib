/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.UniformSelectedQSVT
import Qatlib.Papers.Cbmd26.Algorithms.PreparedPredicateFlatten

/-!
# Compiled second-order words with separate matrix access

This module substitutes coherent sample circuits into the four-branch polynomial response word
and compiles the result to separate controlled matrix oracles. `secondOrderFrame` gives the
associated signal frame for the second-order construction of [WangEtAl2026].

## Main statements

* `rawSecondOrderWord_evaluate`: identifies substitution with the abstract response circuit.
* `secondOrderWord_cost`: counts `8 * D + 2` queries to each matrix oracle and `80 * D + 33`
  fixed gates.
* `secondOrderWord_valid`: proves validity under the phase, frame, and scale hypotheses.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace CBMD
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
variable {J W I : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]

/-- The coherent separate-sample word inserted into an extra control register, masked by
`fourActive`, and reindexed for the flat response oracle. -/
def separateFamilyBody (βL βH : ℝ) (s : J → ℝ) :
    List (PreparedStep ((Fin 4 × J) × (Bool × (Bool × W)))) :=
  reindexPreparedWord (Equiv.prodAssoc (Fin 4) J (Bool × (Bool × W)))
    (maskPreparedWord fourActive (insertTwoOracleWord (coherentSeparateSampleWord βL βH s)))

/-- Against the predicate-controlled separate oracles, `separateFamilyBody` evaluates to the
flat response oracle of the sample unitary family. -/
theorem separateFamilyBody_evaluate (UL UH : Matrix W W ℂ) (βL βH : ℝ) (s : J → ℝ) :
    evaluatePrepared (preparedPredicateSource (J := J) (R := Bool) fourActive UH)
      (preparedPredicateSource (J := J) (R := Bool) fourActive UL)
      (separateFamilyBody βL βH s) =
      flatResponseOracle (fun j => separateSampleUnitary UL UH βL βH (s j)) := by
  rw [separateFamilyBody, preparedPredicateSource, preparedPredicateSource,
    reindexPreparedWord_evaluate, maskPreparedWord_evaluate,
    insertTwoOracleWord_evaluate (controlOracle UH) (controlOracle UL) _ _
      (coherentSeparateSampleWord_evaluate UL UH βL βH s)]
  rfl

omit [Fintype J] [Fintype W] in

/-- The separate family body uses one query to each oracle and five fixed gates. -/
theorem separateFamilyBody_cost (βL βH : ℝ) (s : J → ℝ) :
    preparedDataQueries (separateFamilyBody (W := W) βL βH s) = 1 ∧
    preparedInputQueries (separateFamilyBody (W := W) βL βH s) = 1 ∧
    preparedFixedGates (separateFamilyBody (W := W) βL βH s) = 5 := by
  simp only [separateFamilyBody, (reindexPreparedWord_cost _ _).1,
    (reindexPreparedWord_cost _ _).2.1, (reindexPreparedWord_cost _ _).2.2,
    (maskPreparedWord_cost _ _).1, (maskPreparedWord_cost _ _).2.1,
    (maskPreparedWord_cost _ _).2.2, (insertTwoOracleWord_cost _).1,
    (insertTwoOracleWord_cost _).2.1, (insertTwoOracleWord_cost _).2.2]
  exact coherentSeparateSampleWord_cost βL βH s

/-- Positive branch scales and nonnegative sample parameters make the separate family body
valid. -/
theorem separateFamilyBody_valid (βL βH : ℝ) (s : J → ℝ)
    (hL : 0 < βL) (hH : 0 < βH) (hs : ∀ j, 0 ≤ s j) :
    PreparedCircuitValid (separateFamilyBody (W := W) βL βH s) :=
  reindexPreparedWord_valid _ (maskPreparedWord_valid _ (insertTwoOracleWord_valid
    (coherentSeparateSampleWord_valid βL βH s hL hH hs)))

/-- The raw second-order circuit obtained by substituting the separate sample family body into
the flat response word. -/
def rawSecondOrderWord (c : J → ℂ) (j₀ : J) (F : Matrix W I ℂ) (D : ℕ)
    (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ)) (βL βH : ℝ) (s : J → ℝ) :
    List (PreparedStep ((Fin 4 × J) × (Bool × (Bool × W)))) :=
  substituteTwoOracleWord (separateFamilyBody βL βH s)
    (flatResponseWord c j₀ (tagFrame false F) D base zs)

/-- The second-order circuit compiled from `rawSecondOrderWord` to the prepared predicate
workspace. -/
def secondOrderWord (c : J → ℂ) (j₀ : J) (F : Matrix W I ℂ) (D : ℕ)
    (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ)) (βL βH : ℝ) (s : J → ℝ) :
    List (PreparedStep (Bool × (PreparedPredicateLabels (Fin 4) J Bool × W))) :=
  compiledPreparedPredicateWord fourActive (rawSecondOrderWord c j₀ F D base zs βL βH s)

/-- The signal frame obtained by tagging and averaging the input frame, reindexing the predicate
workspace, and adding the outer control tag. -/
def secondOrderFrame (j₀ : J) (F : Matrix W I ℂ) :
    Matrix (Bool × (PreparedPredicateLabels (Fin 4) J Bool × W)) I ℂ :=
  tagFrame false (reindexFrame (preparedPredicateWorkspaceEquiv (Fin 4) J Bool W)
    (tagFrame (0, j₀) (averageFrame (tagFrame false F))))

omit [DecidableEq I] in

/-- Evaluating the raw word against the predicate-controlled separate oracles equals evaluating
the flat response word against the sample family oracle. -/
theorem rawSecondOrderWord_evaluate (UL UH : Matrix W W ℂ) (c : J → ℂ) (j₀ : J)
    (F : Matrix W I ℂ) (D : ℕ) (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ))
    (βL βH : ℝ) (s : J → ℝ) :
    evaluatePrepared (preparedPredicateSource (J := J) (R := Bool) fourActive UH)
      (preparedPredicateSource (J := J) (R := Bool) fourActive UL)
      (rawSecondOrderWord c j₀ F D base zs βL βH s) =
    evaluate (flatResponseOracle (fun j => separateSampleUnitary UL UH βL βH (s j)))
      (flatResponseWord c j₀ (tagFrame false F) D base zs) := by
  rw [rawSecondOrderWord, substituteTwoOracleWord_evaluate, separateFamilyBody_evaluate]

omit [Fintype W] [DecidableEq I] in

/-- With the prescribed branch lengths, the raw second-order word uses `8 * D + 2` queries to
each oracle and `48 * D + 25` fixed gates. -/
theorem rawSecondOrderWord_cost (c : J → ℂ) (j₀ : J) (F : Matrix W I ℂ) (D : ℕ)
    (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ))
    (hlen : ∀ k, (zs k).length = uniformBranchDegree D k) (βL βH : ℝ) (s : J → ℝ) :
    preparedDataQueries (rawSecondOrderWord c j₀ F D base zs βL βH s) = 8 * D + 2 ∧
    preparedInputQueries (rawSecondOrderWord c j₀ F D base zs βL βH s) = 8 * D + 2 ∧
    preparedFixedGates (rawSecondOrderWord c j₀ F D base zs βL βH s) = 48 * D + 25 := by
  have h := substituteTwoOracleWord_cost (separateFamilyBody βL βH s)
    (flatResponseWord c j₀ (tagFrame false F) D base zs)
  have hb := separateFamilyBody_cost (W := W) βL βH s
  have hw := flatResponseWord_cost c j₀ (tagFrame false F) D base zs hlen
  simp only [hb.1, hb.2.1, hb.2.2, hw.1, hw.2, mul_one] at h
  exact ⟨h.1, h.2.1, h.2.2.trans (by omega)⟩

omit [Fintype W] [DecidableEq I] in

/-- With the prescribed branch lengths, the compiled second-order word uses `8 * D + 2` queries
to each oracle and `80 * D + 33` fixed gates. -/
theorem secondOrderWord_cost (c : J → ℂ) (j₀ : J) (F : Matrix W I ℂ) (D : ℕ)
    (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ))
    (hlen : ∀ k, (zs k).length = uniformBranchDegree D k) (βL βH : ℝ) (s : J → ℝ) :
    preparedDataQueries (secondOrderWord c j₀ F D base zs βL βH s) = 8 * D + 2 ∧
    preparedInputQueries (secondOrderWord c j₀ F D base zs βL βH s) = 8 * D + 2 ∧
    preparedFixedGates (secondOrderWord c j₀ F D base zs βL βH s) = 80 * D + 33 := by
  have h :=
      compiledPreparedPredicateWord_cost fourActive (rawSecondOrderWord c j₀ F D base zs βL βH s)
  have hw := rawSecondOrderWord_cost c j₀ F D base zs hlen βL βH s
  simp only [hw.1, hw.2.1, hw.2.2] at h
  exact ⟨h.1, h.2.1, h.2.2.trans (by omega)⟩

/-- The raw second-order word is valid for positive coefficient mass, an isometric frame,
unit-modulus phases, positive branch scales, and nonnegative sample parameters. -/
theorem rawSecondOrderWord_valid (c : J → ℂ) (j₀ : J) (hc : 0 < coefficientMass c)
    (F : Matrix W I ℂ) (hF : IsIsometry F) (D : ℕ)
    (base : Fin 4 → J → ℂ) (hb : ∀ k j, IsPhase (base k j))
    (zs : Fin 4 → List (J → ℂ)) (hz : ∀ k, ∀ z ∈ zs k, ∀ j, IsPhase (z j))
    (βL βH : ℝ) (s : J → ℝ) (hL : 0 < βL) (hH : 0 < βH) (hs : ∀ j, 0 ≤ s j) :
    PreparedCircuitValid (rawSecondOrderWord c j₀ F D base zs βL βH s) :=
  substituteTwoOracleWord_valid (separateFamilyBody_valid βL βH s hL hH hs)
    (flatResponseWord_wellFormed c j₀ hc _ (tagFrame_isIsometry false F hF) D base hb zs hz)

/-- The compiled second-order word is valid under the coefficient, frame, phase, and
sample-scale hypotheses ensuring validity of the raw word. -/
theorem secondOrderWord_valid (c : J → ℂ) (j₀ : J) (hc : 0 < coefficientMass c)
    (F : Matrix W I ℂ) (hF : IsIsometry F) (D : ℕ)
    (base : Fin 4 → J → ℂ) (hb : ∀ k j, IsPhase (base k j))
    (zs : Fin 4 → List (J → ℂ)) (hz : ∀ k, ∀ z ∈ zs k, ∀ j, IsPhase (z j))
    (βL βH : ℝ) (s : J → ℝ) (hL : 0 < βL) (hH : 0 < βH) (hs : ∀ j, 0 ≤ s j) :
    PreparedCircuitValid (secondOrderWord c j₀ F D base zs βL βH s) :=
  compiledPreparedPredicateWord_valid _
    (rawSecondOrderWord_valid c j₀ hc F hF D base hb zs hz βL βH s hL hH hs)

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
