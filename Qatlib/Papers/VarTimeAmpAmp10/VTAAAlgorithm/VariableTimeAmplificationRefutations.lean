/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.StructuralEstimateCompilationVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundLows
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.AmplificationProductEventBounds
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmpCounterexamples

/-!
# Refutations of unrestricted variable-time clauses

This module uses explicit finite-dimensional inputs and cost counterexamples to refute four
unrestricted conjunctions of variable-time specifications. The conclusions concern the displayed
formal clauses, including their missing restrictions, within the framework motivated by the
cited paper.

The variable-time amplification setting is described in [Ambainis2012].

## Main statements

* `not_clause64`: refutation using negative cost data.
* `not_clause67`: refutation of a compiler depending only on the interface.
* `not_clause68` and `not_clause89`: refutations of the displayed gain and recurrence clauses.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
/-- The four-dimensional state with every amplitude equal to one half. -/
private noncomputable abbrev fourUniform : QState (Fin 4) := fun _ => 1 / 2
/-- The two-projector family consisting of zero at index zero and the identity at index one. -/
private noncomputable abbrev stopProjectors : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun j => if j = 0 then 0 else 1

/-- The state with four amplitudes equal to one half is normalized. -/
private theorem fourUniform_normalized : Normalized fourUniform := by
  norm_num [Normalized, fourUniform]

/-- The zero-then-identity stopping projectors with identity stage matrices satisfy
`nestedStopLegal` for one stage. -/
private theorem stopProjectors_legal : nestedStopLegal 1 stopProjectors (fun _ => 1) := by
  refine ⟨?_, by simp [stopProjectors], by simp [stopProjectors], ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp [stopProjectors, IsOrthogonalProjector]
  · intro j k h
    fin_cases j <;> fin_cases k <;> simp_all [stopProjectors]
    all_goals first
      | exact (Matrix.PosSemidef.zero : (0 : Matrix (Fin 4) (Fin 4) ℂ).PosSemidef)
      | exact (Matrix.PosSemidef.one : (1 : Matrix (Fin 4) (Fin 4) ℂ).PosSemidef)
  · intro j
    exact one_mem _
  · intro j
    simp

/-- The empty plain prefix with identity stage matrices leaves `fourUniform` unchanged. -/
private theorem fourUniform_clock :
    clockState (fun _ => (1 : Matrix (Fin 4) (Fin 4) ℂ)) (plainPrefix 0) fourUniform =
      fourUniform := by
  ext i
  simp [clockState, plainPrefix, run, wordMatrix, controlled, clean, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, fourUniform, Matrix.one_apply]

/-- The singleton good set `{0}` in `fourUniform` has the good-component specification with
target `Ket 0` and success mass one quarter. -/
private theorem fourUniform_good : goodComponentData {0} fourUniform (Qatlib.Foundations.PureStateMath.Ket 0) (1 / 4) := by
  refine ⟨fourUniform_normalized, normalized_ket 0, by norm_num, ?_, ?_⟩
  · norm_num [MeasureProb, BornProb, fourUniform]
  · have hsq := norm_toEuclidean_fromVec_sq (Collapse fourUniform {0})
    have heval : ∑ i : Fin 4, ‖Collapse fourUniform {0} i‖ ^ 2 = (1 / 4 : ℝ) := by
      norm_num [collapse_apply, fourUniform, Fin.sum_univ_succ]
    have hn : normVec (Collapse fourUniform {0}) = 1 / 2 := by
      unfold normVec
      rw [heval] at hsq
      have hn := norm_nonneg (toEuclidean_fromVec (Collapse fourUniform {0}))
      nlinarith
    rw [hn]
    ext i
    simp [stateVector, collapse_apply, fourUniform, Qatlib.Foundations.PureStateMath.Ket]
noncomputable section

/-- The displayed conjunction of variable-time specifications and a universal `tightAccessCost`
amplification bound is false. -/
theorem not_clause64 : ¬ (

  VariableTimeAlgorithm ∧
  VariableTimeModelWellFormed ∧
  StructuralEstimateCompilation ∧
  CascadePrefixTransport ∧
  RecordDrivenVariableTimeAlgorithm ∧

  ∃ K : ℝ, 0 < K ∧
    ∀ (H : Type) [Fintype H] [DecidableEq H] (m : ℕ)
      (P : Fin (m + 1) → Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
      (p t : Fin m → ℝ) (Tmax Tav psucc : ℝ) (prices : ℕ → ℕ)
      (ω ψA ψgood : QState H) (good : Finset H),

      nestedStopLegal m P U →

      stopTimeData m p t Tmax Tav →

      (∀ i : Fin m, prices i = Nat.ceil (t i)) →
      Normalized ω →

      ψA = clockState U (plainPrefix (m - 1)) ω →
      goodComponentData good ψA ψgood psucc →

      ∃ (prog : VtAmpProgram H) (hr : 0 < prog.r),
        legal m prog.word ∧
        1 / 2 ≤ prog.goodMass hr U ω ∧
        (∃ c : ℂ, prog.goodVector hr U ω = c • ψgood) ∧
        ((prog.accessTime prices : ℝ) ≤ K * tightAccessCost Tmax Tav psucc)
) := by
  rintro ⟨_, _, _, _, _, K, hK, h⟩
  obtain ⟨prog, _, _, _, _, hcost⟩ := h (Fin 4) 1 stopProjectors (fun _ => 1)
    (fun _ => 1) (fun _ => 1) 1 (-1) (1 / 4) (fun _ => 1)
    fourUniform fourUniform (Qatlib.Foundations.PureStateMath.Ket 0) {0} stopProjectors_legal
    (by norm_num [stopTimeData]) (by norm_num) fourUniform_normalized
    fourUniform_clock.symm fourUniform_good
  norm_num [tightAccessCost, tightLogFactor] at hcost
  have hn : (0 : ℝ) ≤ prog.accessTime (fun _ => 1) := Nat.cast_nonneg _
  linarith
end
noncomputable section

/-- The displayed universal conjunction of local gain assumptions, gain-product bounds, and a
stopping-time cost bound is false. -/
theorem not_clause68 : ¬ (

  AverageStopTailBound ∧

  ∀ (m : ℕ) (rs rs' pstop : ℕ → ℝ) (psucc : ℝ),
    1 ≤ m → 0 < psucc → psucc ≤ 1 →

    (∀ j, 1 ≤ j → j ≤ m → 1 / (9 * (m : ℝ)) ≤ rs j ∧ 0 ≤ rs' j) ∧
    (rs m ≤ 1 / (m : ℝ)) ∧
    (∀ j, 1 ≤ j → j ≤ m →
      rs j = rs' j ∨
        ∃ k : ℕ,
          (1 - 1 / (3 * (m : ℝ))) * ((2 * k + 1 : ℝ) ^ 2) * rs' j ≤ rs j) ∧

    (∀ j, 1 ≤ j → j ≤ m → 0 ≤ pstop j) ∧

    (∀ i, 1 ≤ i → i ≤ m →
      gainRatioProduct rs rs' i (m + 1) ≤
        lemma3Rhs (remainingStopMass m pstop i) psucc) ∧

    (∃ C : ℝ, 0 < C ∧
      ∀ (Tmax Tav : ℝ) (t : Fin (m + 1) → ℝ),
        (∀ j : Fin (m + 1), t j = (2 : ℝ) ^ (j.val : ℕ)) →
        Tmax = (2 : ℝ) ^ m →
        (Tav ^ 2 = ∑ j : Fin m, pstop j.val * (t ⟨j.val, by omega⟩) ^ 2) →
        (∑ i ∈ Finset.Ico 1 (m + 1),
          gainRatioProduct rs rs' i (m + 1) * (2 : ℝ) ^ ((i : ℕ) - 1)) ≤
          C * tightAccessCost Tmax Tav psucc)
) := by
  intro h
  apply clause68_gainRatioProduct_counterexample.2.2.2.2
  exact (h.2 1 _ _ _ 1 (by decide) (by norm_num) (by norm_num)).2.2.2.2.1
    1 (by decide) (by decide)
end
noncomputable section

/-- The displayed universal compiler specification, whose compiled circuit depends only on the
interface, is false even when paired with `VariableTimeAlgorithm`. -/
theorem not_clause67 : ¬ (

  VariableTimeAlgorithm ∧

  ∃ (K : ℝ) (compile : VtInterface → VtCompiledCircuit), 1 ≤ K ∧
    ∀ (H : Type) [Fintype H] [DecidableEq H] (I : VtInterface)
      (prog : VtAmpProgram H) (hr : 0 < prog.r) (oracles : ℕ → Matrix H H ℂ)
      (ω : QState H) (target : QState H) (ε : ℝ),

      1 ≤ I.slots → (∀ j, 1 ≤ I.prices j) → 1 ≤ I.precision →

      legal I.slots prog.word →
      let circuit := compile I

      circuit.Legal ∧

      ((prog.accessTime I.prices : ℝ) + flagReflectionPrice prog.r ≤
        K * (I.precision : ℝ) * (circuit.bitTime : ℝ)) ∧
      ((circuit.bitTime : ℝ) ≤ K * (I.precision : ℝ) *
        ((prog.accessTime I.prices : ℝ) + (prog.word).length +
          flagReflectionPrice prog.r)) ∧

      (circuit.workspace ≤
        Nat.ceil (K * (I.precision : ℝ) *
          ((prog.r : ℝ) + (prog.word).length + 1))) ∧

      (∀ Tmax Tav psucc : ℝ, 1 ≤ Tmax → 0 < psucc →
        (prog.accessTime I.prices : ℝ) ≤ tightAccessCost Tmax Tav psucc →
        ((circuit.bitTime : ℝ) ≤
          K * (I.precision : ℝ) * tightAccessCost Tmax Tav psucc)) ∧

      (∀ k p q : ℝ, 1 ≤ k → 0 < p → 0 < q →
        (prog.accessTime I.prices : ℝ) ≤ adaptiveEstimateBudget k p q →
        ((circuit.bitTime : ℝ) ≤
          K * (I.precision : ℝ) * adaptiveEstimateBudget k p q)) ∧

      (∀ Csim κ eps : ℝ, 0 < Csim → 1 ≤ κ → 0 < eps →
        (prog.accessTime I.prices : ℝ) ≤ qlsThm3Cost Csim κ eps →
        ((circuit.bitTime : ℝ) ≤
          K * (I.precision : ℝ) * qlsThm3Cost Csim κ eps)) ∧

      (stateGuarantee (1 : Matrix H H ℂ) prog.readout
        (run hr oracles prog.word ω) target ε →
        1 / 2 < prog.goodMass hr oracles ω)
) := by
  rintro ⟨_, K, compile, _, h⟩
  let I : VtInterface := ⟨2, fun _ => 1, 1⟩
  let n := Nat.ceil (K * ((compile I).bitTime : ℝ)) + 1
  obtain ⟨prog, hr, hlegal, htime⟩ := clause67_unbounded_legal_accessTime (Fin 1) n
  have hrun := h (Fin 1) I prog hr (fun _ => 1) (Qatlib.Foundations.PureStateMath.Ket 0) (Qatlib.Foundations.PureStateMath.Ket 0) 1
    (by decide) (by simp [I]) (by decide) hlegal
  have hbudget := hrun.2.1
  have hceil := Nat.le_ceil (K * ((compile I).bitTime : ℝ))
  have hflag : 0 ≤ flagReflectionPrice prog.r := by
    unfold flagReflectionPrice
    positivity
  dsimp [I] at hbudget hceil
  simp only [Nat.cast_one, mul_one] at hbudget
  dsimp [n, I] at htime
  push_cast at htime
  linarith
end
noncomputable section

/-- The displayed universal conjunction of gain assumptions, a stage-time recurrence, and its
proposed bounds is false. -/
theorem not_clause89 : ¬ (

  CascadePrefixTransport ∧

  ∀ (m : ℕ) (rs rs' : ℕ → ℝ) (k : ℕ → ℕ) (T : ℕ → ℝ),
    1 ≤ m →

    (∀ j : ℕ, 1 ≤ j → j ≤ m → 0 < rs' j) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ m → 1 / (9 * (m : ℝ)) ≤ rs j) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ m →
      (1 - 1 / (3 * (m : ℝ))) * ((2 * k j + 1 : ℝ) ^ 2) * rs' j ≤ rs j) ∧

    0 ≤ T 0 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ m →
      T i = (2 * k i + 1 : ℝ) * (T (i - 1) + (2 : ℝ) ^ ((i : ℕ) - 1))) ∧

    (∀ i : ℕ, 1 ≤ i → i ≤ m →
      T i ≤ eq5StageTimeBound m (rs i) (rs' i) (T (i - 1)) i) ∧

    T m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
      (gainRatioProduct rs rs' 1 (m + 1) * T 0 + eq6ProductSum rs rs' m)
) := by
  intro h
  exact clause89_frozen_residual_false h.2
end
noncomputable section

/-- There is a normalized four-dimensional input with a good component of mass one quarter for
which `tightAccessCost 1 (-1) (1 / 4)` equals negative one. -/
theorem negative_cost_quantum_input :
    ∃ (ω ψ : QState (Fin 4)) (good : Finset (Fin 4)),
      Normalized ω ∧ goodComponentData good ω ψ (1 / 4) ∧
        tightAccessCost 1 (-1) (1 / 4) = -1 := by
  refine ⟨fourUniform, Qatlib.Foundations.PureStateMath.Ket 0, {0}, fourUniform_normalized,
      fourUniform_good, ?_⟩
  norm_num [tightAccessCost, tightLogFactor]
end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
