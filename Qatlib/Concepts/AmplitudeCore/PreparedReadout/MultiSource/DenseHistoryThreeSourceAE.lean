/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSource.DenseHistoryOracleGrover
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSource.DenseHistoryOracleSubstitution
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AmplitudeCore.PreparedReadout (aeEstimate)

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE

open Matrix
open scoped Classical BigOperators Kronecker
set_option warningAsError false

variable {H : Type} [Fintype H] [DecidableEq H]

noncomputable def oracle (M : ℕ) (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix (Fin M × (Bool × H)) (Fin M × (Bool × H)) ℂ :=
  fun s => Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin M) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) (O s))

noncomputable def body (M : ℕ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step (Fin M × (Bool × H))) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord (Fin M) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S)

noncomputable def outer (M : ℕ) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Fin M × (Bool × H))) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseCompileCircuit (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.countedPhaseCircuit (I := H) M)

noncomputable def qpeWord (M : ℕ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step (Fin M × (Bool × H))) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.outer M)

noncomputable def initWord (M : ℕ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) :
    List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step (Fin M × (Bool × H))) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord (Fin M) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord Bool Aword)

noncomputable def instructions (M : ℕ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step (Fin M × (Bool × H))) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord M Aword seed S ++ Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.initWord M Aword

noncomputable def input (M : ℕ) (hM : 0 < M) (seed : H) : Qatlib.Foundations.PureStateMath.QState (Fin M × (Bool × H)) :=
  Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket seed))

noncomputable def output (M : ℕ) (hM : 0 < M)
    (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H) :
    Qatlib.Foundations.PureStateMath.QState (Fin M × (Bool × H)) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle M O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S) *ᵥ Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.input M hM seed

theorem body_evaluate (M : ℕ) (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle M O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeControlledGate M (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S) := by
  change Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate
    (fun s => Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin M) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.spectatorSource O s))
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord (Fin M)
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S)) = _
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_tensorWord,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.evaluate_instructions O Aword seed S hO hw,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_eq_kronecker]
  rfl

theorem qpeWord_coherent (M : ℕ) (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword)
    (ξ : Qatlib.Foundations.PureStateMath.QState (Fin M × (Bool × H))) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle M O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord M Aword seed S) *ᵥ ξ =
      Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeControlledGate M (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S))
        (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.countedPhaseCircuit M) ξ := by
  change Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle M O)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.outer M)) *ᵥ ξ = _
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.evaluate_substitute, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body_evaluate M O Aword seed S hO hw]
  exact Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseCompileCircuit_evaluate _ _ ξ

theorem initWord_evaluate (M : ℕ) (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle M O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.initWord M Aword) =
      Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin M) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword)) := by
  change Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate
    (fun s => Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin M) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) (O s)))
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord (Fin M) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord Bool Aword)) = _
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_tensorWord, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_tensorWord]

private theorem initWord_input (M : ℕ) (hM : 0 < M)
    (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle M O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.initWord M Aword) *ᵥ Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.input M hM seed =
      Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M))
        (Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed)) := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.initWord_evaluate, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_eq_kronecker, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_eq_kronecker]
  change Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Foundations.PureStateMath.TensorGate (1 : Qatlib.Foundations.PureStateMath.Operator M)
      (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Bool Bool ℂ) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword)))
      (Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket seed))) = _
  rw [Qatlib.Foundations.PureStateMath.applyGate_tensorGate,
      Qatlib.Foundations.PureStateMath.applyGate_one, Qatlib.Foundations.PureStateMath.applyGate_tensorGate, Qatlib.Foundations.PureStateMath.applyGate_one]
  rfl

theorem output_eq_qpe (M : ℕ) (hM : 0 < M)
    (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.output M hM O Aword seed S =
      Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.phaseFlagEmbed M (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.qpeOutput M
        (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S)
        (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed)) := by
  unfold Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.output Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_append, ← Matrix.mulVec_mulVec, initWord_input,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord_coherent M O Aword seed S hO hw]
  exact (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.counted_offgrid_qpe_clean_flag M hM
    (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S)
    (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed)).1

theorem output_eq_countedAE (M : ℕ) (hM : 0 < M)
    (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.output M hM O Aword seed S =
      Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeControlledGate M (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S))
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.countedAECircuit M (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.input M hM seed) :=
  (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.output_eq_qpe M hM O Aword seed S hO hw).trans
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.countedAE_output M hM (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S).symm

private theorem outer_resources (M : ℕ) (hM : 0 < M) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.outer (H := H) M) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.outer (H := H) M) = M - 1 ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.outer (H := H) M) = 2 * (M - 1) + 2 := by
  have hc :=
      (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.counted_offgrid_qpe_clean_flag M hM (1 : Matrix H H ℂ) (0 : Qatlib.Foundations.PureStateMath.QState H)).2
  have hr :=
      Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseCompileCircuit_counts
      (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.countedPhaseCircuit (I := H) M)
  exact ⟨Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseCompileCircuit_wellFormed hc.2.2,
      hr.1.trans hc.1, hr.2.trans hc.2.1⟩

private theorem body_resources (M : ℕ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) ∧
      (∀ s, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) =
        2 * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) =
        2 * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount Aword + 2 := by
  have hc := Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord_counts (Fin M)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S)
  have hg :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.counts Aword seed S
  refine ⟨Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord_wellFormed (Fin M) _
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions_wellFormed Aword seed S hw), ?_, ?_⟩
  · intro s
    exact (hc.1 s).trans (hg.1 s)
  · exact hc.2.trans hg.2

private theorem initWord_resources (M : ℕ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.initWord M Aword) ∧
      (∀ s, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.initWord M Aword) =
        Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.initWord M Aword) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount Aword := by
  have h1 :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord_counts Bool Aword
  have h2 :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord_counts (Fin M) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord Bool Aword)
  refine ⟨Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord_wellFormed (Fin M) _
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord_wellFormed Bool Aword hw), ?_, ?_⟩
  · intro s
    exact (h2.1 s).trans (h1.1 s)
  · exact h2.2.trans h1.2

theorem qpeWord_resources (M : ℕ) (hM : 0 < M)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord M Aword seed S) ∧
      (∀ s, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord M Aword seed S) =
        (M - 1) * (2 * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword)) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord M Aword seed S) =
        2*(M-1)+2+(M-1)*(2*Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount Aword+2) := by
  have ho := outer_resources (H := H) M hM
  have hb := body_resources M Aword seed S hw
  refine ⟨Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute_wellFormed _ _ hb.1 ho.1, ?_, ?_⟩
  · intro s
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.queryCount_substitute, ho.2.1, hb.2.1 s]
  · rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.gateCount_substitute, ho.2.1, ho.2.2, hb.2.2]

theorem resources (M : ℕ) (hM : 0 < M) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S) ∧
      (∀ s, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S) =
        (2*M-1)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S) =
        (2*M-1)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount Aword + 4*(M-1)+2 := by
  have hq :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord_resources M hM Aword seed S hw
  have hi := initWord_resources M Aword hw
  have hm : 2*M-1 = 2*(M-1)+1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    exact (List.mem_append.mp hc).elim (hq.1 c) (hi.1 c)
  · intro s
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount_append, hq.2.1 s, hi.2.1 s, hm]
    ring
  · rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount_append, hq.2.2, hi.2.2, hm]
    ring

theorem instructions_unitary (M : ℕ) (hM : 0 < M)
    (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle M O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S) ∈
      Matrix.unitaryGroup _ ℂ :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_unitary _ _ (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.resources M hM Aword seed S hw).1
    (fun s => Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_unitary (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_unitary (hO s)))

theorem output_normalized (M : ℕ) (hM : 0 < M)
    (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Foundations.PureStateMath.Normalized (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.output M hM O Aword seed S) :=
  Qatlib.Foundations.PureStateMath.normalized_applyGate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions_unitary M hM O Aword seed S hO hw)
    (Qatlib.Foundations.PureStateMath.normalized_tensorState (Qatlib.Foundations.PureStateMath.normalized_ket _)
      (Qatlib.Foundations.PureStateMath.normalized_tensorState (Qatlib.Foundations.PureStateMath.normalized_ket _) (Qatlib.Foundations.PureStateMath.normalized_ket _)))

theorem inverse_evaluate (M : ℕ) (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle M O)
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S)) =
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle M O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S))ᴴ :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_adjointWord _ _

theorem inverse_resources (M : ℕ) (hM : 0 < M)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S)) ∧
      (∀ s, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S)) =
          (2*M-1)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S)) =
        (2*M-1)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount Aword + 4*(M-1)+2 := by
  have h :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.resources M hM Aword seed S hw
  refine ⟨Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord_wellFormed _ h.1, ?_, ?_⟩
  · intro s
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount_adjointWord]
    exact h.2.1 s
  · rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount_adjointWord]
    exact h.2.2

theorem projectorHistory_resources (M : ℕ) (hM : 0 < M) (w : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit w) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .hamiltonian
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S) =
          (2*M-1)*Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount w ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .preparation
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S) = 2*M-1 ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .projector
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S) = 2*M-1 ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S) =
          (2*M-1)*Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount w + 4*(M-1)+2 := by
  have hs :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistory_counts w
  have hr := Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.resources M hM (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistory_wellFormed w hw)
  refine ⟨hr.1, ?_, ?_, ?_, ?_⟩
  · simpa only [hs.1] using! hr.2.1 .hamiltonian
  · simpa only [hs.2.1, Nat.mul_one] using! hr.2.1 .preparation
  · simpa only [hs.2.2.1, Nat.mul_one] using! hr.2.1 .projector
  · simpa only [hs.2.2.2] using! hr.2.2

theorem event_eq_aeLaw (M : ℕ) (hM : 2 ≤ M)
    (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword)
    (P : Fin M → Prop) :
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.output M (by omega) O Aword seed S)
      (Finset.univ.filter (fun z : Fin M × (Bool × H) => P z.1)) =
      ∑ z ∈ Finset.univ.filter P,
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw M (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S
          (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_unitary O Aword hw hO) hM).prob z := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.output_eq_countedAE M (by omega) O Aword seed S hO hw]
  exact (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw_event M hM (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_unitary O Aword hw hO) P).symm

theorem bhmt_actual (M : ℕ) (hM : 2 ≤ M)
    (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    let p :=
        Qatlib.Foundations.PureStateMath.MeasureProb
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) S
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.output M (by omega) O Aword seed S)
      (Finset.univ.filter (fun z : Fin M × (Bool × H) =>
        |aeEstimate M z.1-p| ≤ 2*Real.pi*Real.sqrt (p*(1-p))/(M : ℝ)+
          Real.pi^2/(M : ℝ)^2)) ≥ 8/Real.pi^2 := by
  (try dsimp only)
  have he := Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.event_eq_aeLaw M hM O Aword seed S hO hw
    (fun z : Fin M =>
      |aeEstimate M z-Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) S| ≤
        2*Real.pi*Real.sqrt (Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) S *
          (1-Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) S))/(M : ℝ)+
            Real.pi^2/(M : ℝ)^2)
  rw [he]
  exact (Qatlib.Concepts.AmplitudeCore.PreparedReadout.prepared_ae_bhmt_error_and_endpoints M hM (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword)
    seed S (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_unitary O Aword hw hO)).1

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE
