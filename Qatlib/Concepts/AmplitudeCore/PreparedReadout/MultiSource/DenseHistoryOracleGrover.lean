/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSource.DenseHistoryOracleWord
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover

open Matrix
open scoped Classical BigOperators
set_option warningAsError false

variable {H : Type} [Fintype H] [DecidableEq H]

noncomputable def spectatorSource (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix (Bool × H) (Bool × H) ℂ :=
  fun s => Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) (O s)

noncomputable def instructions (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step (Bool × H)) :=
  ((Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord Bool Aword ++
      [.gate (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed))]) ++
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord Bool Aword)) ++
      [.gate (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S))]

private theorem wellFormed_append {X : Type} [Fintype X] [DecidableEq X]
    (u v : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step X))
    (hu : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed u) (hv : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed v) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (u ++ v) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hu c hc
  · exact hv c hc

private theorem known_gate_wellFormed {X : Type} [Fintype X] [DecidableEq X]
    (V : Matrix X X ℂ) (hV : V ∈ Matrix.unitaryGroup X ℂ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed [.gate V] := by
  intro c hc
  have hc' : c = .gate V := List.mem_singleton.mp hc
  subst c
  exact hV

theorem instructions_wellFormed (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S) := by
  have hA :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord_wellFormed Bool Aword hw
  have hR := known_gate_wellFormed (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed))
    (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_unitary (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection_unitary seed))
  have hM := known_gate_wellFormed (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S))
    (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_unitary (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.mark_unitary seed S))
  exact wellFormed_append _ _
    (wellFormed_append _ _ (wellFormed_append _ _ hA hR)
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord_wellFormed _ hA)) hM

theorem evaluate_instructions (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.spectatorSource O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S) =
      Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S) := by
  let A :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword
  have hA : A ∈ Matrix.unitaryGroup H ℂ :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_unitary O Aword hw hO
  have hs : Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A *
      Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed) *
      (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A)ᴴ =
        Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (A * Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed * Aᴴ) := by
    have hh := Qatlib.Concepts.HspRecovery.ReductionCore.controlled_sandwich Aᴴ
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed) (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hA)
    simpa only [Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_adjoint,
        Matrix.conjTranspose_conjTranspose] using! hh
  have hlift :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_tensorWord Bool O Aword
  change Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.spectatorSource O)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord Bool Aword) = Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A at hlift
  simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_append,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_adjointWord, hlift, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.instructionMatrix, Matrix.mul_one]
  change Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A *
    Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed) *
    (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A)ᴴ * Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S) = _
  exact (congrArg (fun M => M * Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S)) hs).trans
    (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_mul (A * Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed * Aᴴ) (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S))

theorem coherent (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword)
    (ψ : Qatlib.Foundations.PureStateMath.QState (Bool × H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.spectatorSource O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S) *ᵥ ψ =
      Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S) *ᵥ ψ := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.evaluate_instructions O Aword seed S hO hw]

theorem false_sector (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword)
    (x y : H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.spectatorSource O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S) (false,x) (false,y) =
      (1 : Matrix H H ℂ) x y := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.evaluate_instructions O Aword seed S hO hw]
  simp [Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle,
      Qatlib.Concepts.BlockEncoding.LCU.select]

theorem instructions_unitary (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.spectatorSource O) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S) ∈
      Matrix.unitaryGroup _ ℂ :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_unitary _ _ (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions_wellFormed Aword seed S hw)
    (fun s => Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_unitary (hO s))

theorem counts (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H) :
    (∀ s, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S) =
      2 * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S) =
        2 * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount Aword + 2 := by
  constructor
  · intro s
    unfold Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions
    simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount_append,
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount_adjointWord,
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord_counts Bool Aword).1 s]
    have hz (V : Matrix (Bool × H) (Bool × H) ℂ) :
        Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s [.gate V] = 0 := rfl
    rw [hz, hz]
    omega
  · unfold Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions
    simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount_append,
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount_adjointWord,
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord_counts Bool Aword).2]
    have hg (V : Matrix (Bool × H) (Bool × H) ℂ) :
        Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount [.gate V] = 1 := rfl
    rw [hg, hg]
    omega

theorem inverse_evaluate (O : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.spectatorSource O)
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S)) =
      Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle ((Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate O Aword) seed S)ᴴ) := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_adjointWord, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.evaluate_instructions O Aword seed S hO hw,
    Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_adjoint]

theorem inverse_resources (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S)) ∧
      (∀ s, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S)) =
        2 * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S)) =
        2 * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount Aword + 2 := by
  refine ⟨Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord_wellFormed _
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions_wellFormed Aword seed S hw), ?_, ?_⟩
  · intro s
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount_adjointWord]
    exact (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.counts Aword seed S).1 s
  · rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount_adjointWord]
    exact (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.counts Aword seed S).2

theorem projectorHistory_counts (w : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .hamiltonian
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S) =
          2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount w ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .preparation
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S) = 2 ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .projector
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S) = 2 ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S) =
          2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount w + 2 := by
  have h :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistory_counts w
  have hc :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.counts (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.projectorHistoryWord w) seed S
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [h.1] using! hc.1 .hamiltonian
  · simpa only [h.2.1, Nat.mul_one] using! hc.1 .preparation
  · simpa only [h.2.2.1, Nat.mul_one] using! hc.1 .projector
  · simpa only [h.2.2.2] using! hc.2

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover
