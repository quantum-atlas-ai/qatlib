/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover

open Matrix
open scoped Classical BigOperators
set_option warningAsError false

variable {H : Type} [Fintype H] [DecidableEq H]

noncomputable def seedReflection (seed : H) : Matrix H H ℂ :=
  Qatlib.Foundations.PureStateMath.Reflection.ReflectionAbout (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket seed))

omit [Fintype H] in

theorem seedReflection_formula (seed : H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed = (2 : ℂ) • Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket seed) - 1 := rfl

theorem seedReflection_unitary (seed : H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed ∈ Matrix.unitaryGroup H ℂ :=
  Qatlib.Foundations.PureStateMath.Reflection.outerProduct_reflection_unitary (Qatlib.Foundations.PureStateMath.normalized_ket seed)

theorem mark_unitary (seed : H) (S : Finset H) :
    Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S ∈ Matrix.unitaryGroup H ℂ :=
  (Qatlib.Concepts.LchsSimulation.StaticLchs.prepared_aa_reflection_and_access (1 : Matrix H H ℂ) seed S (Submonoid.one_mem _)).1

noncomputable def spectatorWord (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H)) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool)) Aword

theorem spectatorWord_evaluate (U : Matrix H H ℂ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord Aword) =
      Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool))
    (by exact Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_one)
    (by intro V W; exact (Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul _ _).symm)
    (fun V => (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_adjoint V).symm) U Aword

theorem spectatorWord_wellFormed {Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)}
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord Aword) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool)) (fun _ h => Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_unitary h) hw

omit [Fintype H] [DecidableEq H] in

theorem spectatorWord_counts (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord Aword) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount Aword ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord Aword) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount Aword :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts _ _

noncomputable def instructions (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H)) :=
  ((Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord Aword ++ [.gate (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed))]) ++
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord Aword)) ++ [.gate (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S))]

theorem instructions_wellFormed (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S) := by
  have hA :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord_wellFormed hw
  have hR : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
      ([.gate (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed))] : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H))) := by
    simpa only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true] using!
      Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_unitary (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection_unitary seed)
  have hM : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
      ([.gate (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S))] : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H))) := by
    simpa only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true] using! Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_unitary (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.mark_unitary seed S)
  exact ((hA.append hR).append hA.adjointCircuit).append hM

theorem evaluate_instructions (U : Matrix H H ℂ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S) =
      Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S) := by
  let A := Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword
  have hA : A ∈ Matrix.unitaryGroup H ℂ := hw.evaluate_unitary hU
  have hs : Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A * Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed) *
      (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A)ᴴ = Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (A * Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed * Aᴴ) := by
    have h :=
        Qatlib.Concepts.HspRecovery.ReductionCore.controlled_sandwich Aᴴ
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed)
        (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hA)
    simpa only [Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_adjoint,
        Matrix.conjTranspose_conjTranspose] using! h
  simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_append, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_adjointCircuit,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord_evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one]
  change Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A * Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed) *
      (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A)ᴴ * Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S) = _
  exact (congrArg (fun M => M * Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S)) hs).trans
    (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_mul (A * Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.seedReflection seed * Aᴴ) (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S))

theorem coherent (U : Matrix H H ℂ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword)
    (ψ : Qatlib.Foundations.PureStateMath.QState (Bool × H)) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S) *ᵥ ψ =
      Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S) *ᵥ ψ := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.evaluate_instructions U Aword seed S hU hw]

theorem instructions_unitary (U : Matrix H H ℂ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S) ∈ Matrix.unitaryGroup _ ℂ :=
  (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions_wellFormed Aword seed S hw).evaluate_unitary (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_unitary hU)

theorem counts (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S) = 2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount Aword ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S) = 2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount Aword + 2 := by
  constructor
  · simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_adjointCircuit,
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord_counts Aword).1, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
    omega
  · simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_adjointCircuit,
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord_counts Aword).2, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount]
    omega

theorem resources (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S) = 2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount Aword ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S) = 2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount Aword + 2 :=
  ⟨Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions_wellFormed Aword seed S hw, Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.counts Aword seed S⟩

theorem inverse_evaluate (U : Matrix H H ℂ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) U) (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S)) =
      Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle ((Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S)ᴴ) := by
  rw [Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_adjointCircuit, Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.evaluate_instructions U Aword seed S hU hw,
    Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_adjoint]

theorem inverse_resources (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S)) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S)) = 2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount Aword ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S)) =
        2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount Aword + 2 := by
  exact ⟨(Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions_wellFormed Aword seed S hw).adjointCircuit,
    (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_adjointCircuit _).trans (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.counts Aword seed S).1,
    (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_adjointCircuit _).trans (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.counts Aword seed S).2⟩

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover
