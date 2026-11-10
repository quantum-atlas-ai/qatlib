/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.CleanBlockLCU
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot
open Matrix
open scoped BigOperators Kronecker

variable {J T I : Type} [Fintype J] [DecidableEq J]
  [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I]

omit [Fintype J] [Fintype T] in

private theorem word_phase_matrix (d : J → ℂ) :
    Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed d (fun _ => (1 : Matrix T T ℂ))) =
      Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := T) (Matrix.diagonal (fun j => Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPhase (d j))) := by
  classical
  ext ⟨j,x⟩ ⟨k,y⟩
  by_cases hj : j = k <;> by_cases hx : x = y <;>
    simp [Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister, Matrix.kroneckerMap_apply, Qatlib.Concepts.BlockEncoding.LCU.select, Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed,
      Matrix.one_apply, hj, hx]

theorem clean_word_lcu_encoding_cost
    (L : Matrix T I ℂ) (O : Matrix (J × T) (J × T) ℂ)
    (W : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × T))) (Y : J → Matrix I I ℂ)
    (d : J → ℂ) (j₀ : J) (hmass : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d)
    (hL : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L) (hW : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W ∈ unitaryGroup (J × T) ℂ)
    (hblock : Qatlib.Concepts.Execution.WorkspaceCP.compress ((1 : Matrix J J ℂ) ⊗ₖ L) (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W)
      ((1 : Matrix J J ℂ) ⊗ₖ L) = Qatlib.Concepts.BlockEncoding.LCU.select Y) :
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (∑ j, (d j / (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d : ℂ)) • Y j)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ L) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ L) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W + 3 ∧
    (Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W →
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W)) := by
  let Q := Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare d j₀
  let D :=
      Matrix.diagonal
      (fun j => Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPhase (d j))
  let body := Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody d W
  let cs := Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord (H := T) d j₀
  have hsub := Qatlib.Concepts.QsvtCore.QueryLowerBound.substitute_adjoint_evaluate_cost O body cs
  have hev : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) =
      (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := T) Q)ᴴ * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := T) D *
        Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := T) Q := by
    change Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O
        (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hsub.1]
    simp only [cs, Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one,
      body, Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody, word_phase_matrix, Q, D]
    simp only [Matrix.mul_assoc]
  have hP :=
      Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister_unitary (I := T)
      (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare_unitary d j₀ hmass)
  have hD : Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := T) D ∈ unitaryGroup (J × T) ℂ := by
    rw [← word_phase_matrix d]
    exact Qatlib.Concepts.BlockEncoding.LCU.select_unitary _
      (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed_unitary d _ (fun _ => (unitaryGroup T ℂ).one_mem))
  have hresult : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) ∈ unitaryGroup (J × T) ℂ := by
    rw [hev]
    exact (unitaryGroup (J × T) ℂ).mul_mem
      ((unitaryGroup (J × T) ℂ).mul_mem
        ((unitaryGroup (J × T) ℂ).mul_mem (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hP) hD) hW) hP
  have hframe := Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame_isIsometry j₀ L hL
  have hc :=
      Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.clean_block_lcu_compress L
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) Y d j₀ hmass hblock
  refine ⟨⟨hresult, hframe, hframe, ?_⟩, ?_, ?_, ?_⟩
  · rw [hev]
    exact hc
  · change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hsub.2.1]
    simp [cs, Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord,
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount, body, Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody]
  · change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hsub.2.2.1]
    simp [cs, Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount, body,
      Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody]
    omega
  · intro hlegal
    apply hsub.2.2.2
    · exact (Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff _ _).2 ⟨by
        rw [word_phase_matrix]
        exact hD, hlegal⟩
    · simpa only [cs, Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
        Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil,
        and_true] using And.intro (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hP) hP

end Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot
