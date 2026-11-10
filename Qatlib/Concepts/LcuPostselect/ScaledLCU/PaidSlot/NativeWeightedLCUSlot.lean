/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

def weightedLCUSlotBody (d : J → ℂ) (W : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × H))) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × H)) :=
  .gate (Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed d (fun _ => (1 : Matrix H H ℂ)))) :: W

def weightedLCUSlotWord (d : J → ℂ) (j₀ : J)
    (W : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × H))) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × H)) :=
  Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody d W) (Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord d j₀)

theorem weightedLCUSlot_encoding_cost (j₀ : J) (A : J → Matrix I I ℂ)
    (U : J → Matrix H H ℂ) (F : Matrix H I ℂ) (c : J → ℂ) (α ε : J → ℝ)
    (O : Matrix (J × H) (J × H) ℂ) (W : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × H)))
    (henc : ∀ j, Qatlib.Concepts.BlockEncoding.BlockEncoding (A j) (U j) F F (α j) (ε j))
    (hmass : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUCoefficients c α))
    (hdiag : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W = Qatlib.Concepts.BlockEncoding.LCU.select U) (hW : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W) :
    let d := Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUCoefficients c α
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) ∧
    Qatlib.Concepts.BlockEncoding.BlockEncoding (∑ j, c j • A j)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ F) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ F)
      (∑ j, ‖c j‖ * α j) (∑ j, ‖c j‖ * ε j) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W + 3 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W)) =
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W))ᴴ ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W)) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W := by
  (try dsimp only)
  let d := Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUCoefficients c α
  let D :=
      Qatlib.Concepts.BlockEncoding.LCU.select
      (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed d (fun _ => (1 : Matrix H H ℂ)))
  let body := Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody d W
  let cs := Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord (H := H) d j₀
  have hD : D ∈ unitaryGroup (J × H) ℂ := by
    apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
    exact Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed_unitary d _
        (fun _ => (unitaryGroup H ℂ).one_mem)
  have hbody : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit body := by
    exact (Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff _ _).2 ⟨hD, hW⟩
  have hP :=
      Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister_unitary (I := H)
      (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare_unitary d j₀ hmass)
  have hcs : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit cs := by
    simpa only [cs, Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil,
      and_true] using And.intro (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hP) hP
  have hbodyeval : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O body = Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed d U) := by
    simp only [body,
        Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, hdiag]
    rw [Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]
    apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
    funext j
    simp [Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed]
  obtain ⟨he,hq,hg,hw⟩ :=
      Qatlib.Concepts.QsvtCore.QueryLowerBound.substitute_adjoint_evaluate_cost O body cs
  have heval : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) =
      Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary d U j₀ := by
    change Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O
        (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [he, hbodyeval]
    simp only [cs, Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one,
      Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary]
    rw [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_adjointCircuit _ _, ?_⟩
  · exact hw hbody hcs
  · rw [heval]
    exact Qatlib.Concepts.LcuPostselect.ScaledLCU.scaled_approximate_lcu_encoding j₀ A U F F c α ε henc hmass
  · change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hq]
    simp [cs, Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord,
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount, body, Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody]
  · change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hg]
    simp [cs, Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount, body,
      Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody]
    omega
  · rw [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_adjointCircuit]
    change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount
        (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hq]
    simp [cs, Qatlib.Concepts.LcuPostselect.ScaledLCU.scaledLCUAdjointWord,
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount, body, Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody]

end Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot
