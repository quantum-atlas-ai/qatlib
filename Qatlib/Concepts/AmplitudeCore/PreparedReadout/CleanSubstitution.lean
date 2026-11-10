/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution

open Matrix
open scoped Classical BigOperators

variable {H : Type} [Fintype H] [DecidableEq H]

private noncomputable abbrev matmul {X Y Z : Type*} [Fintype Y]
    (A : Matrix X Y ℂ) (B : Matrix Y Z ℂ) : Matrix X Z ℂ :=
  @HMul.hMul (Matrix X Y ℂ) (Matrix Y Z ℂ) (Matrix X Z ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

noncomputable def frame : Matrix (Bool × H) H ℂ :=
    Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false

theorem frame_isometry : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (H := H)) :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry false

theorem parallel_frame (V : Matrix H H ℂ) :
    matmul (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) V) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame V := by
  ext ⟨b,i⟩ j
  cases b <;>
    simp [matmul, Matrix.mul_apply, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.BlockEncoding.LCU.select, Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame, Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber,
      Fintype.sum_prod_type]

noncomputable def liftWord (cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H)) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool)) cs

noncomputable def instructions (body : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H)))
    (cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H)) :=
  Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord cs)

omit [Fintype H] [DecidableEq H] in

theorem liftWord_counts (cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord cs) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount cs ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord cs) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount cs :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts _ cs

theorem liftWord_wellFormed {cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)}
    (hcs : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit cs) : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord cs) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool))
    (fun _ h => Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_unitary h) hcs

theorem adjoint_clean (B : Matrix (Bool × H) (Bool × H) ℂ)
    (O : Matrix H H ℂ) (hB : B ∈ Matrix.unitaryGroup (Bool × H) ℂ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ)
    (hf : matmul B Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame O) :
    matmul Bᴴ Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame Oᴴ := by
  have hBB : Bᴴ * B = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hB)
  have hOO : O * Oᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hO)
  calc
    matmul Bᴴ Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Bᴴ (matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (O * Oᴴ)) := by
      simp only [hOO, matmul, Matrix.mul_one]
    _ = matmul Bᴴ (matmul (matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame O) Oᴴ) :=
      congrArg (fun M => matmul Bᴴ M) (Matrix.mul_assoc Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame O Oᴴ).symm
    _ = matmul Bᴴ (matmul (matmul B Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame) Oᴴ) := by rw [← hf]
    _ = matmul (Bᴴ * B) (matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame Oᴴ) := by
      simp only [matmul, Matrix.mul_assoc]
    _ = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame Oᴴ := by simp only [hBB, matmul, Matrix.one_mul]

theorem lifted_intertwining (B : Matrix (Bool × H) (Bool × H) ℂ)
    (O : Matrix H H ℂ)
    (hf : matmul B Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame O)
    (hb : matmul Bᴴ Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame Oᴴ)
    (cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate B (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord cs)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs) := by
  induction cs with
  | nil =>
    change matmul (1 : Matrix (Bool × H) (Bool × H) ℂ) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame =
      matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (1 : Matrix H H ℂ)
    exact (Matrix.one_mul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame).trans (Matrix.mul_one Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame).symm
  | cons c cs ih =>
    have hs :
        matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix B
          (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftStep (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool)) c)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame =
          matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix O c) := by
      cases c with
      | gate V => exact Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.parallel_frame V
      | forward => exact hf
      | backward => exact hb
    change matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix B (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftStep (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool)) c) *
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate B (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord cs)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame =
      matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix O c * Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs)
    calc
      _ = matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix B (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftStep (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool)) c))
          (matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate B (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord cs)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame) := Matrix.mul_assoc _ _ _
      _ = matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix B (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftStep (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool)) c))
          (matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs)) := by rw [ih]
      _ = matmul (matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix B
          (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftStep (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool)) c)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame) (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs) :=
        (Matrix.mul_assoc _ _ _).symm
      _ = matmul (matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix O c)) (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs) := by rw [hs]
      _ = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix O c * Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs) := Matrix.mul_assoc _ _ _

theorem intertwining (W : Matrix (Bool × H) (Bool × H) ℂ) (O : Matrix H H ℂ)
    (body : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H))) (cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (hW : W ∈ Matrix.unitaryGroup (Bool × H) ℂ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hbody : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit body)
    (hf : matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W body) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame O) :
    matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs) := by
  have he :=
      Qatlib.Concepts.QsvtCore.QueryLowerBound.substitute_adjoint_evaluate_cost W body
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord cs)
  have hb :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.adjoint_clean
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W body) O (hbody.evaluate_unitary hW) hO hf
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions, he.1]
  exact Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.lifted_intertwining
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W body) O hf hb cs

theorem coherent (W : Matrix (Bool × H) (Bool × H) ℂ) (O : Matrix H H ℂ)
    (body : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H))) (cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (hW : W ∈ Matrix.unitaryGroup (Bool × H) ℂ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hbody : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit body)
    (hf : matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W body) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame O) (psi : Qatlib.Foundations.PureStateMath.QState H) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs) *ᵥ (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame *ᵥ psi) =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame *ᵥ (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs *ᵥ psi) := by
  calc
    _ = matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame *ᵥ psi :=
      Matrix.mulVec_mulVec psi (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame
    _ = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs) *ᵥ psi := by
      rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.intertwining W O body cs hW hO hbody hf]
    _ = _ := (Matrix.mulVec_mulVec psi Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O cs)).symm

theorem resources (W : Matrix (Bool × H) (Bool × H) ℂ)
    (body : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H))) (cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (hbody : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit body) (hcs : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit cs) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount body * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount cs ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount cs + Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount body * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount cs := by
  have he :=
      Qatlib.Concepts.QsvtCore.QueryLowerBound.substitute_adjoint_evaluate_cost W body
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord cs)
  refine ⟨he.2.2.2 hbody (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord_wellFormed hcs), ?_, ?_⟩
  · simpa only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions,
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord_counts cs).1, Nat.mul_comm] using he.2.1
  · simpa only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions, (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord_counts cs).1, (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.liftWord_counts cs).2,
      Nat.mul_comm] using he.2.2.1

theorem inverse_intertwining
    (W : Matrix (Bool × H) (Bool × H) ℂ) (O : Matrix H H ℂ)
    (body : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H))) (cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (hW : W ∈ Matrix.unitaryGroup (Bool × H) ℂ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hbody : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit body)
    (hcs : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit cs)
    (hf : matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W body) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame = matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame O) :
    matmul (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate W (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs))) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame =
      matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs)) := by
  rw [Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_adjointCircuit,
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_adjointCircuit]
  exact Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.adjoint_clean _ _ ((Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.resources W body cs hbody hcs).1.evaluate_unitary hW)
    (hcs.evaluate_unitary hO) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.intertwining W O body cs hW hO hbody hf)

theorem inverse_resources (W : Matrix (Bool × H) (Bool × H) ℂ)
    (body : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H))) (cs : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (hbody : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit body) (hcs : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit cs) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs)) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs)) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount body * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount cs ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions body cs)) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount cs + Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount body * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount cs := by
  have hr :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.resources W body cs hbody hcs
  exact ⟨hr.1.adjointCircuit,
    (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_adjointCircuit _).trans hr.2.1,
    (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_adjointCircuit _).trans hr.2.2⟩

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution
