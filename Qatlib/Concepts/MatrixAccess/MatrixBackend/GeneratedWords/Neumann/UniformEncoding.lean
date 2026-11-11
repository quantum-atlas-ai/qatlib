/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

/-!
Uniform block encodings of finite Neumann polynomials.


The original definitions, proofs, and accounting for the same word are retained.
Known matrix macros do not establish elementary gate synthesis; input preparation,
retries, and bit costs require separate analysis.
-/

/-! Average the shared Neumann branches in the same physical flag workspace.
The explicit known preparation is the pinned coefficientPrepare Householder,
not a claim to refine the Python Hadamard gate list. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix
open scoped BigOperators Kronecker

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The exact `uniform_mass` invariant under the original hypotheses and resource conventions. -/
private theorem uniform_mass (b : ℕ) : Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (fun _ : Fin b => (1 : ℂ)) = b := by
  simp [Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass]

/-- Explicit PREPARE independent of the unknown data oracle. -/
def uniformNeumannPrepare (b : ℕ) (hb : 0 < b) :
    Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H)) ℂ :=
  Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1) (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H)
    (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare (fun _ : Fin b => (1 : ℂ)) ⟨0,hb⟩))

/-- Product order: prepare, run every paid layer and final inverse query, unprepare. -/
def uniformNeumannWord (b : ℕ) (hb : 0 < b) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H))) :=
  [.gate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannPrepare b hb)ᴴ] ++ Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.sharedNeumannWord b P ++
    [.gate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannPrepare b hb)]

/-- The actual initial/final seed, including all fresh flags, the label and F. -/
def uniformNeumannFrame (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ) :
    Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H)) I ℂ :=
  Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame (b-1) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b) * F)

/-- The exact `uniform_prepare_unitary` invariant under the original hypotheses and resource conventions. -/
private theorem uniform_prepare_unitary (b : ℕ) (hb : 0 < b) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannPrepare (H := H) b hb ∈ unitaryGroup (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H)) ℂ := by
  have hm : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (fun _ : Fin b => (1 : ℂ)) := by
    rw [uniform_mass]
    exact_mod_cast hb
  exact Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup _ ℂ).one_mem
    (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister_unitary (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare_unitary _ _ hm))

/-- Full literal costs, including both known preparation macros. -/
theorem uniform_neumann_word_cost_legal (b : ℕ) (hb : 0 < b) (P : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb P) = 2*b-1 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb P) = 2*b ∧
    (Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P → Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb P)) := by
  obtain ⟨hq,hg,hw⟩ := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.shared_neumann_word_cost_legal b hb P
  refine ⟨?_, ?_, ?_⟩
  · simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount, hq]
    omega
  · simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount, hg]
    omega
  · intro hp
    have hu := uniform_prepare_unitary (H := H) b hb
    simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
    exact ⟨⟨Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hu, hw hp⟩, hu⟩

/-- The exact `ket_fiber` invariant under the original hypotheses and resource conventions. -/
private theorem ket_fiber (b : ℕ) (hb : 0 < b) :
    Qatlib.Concepts.BlockEncoding.LCU.prepareLift (I := H) (Qatlib.Foundations.PureStateMath.Ket (⟨0,hb⟩ : Fin b)) = Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b) := by
  ext ⟨k,h⟩ i
  simp [Qatlib.Concepts.BlockEncoding.LCU.prepareLift, Qatlib.Foundations.PureStateMath.Ket, Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The exact `uniform_average` invariant under the original hypotheses and resource conventions. -/
private theorem uniform_average (b : ℕ) (hb : 0 < b)
    (V : Fin b → Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b))
      ((Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare (fun _ : Fin b => (1 : ℂ)) ⟨0,hb⟩))ᴴ *
        Qatlib.Concepts.BlockEncoding.LCU.select V * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare (fun _ : Fin b => (1 : ℂ)) ⟨0,hb⟩))
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b)) =
        ((b : ℂ)⁻¹) • ∑ k, V k := by
  have hm : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (fun _ : Fin b => (1 : ℂ)) := by
    rw [uniform_mass]
    exact_mod_cast hb
  have h := Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary_compress (fun _ : Fin b => (1 : ℂ)) V ⟨0,hb⟩ hm
  have hp : Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed (fun _ : Fin b => (1 : ℂ)) V = V := by
    funext k
    simp [Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed, Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPhase]
  simp only [Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary] at h
  rw [hp, ket_fiber] at h
  simpa only [uniform_mass, Complex.ofReal_natCast, one_div, Finset.smul_sum] using h

/-- The exact `compressed_power` invariant under the original hypotheses and resource conventions. -/
private theorem compressed_power (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (k : ℕ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress F (Uᴴ*(Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F*U*(1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^k) F =
      (Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ * (1-Qatlib.Concepts.Execution.WorkspaceCP.compress F U F*(Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ)^k := by
  have h := congrArg (fun X : Matrix H I ℂ => Fᴴ*Uᴴ*X) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_frame_power U F k)
  rw [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_frame_defect U F hU hF] at h
  simpa only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using h

/-- The actual shared program, with both preparations, encodes the mean of all
Neumann terms. No phase list, target corner or free branch oracle is supplied. -/
theorem uniform_neumann_word_encoding (b : ℕ) (hb : 0 < b)
    (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (Qatlib.Concepts.Execution.WorkspaceCP.compress F U F) b)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb F) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb F) := by
  let E := Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := Fin b × H) (fun _ : Fin (b-1) => (false,false))
  let L := Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b)
  let R := Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare (fun _ : Fin b => (1 : ℂ)) ⟨0,hb⟩)
  let W := Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U))
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.sharedNeumannWord b (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F))
  have hp := Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector_isOrthogonalProjector hF
  have hw := (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_cost_legal b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)).2.2 hp
  have hu : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U) ∈
      unitaryGroup (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H)) ℂ :=
    Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup _ ℂ).one_mem
      (Qatlib.Concepts.BlockEncoding.LCU.select_unitary _ (fun _ => hU))
  have hf : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb F) :=
    Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry _)
      (Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry _) hF)
  refine ⟨hw.evaluate_unitary hu, hf, hf, ?_⟩
  have he : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)) =
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannPrepare b hb)ᴴ * W * Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannPrepare b hb := by
    simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_append, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one]
    rfl
  have hcorner := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.shared_neumann_word_corner b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) U hU hp
  have hcompress : Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb F)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F))) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb F) =
      Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.Execution.WorkspaceCP.compress L (Rᴴ * Qatlib.Concepts.Execution.WorkspaceCP.compress E W E * R) L) F := by
    rw [he]
    simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannPrepare,
      Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.conjTranspose_mul, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose,
      Matrix.conjTranspose_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin (b-1) => (false,false)))ᴴ,
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fiber_data_left]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix (Fin (b-1) → Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair)
      (Fin (b-1) → Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair) ℂ) R), Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fiber_data]
    simp only [E, L, R, Matrix.mul_assoc]
  rw [hcompress]
  change Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.Execution.WorkspaceCP.compress L (Rᴴ * Qatlib.Concepts.Execution.WorkspaceCP.compress E W E * R) L) F = _
  rw [show Qatlib.Concepts.Execution.WorkspaceCP.compress E W E = Qatlib.Concepts.BlockEncoding.LCU.select (fun k : Fin b =>
      Uᴴ*(Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F*U*(1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^k.val) from hcorner]
  rw [uniform_average b hb]
  rw [Qatlib.Concepts.Execution.WorkspaceCP.compress_smul]
  congr 1
  calc
    Qatlib.Concepts.Execution.WorkspaceCP.compress F (∑ k : Fin b, Uᴴ*(Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F*U*(1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^k.val) F =
        ∑ k : Fin b, Qatlib.Concepts.Execution.WorkspaceCP.compress F (Uᴴ*(Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F*U*(1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^k.val) F := by
      simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_sum, Matrix.sum_mul]
    _ = (Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ * ∑ k : Fin b,
        (1-Qatlib.Concepts.Execution.WorkspaceCP.compress F U F*(Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ)^k.val := by
      simp only [compressed_power U F hU hF, Finset.mul_sum]
    _ = Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (Qatlib.Concepts.Execution.WorkspaceCP.compress F U F) b := by
      unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
      congr 1
      exact Fin.sum_univ_eq_sum_range _ b

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
