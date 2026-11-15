/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.UniformEncoding
public import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

def uniformNeumannOracle (b : ℕ) (U : Matrix H H ℂ) :
    Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H))
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H)) ℂ :=
  Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U)

def familyBodyWord (G₁ G₂ G₃ : J → Matrix H H ℂ) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × H)) :=
  [.gate (Qatlib.Concepts.BlockEncoding.LCU.select G₁), .gate (Qatlib.Concepts.BlockEncoding.LCU.select G₂), .forward, .gate (Qatlib.Concepts.BlockEncoding.LCU.select G₃)]

def familyBodyMatrix (G₁ G₂ G₃ : J → Matrix H H ℂ) (U : Matrix H H ℂ) (j : J) :
    Matrix H H ℂ := G₁ j * G₂ j * U * G₃ j

/-- Evaluating the family body word with the parallel oracle gives the selected family body
matrices. -/
theorem familyBody_evaluate (G₁ G₂ G₃ : J → Matrix H H ℂ) (U : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyWord G₁ G₂ G₃) =
      Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix G₁ G₂ G₃ U) := by
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]
  apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
  funext j
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix,
      Matrix.mul_assoc]

/-- The family body word is well formed when all three gate families are unitary. -/
theorem familyBody_legal (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyWord G₁ G₂ G₃) := by
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
  exact ⟨Qatlib.Concepts.BlockEncoding.LCU.select_unitary G₁ h₁,
      Qatlib.Concepts.BlockEncoding.LCU.select_unitary G₂ h₂, Qatlib.Concepts.BlockEncoding.LCU.select_unitary G₃ h₃⟩

def labelFrame (F : Matrix H I ℂ) : Matrix (J × H) (J × I) ℂ :=
  (1 : Matrix J J ℂ) ⊗ₖ F

omit [DecidableEq H] [Fintype I] in

/-- Adding a label register to an isometric frame preserves isometry. -/
theorem labelFrame_isometry (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F) := by
  unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, hF, Matrix.one_kronecker_one]

private def rectLabelLift {M N L : Type} [DecidableEq L]
    (V : L → Matrix M N ℂ) : Matrix (L × M) (L × N) ℂ :=
  (Matrix.blockDiagonal V).submatrix (Equiv.prodComm L M) (Equiv.prodComm L N)

/-- The conjugate transpose of a rectangular label lift is the lift of the pointwise conjugate
transposes. -/
private theorem rectLabelLift_adjoint {M N L : Type} [DecidableEq L]
    (V : L → Matrix M N ℂ) :
    (rectLabelLift V)ᴴ = rectLabelLift (fun j => (V j)ᴴ) := by
  simp only [rectLabelLift, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose]

/-- Rectangular label lifting preserves compatible pointwise matrix products. -/
private theorem rectLabelLift_mul {M N P L : Type}
    [Fintype N] [Fintype L] [DecidableEq L]
    (V : L → Matrix M N ℂ) (W : L → Matrix N P ℂ) :
    rectLabelLift (fun j => V j * W j) = rectLabelLift V * rectLabelLift W := by
  unfold rectLabelLift
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]

/-- For square matrices, rectangular label lifting agrees with `select`. -/
private theorem rectLabelLift_select {L M : Type} [DecidableEq L]
    (V : L → Matrix M M ℂ) : rectLabelLift V = Qatlib.Concepts.BlockEncoding.LCU.select V := by
  rfl

omit [Fintype J] [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] in

/-- The label frame is the rectangular label lift of the constant frame family. -/
private theorem labelFrame_eq_lift (F : Matrix H I ℂ) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F = rectLabelLift (fun _ : J => F) := by
  ext ⟨j,h⟩ ⟨k,i⟩
  by_cases hj : j = k <;>
    simp [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame,
        rectLabelLift, Matrix.blockDiagonal, hj]

omit [DecidableEq H] [Fintype I] [DecidableEq I] in

/-- Compression of a selected family by the label frame is the selection of the individually
compressed matrices. -/
theorem labelFrame_compress_select (F : Matrix H I ℂ) (V : J → Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F) (Qatlib.Concepts.BlockEncoding.LCU.select V) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F) =
      Qatlib.Concepts.BlockEncoding.LCU.select (fun j => Qatlib.Concepts.Execution.WorkspaceCP.compress F (V j) F) := by
  simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, labelFrame_eq_lift, ← rectLabelLift_select,
    rectLabelLift_adjoint, ← rectLabelLift_mul]

omit [Fintype J] [Fintype H] [DecidableEq H] in

/-- Subtracting selected families equals selecting their pointwise differences. -/
private theorem select_sub_family (U V : J → Matrix H H ℂ) :
    Qatlib.Concepts.BlockEncoding.LCU.select U - Qatlib.Concepts.BlockEncoding.LCU.select V = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => U j - V j) := by
  ext ⟨j,h⟩ ⟨k,i⟩
  by_cases hj : j = k <;> simp [Qatlib.Concepts.BlockEncoding.LCU.select, hj]

omit [Fintype J] [Fintype H] [DecidableEq H] in

/-- A finite sum of selected families equals the selection of their pointwise sums. -/
private theorem select_sum_family {K : Type} (s : Finset K) (U : K → J → Matrix H H ℂ) :
    (∑ k ∈ s, Qatlib.Concepts.BlockEncoding.LCU.select (U k)) = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => ∑ k ∈ s, U k j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext ⟨j,h⟩ ⟨k,i⟩
    by_cases hj : j = k <;> simp [Qatlib.Concepts.BlockEncoding.LCU.select, hj]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk, ih]
    ext ⟨j,h⟩ ⟨l,i⟩
    by_cases hj : j = l <;> simp [Qatlib.Concepts.BlockEncoding.LCU.select, hj]

/-- A power of a selected family equals the selection of the pointwise powers. -/
private theorem select_pow_family (U : J → Matrix H H ℂ) (n : ℕ) :
    (Qatlib.Concepts.BlockEncoding.LCU.select U)^n = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => (U j)^n) := by
  induction n with
  | zero => simpa using (Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_one (J := J) (H := H)).symm
  | succ n ih =>
    rw [pow_succ, ih, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]
    apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
    funext j
    rw [pow_succ]

/-- The left-defect Neumann polynomial commutes with selecting a matrix family. -/
theorem leftDefectNeumann_select (U : J → Matrix H H ℂ) (b : ℕ) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.BlockEncoding.LCU.select U) b = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (U j) b) := by
  unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann
  have hdef : 1 - Qatlib.Concepts.BlockEncoding.LCU.select U * (Qatlib.Concepts.BlockEncoding.LCU.select U)ᴴ = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => 1 - U j * (U j)ᴴ) := by
    rw [Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_adjoint, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul,
      ← Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_one (J := J) (H := H), select_sub_family]
  rw [hdef]
  simp only [Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_adjoint, select_pow_family,
      select_sum_family, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]

def sharedOriginalWord (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (G₁ G₂ G₃ : J → Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × (J × H)))) :=
  Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyWord G₁ G₂ G₃))
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F)))

omit [Fintype H] in

/-- The uniform Neumann oracle of the identity is the identity. -/
private theorem oracle_one (b : ℕ) : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle (H := H) b 1 = 1 := by
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_one,
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.one_kronecker_one]

omit [DecidableEq H] in
/-- The uniform Neumann oracle construction preserves matrix multiplication. -/
private theorem oracle_mul [DecidableEq H] (b : ℕ) (U V : Matrix H H ℂ) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (U*V) = Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U * Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b V := by
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle, Qatlib.Foundations.PureStateMath.tensorGate_mul, Matrix.one_mul,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]

omit [Fintype H] [DecidableEq H] in
/-- The uniform Neumann oracle construction commutes with conjugate transpose. -/
private theorem oracle_adjoint [Fintype H] [DecidableEq H] (b : ℕ) (U : Matrix H H ℂ) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b Uᴴ = (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U)ᴴ := by
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose,
    Matrix.conjTranspose_one, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_adjoint]

/-- The uniform Neumann oracle is unitary whenever the original oracle is unitary. -/
theorem uniformNeumannOracle_unitary (b : ℕ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U ∈ unitaryGroup (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H)) ℂ :=
  Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup _ ℂ).one_mem (Qatlib.Concepts.BlockEncoding.LCU.select_unitary _ (fun _ => hU))

/-- The shared original-oracle word exactly encodes the normalized selected Neumann
approximants, with the stated query and gate counts and well-formedness. -/
theorem sharedOriginal_encoding_cost (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) :
    let O :=
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b
        (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U)
    let W :=
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedOriginalWord b hb F G₁ G₂ G₃
    O ∈ unitaryGroup _ ℂ ∧ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W ∧
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (((b : ℂ)⁻¹) • Qatlib.Concepts.BlockEncoding.LCU.select (fun j => Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann
        (Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix G₁ G₂ G₃ U j) F) b))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F))
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F)) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b-3 := by
  (try dsimp only)
  let V :=
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate
      (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U)
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyWord G₁ G₂ G₃)
  let L := Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F
  let P := Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector L
  let cs :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord b hb P
  let body :=
      Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b)
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyWord G₁ G₂ G₃)
  have hbase :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBody_legal G₁ G₂ G₃ h₁ h₂ h₃
  have hqU : Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U ∈ unitaryGroup (J × H) ℂ :=
    Qatlib.Concepts.BlockEncoding.LCU.select_unitary _ (fun _ => hU)
  have hV : V ∈ unitaryGroup (J × H) ℂ := hbase.evaluate_unitary hqU
  have hL :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame_isometry
      (J := J) F hF
  have hp := Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector_isOrthogonalProjector hL
  obtain ⟨hcq,hcg,hcw⟩ :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniform_neumann_word_cost_legal b hb P
  have hbw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit body := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle_unitary b) hbase
  have hlift := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b) (oracle_one b)
    (oracle_mul b) (oracle_adjoint b) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyWord G₁ G₂ G₃)
  obtain ⟨he,hq,hg,hw⟩ := Qatlib.Concepts.QsvtCore.QueryLowerBound.substitute_adjoint_evaluate_cost
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U)) body cs
  have ht : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U))
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedOriginalWord b hb F G₁ G₂ G₃) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b V) cs := by
    change Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate _
        (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [he, hlift]
  have hpoly :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniform_neumann_word_encoding b hb V L hV hL
  have hcomp : Qatlib.Concepts.Execution.WorkspaceCP.compress L V L = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix G₁ G₂ G₃ U j) F) := by
    dsimp only [L, V]
    rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBody_evaluate,
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame_compress_select]
  rw [hcomp,
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann_select] at hpoly
  have hbq : Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount body = 1 := by
    rw [(Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts _ _).1]
    rfl
  have hbg : Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount body = 3 := by
    rw [(Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts _ _).2]
    rfl
  refine ⟨Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle_unitary b _ hqU, hw hbw (hcw hp), ?_, ?_, ?_⟩
  · rw [ht]
    exact hpoly
  · change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hq, hcq, hbq, Nat.mul_one]
  · change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hg, hcg, hcq, hbg]
    omega

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
