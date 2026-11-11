/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

/-!
# One original oracle for a multinode Neumann word


The known three-macro family is generalized to actual matrix inputs on a finite
space. The construction preserves the same original oracle and proves legality,
nodewise finite polynomial identities, and literal word costs.

Word construction does not inspect the unknown U or assume the final compressed
block. All nodes share the original U and F. Elementary synthesis of the matrix
macros, concrete production of the six auxiliary parameters, outer weighted
adaptation, and complete retry costs remain outside the theorem's scope.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The same spectator extension of the unknown U is used at every node. -/
def uniformNeumannOracle (b : ℕ) (U : Matrix H H ℂ) :
    Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H)) ℂ :=
  Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U)

/-- The original single-query body uses known node tables as gate parameters and contains no unknown U in its syntax. -/
def familyBodyWord (G₁ G₂ G₃ : J → Matrix H H ℂ) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × H)) :=
  [.gate (Qatlib.Concepts.BlockEncoding.LCU.select G₁), .gate (Qatlib.Concepts.BlockEncoding.LCU.select G₂), .forward, .gate (Qatlib.Concepts.BlockEncoding.LCU.select G₃)]

/-- Construction for family Body Matrix in the shared original oracle model. -/
def familyBodyMatrix (G₁ G₂ G₃ : J → Matrix H H ℂ) (U : Matrix H H ℂ) (j : J) :
    Matrix H H ℂ := G₁ j * G₂ j * U * G₃ j

/-- The exact `familyBody_evaluate` invariant under the original hypotheses and resource conventions. -/
theorem familyBody_evaluate (G₁ G₂ G₃ : J → Matrix H H ℂ) (U : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyWord G₁ G₂ G₃) =
      Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyMatrix G₁ G₂ G₃ U) := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]
  apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
  funext j
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyMatrix, Matrix.mul_assoc]

/-- The exact `familyBody_legal` invariant under the original hypotheses and resource conventions. -/
theorem familyBody_legal (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyWord G₁ G₂ G₃) := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
  exact ⟨Qatlib.Concepts.BlockEncoding.LCU.select_unitary G₁ h₁, Qatlib.Concepts.BlockEncoding.LCU.select_unitary G₂ h₂, Qatlib.Concepts.BlockEncoding.LCU.select_unitary G₃ h₃⟩

/-- Every node uses the same original frame; this table is neither the target matrix nor a certificate for it. -/
def labelFrame (F : Matrix H I ℂ) : Matrix (J × H) (J × I) ℂ :=
  (1 : Matrix J J ℂ) ⊗ₖ F

omit [DecidableEq H] [Fintype I] in
/-- The exact `labelFrame_isometry` invariant under the original hypotheses and resource conventions. -/
theorem labelFrame_isometry (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame (J := J) F) := by
  unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, hF, Matrix.one_kronecker_one]

/-- Construction for rect Label Lift in the shared original oracle model. -/
private def rectLabelLift {M N L : Type} [DecidableEq L]
    (V : L → Matrix M N ℂ) : Matrix (L × M) (L × N) ℂ :=
  (Matrix.blockDiagonal V).submatrix (Equiv.prodComm L M) (Equiv.prodComm L N)

/-- The exact `rectLabelLift_adjoint` invariant under the original hypotheses and resource conventions. -/
private theorem rectLabelLift_adjoint {M N L : Type} [DecidableEq L]
    (V : L → Matrix M N ℂ) :
    (rectLabelLift V)ᴴ = rectLabelLift (fun j => (V j)ᴴ) := by
  simp only [rectLabelLift, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose]

/-- The exact `rectLabelLift_mul` invariant under the original hypotheses and resource conventions. -/
private theorem rectLabelLift_mul {M N P L : Type}
    [Fintype N] [Fintype L] [DecidableEq L]
    (V : L → Matrix M N ℂ) (W : L → Matrix N P ℂ) :
    rectLabelLift (fun j => V j * W j) = rectLabelLift V * rectLabelLift W := by
  unfold rectLabelLift
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]

/-- The exact `rectLabelLift_select` invariant under the original hypotheses and resource conventions. -/
private theorem rectLabelLift_select {L M : Type} [DecidableEq L]
    (V : L → Matrix M M ℂ) : rectLabelLift V = Qatlib.Concepts.BlockEncoding.LCU.select V := by
  rfl

omit [Fintype J] [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] in
/-- The exact `labelFrame_eq_lift` invariant under the original hypotheses and resource conventions. -/
private theorem labelFrame_eq_lift (F : Matrix H I ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame (J := J) F = rectLabelLift (fun _ : J => F) := by
  ext ⟨j,h⟩ ⟨k,i⟩
  by_cases hj : j = k <;>
    simp [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame, rectLabelLift, Matrix.blockDiagonal, hj]

omit [DecidableEq H] [Fintype I] [DecidableEq I] in
/-  实际共同帧的压缩逐节点分离，包括空标签/数据空间。 -/
/-- The exact `labelFrame_compress_select` invariant under the original hypotheses and resource conventions. -/
theorem labelFrame_compress_select (F : Matrix H I ℂ) (V : J → Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame (J := J) F) (Qatlib.Concepts.BlockEncoding.LCU.select V) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame (J := J) F) =
      Qatlib.Concepts.BlockEncoding.LCU.select (fun j => Qatlib.Concepts.Execution.WorkspaceCP.compress F (V j) F) := by
  simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, labelFrame_eq_lift, ← rectLabelLift_select,
    rectLabelLift_adjoint, ← rectLabelLift_mul]

omit [Fintype J] [Fintype H] [DecidableEq H] in
/-- The exact `select_sub_family` invariant under the original hypotheses and resource conventions. -/
private theorem select_sub_family (U V : J → Matrix H H ℂ) :
    Qatlib.Concepts.BlockEncoding.LCU.select U - Qatlib.Concepts.BlockEncoding.LCU.select V = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => U j - V j) := by
  ext ⟨j,h⟩ ⟨k,i⟩
  by_cases hj : j = k <;> simp [Qatlib.Concepts.BlockEncoding.LCU.select, hj]

omit [Fintype J] [Fintype H] [DecidableEq H] in
/-- The exact `select_sum_family` invariant under the original hypotheses and resource conventions. -/
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

/-- The exact `select_pow_family` invariant under the original hypotheses and resource conventions. -/
private theorem select_pow_family (U : J → Matrix H H ℂ) (n : ℕ) :
    (Qatlib.Concepts.BlockEncoding.LCU.select U)^n = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => (U j)^n) := by
  induction n with
  | zero => simpa using (Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_one (J := J) (H := H)).symm
  | succ n ih =>
    rw [pow_succ, ih, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]
    apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
    funext j
    rw [pow_succ]

/-  原有限多项式的逐标签同值，不假设可逆性或 normality。 -/
/-- The exact `leftDefectNeumann_select` invariant under the original hypotheses and resource conventions. -/
theorem leftDefectNeumann_select (U : J → Matrix H H ℂ) (b : ℕ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (Qatlib.Concepts.BlockEncoding.LCU.select U) b = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (U j) b) := by
  unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
  have hdef : 1 - Qatlib.Concepts.BlockEncoding.LCU.select U * (Qatlib.Concepts.BlockEncoding.LCU.select U)ᴴ = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => 1 - U j * (U j)ᴴ) := by
    rw [Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_adjoint, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul,
      ← Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_one (J := J) (H := H), select_sub_family]
  rw [hdef]
  simp only [Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_adjoint, select_pow_family, select_sum_family, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]

/-- The complete emitted word depends only on the known frame, node macro tables, and cutoff, with no unknown U parameter. -/
def sharedOriginalWord (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (G₁ G₂ G₃ : J → Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × H)))) :=
  Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyWord G₁ G₂ G₃))
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame (J := J) F)))

omit [Fintype H] in
/-- The exact `oracle_one` invariant under the original hypotheses and resource conventions. -/
private theorem oracle_one (b : ℕ) : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle (H := H) b 1 = 1 := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_one,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.one_kronecker_one]

/-- The exact `oracle_mul` invariant under the original hypotheses and resource conventions. -/
private theorem oracle_mul (b : ℕ) (U V : Matrix H H ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (U*V) = Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U * Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b V := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, Qatlib.Foundations.PureStateMath.tensorGate_mul, Matrix.one_mul,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]

/-- The exact `oracle_adjoint` invariant under the original hypotheses and resource conventions. -/
private theorem oracle_adjoint (b : ℕ) (U : Matrix H H ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b Uᴴ = (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U)ᴴ := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose,
    Matrix.conjTranspose_one, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_adjoint]

/-- The exact `uniformNeumannOracle_unitary` invariant under the original hypotheses and resource conventions. -/
theorem uniformNeumannOracle_unitary (b : ℕ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U ∈ unitaryGroup (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H)) ℂ :=
  Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup _ ℂ).one_mem (Qatlib.Concepts.BlockEncoding.LCU.select_unitary _ (fun _ => hU))

/-  同一原始 U 的实际多节点 Neumann 程序、已知门合法性、逐节点目标及精确账本。 -/
/-- The exact `sharedOriginal_encoding_cost` invariant under the original hypotheses and resource conventions. -/
theorem sharedOriginal_encoding_cost (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) :
    let O := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U)
    let W := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.sharedOriginalWord b hb F G₁ G₂ G₃
    O ∈ unitaryGroup _ ℂ ∧ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W ∧
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (((b : ℂ)⁻¹) • Qatlib.Concepts.BlockEncoding.LCU.select (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
        (Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyMatrix G₁ G₂ G₃ U j) F) b))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame (J := J) F))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame (J := J) F)) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b-3 := by
  dsimp only
  let V := Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyWord G₁ G₂ G₃)
  let L := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame (J := J) F
  let P := Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector L
  let cs := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb P
  let body := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyWord G₁ G₂ G₃)
  have hbase := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBody_legal G₁ G₂ G₃ h₁ h₂ h₃
  have hqU : Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U ∈ unitaryGroup (J × H) ℂ :=
    Qatlib.Concepts.BlockEncoding.LCU.select_unitary _ (fun _ => hU)
  have hV : V ∈ unitaryGroup (J × H) ℂ := hbase.evaluate_unitary hqU
  have hL := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame_isometry (J := J) F hF
  have hp := Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector_isOrthogonalProjector hL
  obtain ⟨hcq,hcg,hcw⟩ := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_cost_legal b hb P
  have hbw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit body := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle_unitary b) hbase
  have hlift := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (oracle_one b)
    (oracle_mul b) (oracle_adjoint b) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyWord G₁ G₂ G₃)
  obtain ⟨he,hq,hg,hw⟩ := Qatlib.Concepts.QsvtCore.QueryLowerBound.substitute_adjoint_evaluate_cost
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U)) body cs
  have ht : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.sharedOriginalWord b hb F G₁ G₂ G₃) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b V) cs := by
    change Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate _ (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [he, hlift]
  have hpoly := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_encoding b hb V L hV hL
  have hcomp : Qatlib.Concepts.Execution.WorkspaceCP.compress L V L = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBodyMatrix G₁ G₂ G₃ U j) F) := by
    dsimp only [L, V]
    rw [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.familyBody_evaluate, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.labelFrame_compress_select]
  rw [hcomp, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann_select] at hpoly
  have hbq : Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount body = 1 := by
    rw [(Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts _ _).1]
    rfl
  have hbg : Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount body = 3 := by
    rw [(Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts _ _).2]
    rfl
  refine ⟨Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle_unitary b _ hqU, hw hbw (hcw hp), ?_, ?_, ?_⟩
  · rw [ht]
    exact hpoly
  · change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hq, hcq, hbq, Nat.mul_one]
  · change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit body cs) = _
    rw [hg, hcg, hcq, hbg]
    omega

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
