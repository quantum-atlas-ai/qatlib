/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.ShiftCoefficients
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.WeightedReciprocalError

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
set_option maxHeartbeats 1200000

set_option synthInstance.maxSize 256
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts
open Matrix Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
open scoped BigOperators Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

def slotOracle (U : Matrix H H ℂ) : Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) ℂ :=
  Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlotMatrix U)

def slotWireEquiv (H : Type) : (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) ≃ Fin 4 × (Bool × H) where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun y := ((y.2.1, y.1), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype H] [DecidableEq H] in
/-- Relabeling the slot oracle gives four parallel copies of the controlled data oracle. -/
theorem slotOracle_relabel [Fintype H] [DecidableEq H] (U : Matrix H H ℂ) :
    Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotWireEquiv H) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U) =
      Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin 4) (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle U) := by
  ext ⟨a,b,i⟩ ⟨c,d,j⟩
  by_cases ha : a = c <;> by_cases hb : b = d <;>
    simp [Qatlib.Foundations.PureStateMath.BornBridge.relabelGate, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotWireEquiv, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlotMatrix, Qatlib.Concepts.BlockEncoding.LCU.select,
      Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle, ha, hb]

/-- The slot oracle is unitary when the data oracle is unitary. -/
theorem slotOracle_unitary (U : Matrix H H ℂ) (hU : U ∈ unitaryGroup H ℂ) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U ∈ unitaryGroup (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) ℂ := by
  apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
  intro s
  cases hs :
      s.1 <;> simp only
      [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlotMatrix,
      hs, Bool.false_eq_true, ↓reduceIte]
  · exact (unitaryGroup H ℂ).one_mem
  · exact hU

def nodePrepare (α B : ℝ) (z : J → ℂ) (j : J) :
    Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) ℂ :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient (z j) α B) Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSeed)

def nodePhase (α B : ℝ) (z : J → ℂ) (j : J) :
    Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) ℂ :=
  Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient (z j) α B) (fun _ => (1 : Matrix H H ℂ)))

def nodeLeft (α B : ℝ) (z : J → ℂ) (j : J) :=
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare (H := H) α B z j)ᴴ

def shiftFrame (F : Matrix H I ℂ) :
    Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) I ℂ := Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSeed F

def normalizedShift (A : Matrix I I ℂ) (z : ℂ) (B : ℝ) : Matrix I I ℂ :=
  ((B⁻¹ : ℝ) : ℂ) • (z • (1 : Matrix I I ℂ) - A)

omit [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] in
/-- The node left, phase, and preparation gates are unitary under the scale and shift bounds. -/
theorem node_gates_unitary [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
    (α B : ℝ) (z : J → ℂ) (hα : 0 ≤ α) (hB : 0 < B)
    (hbound : ∀ j, α + ‖z j‖ ≤ B) :
    (∀ j, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodeLeft (H := H) α B z j ∈ unitaryGroup (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) ℂ) ∧
    (∀ j, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase (H := H) α B z j ∈ unitaryGroup (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) ℂ) ∧
    (∀ j, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare (H := H) α B z j ∈ unitaryGroup (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) ℂ) := by
  have hp (j : J) : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare (H := H) α B z j ∈ unitaryGroup (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.ShiftSlot × H) ℂ := by
    apply Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister_unitary
    apply Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare_unitary
    rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shift_coefficient_mass (z j) α B hα (hbound j)]
    exact hB
  refine ⟨fun j => Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary (hp j), ?_, hp⟩
  intro j
  apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
  exact Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed_unitary _ _
      (fun _ => (unitaryGroup H ℂ).one_mem)

omit [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] in
/-- The node family body matrix equals the shifted coefficient LCU unitary. -/
theorem node_body_eq_lcu [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
    (α B : ℝ) (z : J → ℂ) (U : Matrix H H ℂ) (j : J) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodeLeft α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U) j =
      Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient (z j) α B) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlotMatrix U) Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSeed := by
  have hd : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase (H := H) α B z j * Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U =
      Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftCoefficient (z j) α B) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSlotMatrix U)) := by
    rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase,
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]
    apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
    funext s
    simp [Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed]
  unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix
  rw [Matrix.mul_assoc (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodeLeft α B z j), hd]
  rfl

/-- An exact block encoding yields the normalized shifted matrix as its actual node block. -/
theorem actualNodeBlock_eq_shift (F : Matrix H I ℂ) (A : Matrix I I ℂ)
    (U : Matrix H H ℂ) (α B : ℝ) (z : J → ℂ)
    (hbe : Qatlib.Concepts.BlockEncoding.BlockEncoding A U F F α 0) (hB : 0 < B)
    (hbound : ∀ j, α + ‖z j‖ ≤ B) (j : J) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodeLeft α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare α B z)
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U) j = Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B := by
  have hAreal : A = α • Qatlib.Concepts.Execution.WorkspaceCP.compress F U F :=
    sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbe.error_le (norm_nonneg _)))
  have hA : A = (α : ℂ) • Qatlib.Concepts.Execution.WorkspaceCP.compress F U F := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at hAreal
    exact hAreal
  unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame
  rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.node_body_eq_lcu, Qatlib.Concepts.LcuPostselect.ScaledLCU.compress_tagFrame,
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shifted_lcu_compress H (z j) α B U hbe.normalization_pos.le hB (hbound j)]
  change Qatlib.Concepts.Execution.WorkspaceCP.compress F
      (((B⁻¹ : ℝ) : ℂ) • (z j • (1 : Matrix H H ℂ) - (α : ℂ) • U)) F = _
  rw [Qatlib.Concepts.Execution.WorkspaceCP.compress_smul]
  unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift
  congr 1
  simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one]
  rw [show Fᴴ * F = 1 from hbe.left_isometry]
  change z j • 1 - (α : ℂ) • Qatlib.Concepts.Execution.WorkspaceCP.compress F U F = z j • 1 - A
  rw [← hA]

def shiftedWeightedWord (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (α B : ℝ) (z : J → ℂ) (d : J → ℂ) (j₀ : J) :=
  Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weightedOriginalWord b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodeLeft α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase α B z)
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare α B z) d j₀

/-- The shifted weighted word block-encodes the weighted normalized-shift pseudoinverses with
the stated reciprocal error and linear query and gate counts. -/
theorem shiftedWeighted_encoding_error (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α B : ℝ) (z : J → ℂ)
    (hbe : Qatlib.Concepts.BlockEncoding.BlockEncoding A U F F α 0) (hB : 0 < B) (hbound : ∀ j, α + ‖z j‖ ≤ B)
    (d : J → ℂ) (j₀ : J) (hm : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d)
    (δ : J → ℝ) (hd : ∀ j, 0 < δ j) (hd1 : ∀ j, δ j ≤ 1)
    (hg : ∀ j (i : Fin (Fintype.card I)), 0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B) i →
      δ j ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B) i) :
    let O :=
        Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J)
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U))
    let W :=
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftedWeightedWord b hb F α B z d j₀
    O ∈ unitaryGroup _ ℂ ∧ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W ∧
    Qatlib.Concepts.BlockEncoding.BlockEncoding (∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F)))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F)))
      ((b : ℝ) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) (∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (δ j) b) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b := by
  have hG :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.node_gates_unitary
      (H := H) α B z hbe.normalization_pos.le hB hbound
  have hF :=
      Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame_isIsometry Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftSeed F hbe.left_isometry
  have hgap : ∀ j (i : Fin (Fintype.card I)),
      0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodeLeft α B z)
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U) j) i →
        δ j ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodeLeft α B z)
          (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U) j) i := by
    intro j i hi
    rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.actualNodeBlock_eq_shift F A U α B z hbe hB hbound] at hi ⊢
    exact hg j i hi
  have h := Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weightedOriginal_pseudoinverse_encoding b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F) hF
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodeLeft α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare α B z) hG.1 hG.2.1 hG.2.2
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle_unitary U hbe.unitary) d j₀ hm δ hd hd1 hgap
  have ht : (∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodeLeft α B z)
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePhase α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.nodePrepare α B z) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U) j)) =
      ∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.actualNodeBlock_eq_shift F A U α B z hbe hB hbound]
  rw [ht] at h
  exact h

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts
