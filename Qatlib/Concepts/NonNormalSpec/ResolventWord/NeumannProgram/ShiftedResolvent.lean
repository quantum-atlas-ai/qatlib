/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.ShiftedOriginalWord

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

def unscaledShift (A : Matrix I I ℂ) (z : ℂ) : Matrix I I ℂ := z • 1 - A

/-- The pseudoinverse of a nonzero scalar multiple is the inverse scalar multiple of the
pseudoinverse. -/
theorem pseudoinverse_smul (S : Matrix I I ℂ) (c : ℂ) (hc : c ≠ 0) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (c • S) = c⁻¹ • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse S := by
  have hab : (c • S) * (c⁻¹ • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse S) = S * Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse S := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hba : (c⁻¹ • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse S) * (c • S) = Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse S * S := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  apply Eq.symm
  apply Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse_unique
  · rw [hab, Matrix.mul_smul, Qatlib.Concepts.CoherentSim.CoherentOAA.mul_matrixPseudoinverse_mul]
  · rw [hba, Matrix.mul_smul, Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse_mul_self]
  · rw [hab, Qatlib.Concepts.CoherentSim.CoherentOAA.mul_matrixPseudoinverse_adjoint]
  · rw [hba, Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse_mul_adjoint]

/-- The pseudoinverse of the normalized shift is `B` times the pseudoinverse of the unscaled
shift. -/
theorem normalizedShift_pseudoinverse (A : Matrix I I ℂ) (z : ℂ) (B : ℝ) (hB : 0 < B) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A z B) =
      (B : ℂ) • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.unscaledShift A z) := by
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift
  rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.pseudoinverse_smul _ _ (by simpa using inv_ne_zero hBc)]
  simp only [Complex.ofReal_inv, inv_inv,
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.unscaledShift]

/-- Positive real rescaling of the encoded matrix rescales both the block-encoding scale and
error by the same factor. -/
theorem rescaleEncoding {T : Type} [Fintype T] [DecidableEq T]
    {A : Matrix I I ℂ} {U : Matrix T T ℂ} {L R : Matrix T I ℂ} {α ε : ℝ}
    (h : Qatlib.Concepts.BlockEncoding.BlockEncoding A U L R α ε) (c : ℝ) (hc : 0 < c) :
    Qatlib.Concepts.BlockEncoding.BlockEncoding (c • A) U L R (c*α) (c*ε) := by
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, mul_pos hc h.normalization_pos,
    mul_nonneg hc.le h.error_nonneg, ?_⟩
  calc
    _ = ‖c • (A - α • Qatlib.Concepts.Execution.WorkspaceCP.compress L U R)‖ := by rw [smul_sub, smul_smul]
    _ = c * ‖A - α • Qatlib.Concepts.Execution.WorkspaceCP.compress L U R‖ := by rw [norm_smul, Real.norm_of_nonneg hc.le]
    _ ≤ c*ε := mul_le_mul_of_nonneg_left h.error_le hc.le

/-- The shifted weighted word encodes unscaled-shift pseudoinverses with scale and reciprocal
error divided by `B`, retaining the stated resource counts. -/
theorem shiftedWeighted_unscaled_error (b : ℕ) (hb : 0 < b)
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
    Qatlib.Concepts.BlockEncoding.BlockEncoding (∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.unscaledShift A (z j)))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F)))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F)))
      (((b : ℝ)/B) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) ((∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (δ j) b) / B) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b := by
  have h :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftedWeighted_encoding_error b hb F A U α B z hbe hB hbound d j₀ hm δ hd hd1 hg
  have hs :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.rescaleEncoding h.2.2.1 B⁻¹ (inv_pos.mpr hB)
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have ht : B⁻¹ • (∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B)) =
      ∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.unscaledShift A (z j)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift_pseudoinverse A (z j) B hB]
    ext x y
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
    field_simp [hBc]
  rw [ht] at hs
  have ha :
      B⁻¹ * ((b : ℝ) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) =
      ((b : ℝ)/B) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d := by ring
  have he : B⁻¹ * (∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (δ j) b) =
      (∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (δ j) b) / B := by rw [div_eq_mul_inv, mul_comm]
  rw [ha, he] at hs
  exact ⟨h.1, h.2.1, hs, h.2.2.2.1, h.2.2.2.2⟩

/-- For invertible shifts, the shifted weighted word encodes their weighted inverses with the
stated error and resource counts. -/
theorem shiftedWeighted_inverse_error (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α B : ℝ) (z : J → ℂ)
    (hbe : Qatlib.Concepts.BlockEncoding.BlockEncoding A U F F α 0) (hB : 0 < B) (hbound : ∀ j, α + ‖z j‖ ≤ B)
    (d : J → ℂ) (j₀ : J) (hm : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d)
    (δ : J → ℝ) (hd : ∀ j, 0 < δ j) (hd1 : ∀ j, δ j ≤ 1)
    (hg : ∀ j (i : Fin (Fintype.card I)), 0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B) i →
      δ j ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B) i)
    (hinv : ∀ j, IsUnit (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.unscaledShift A (z j))) :
    let O :=
        Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J)
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U))
    let W :=
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftedWeightedWord b hb F α B z d j₀
    O ∈ unitaryGroup _ ℂ ∧ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W ∧
    Qatlib.Concepts.BlockEncoding.BlockEncoding (∑ j, d j • Ring.inverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.unscaledShift A (z j)))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F)))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F)))
      (((b : ℝ)/B) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) ((∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (δ j) b) / B) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b := by
  have h :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftedWeighted_unscaled_error b hb F A U α B z hbe hB hbound d j₀ hm δ hd hd1 hg
  have ht : (∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.unscaledShift A (z j))) =
      ∑ j, d j • Ring.inverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.unscaledShift A (z j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.pseudoinverse_eq_ringInverse _ (hinv j)]
  rw [ht] at h
  exact h

/-- The precision cutoff yields a weighted unscaled-shift pseudoinverse encoding with the stated
inverse-power-of-two error and resource counts. -/
theorem shiftedWeighted_unscaled_precision (K k : ℕ) (hK : 2 ≤ K)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α B : ℝ) (z : J → ℂ)
    (hbe : Qatlib.Concepts.BlockEncoding.BlockEncoding A U F F α 0) (hB : 0 < B) (hbound : ∀ j, α + ‖z j‖ ≤ B)
    (d : J → ℂ) (j₀ : J) (hm : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d)
    (hg : ∀ j (i : Fin (Fintype.card I)), 0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B) i →
      (K : ℝ)⁻¹ ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.normalizedShift A (z j) B) i) :
    let b := Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff K k
    let O :=
        Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J)
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.slotOracle U))
    let W :=
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftedWeightedWord b (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff_pos hK k) F α B z d j₀
    O ∈ unitaryGroup _ ℂ ∧ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W ∧
    Qatlib.Concepts.BlockEncoding.BlockEncoding (∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.unscaledShift A (z j)))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff_pos hK k) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F)))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff_pos hK k) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftFrame F)))
      (((b : ℝ)/B) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d * ((2 : ℝ)⁻¹)^(k+2) / B) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hi : (K : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hKp).mpr (by exact_mod_cast (by omega : 1 ≤ K))
  have h := Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts.shiftedWeighted_unscaled_error (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff K k) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff_pos hK k)
    F A U α B z hbe hB hbound d j₀ hm (fun _ => (K : ℝ)⁻¹)
    (fun _ => inv_pos.mpr hKp) (fun _ => hi) hg
  refine ⟨h.1, h.2.1, h.2.2.1.mono ?_, h.2.2.2.1, h.2.2.2.2⟩
  apply div_le_div_of_nonneg_right _ hB.le
  calc
    (∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (K : ℝ)⁻¹ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff K k)) ≤
        ∑ j, ‖d j‖ * ((2 : ℝ)⁻¹)^(k+2) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.LogarithmicReciprocalTail.logarithmic_reciprocal_tail K k hK) (norm_nonneg _)
    _ = Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d * ((2 : ℝ)⁻¹)^(k+2) := by rw [← Finset.sum_mul]; rfl

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.Shifts
