/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.WeightedOriginalOracle
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NativeNeumannLogCutoff

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

def actualNodeBlock (F : Matrix H I ℂ) (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (U : Matrix H H ℂ) (j : J) : Matrix I I ℂ :=
  Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix G₁ G₂ G₃ U j) F

omit [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] in
/-- An actual node block obtained by isometric compression of unitary family gates has norm at
most one. -/
theorem actualNodeBlock_norm_le_one [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F)
    (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (j : J) :
    ‖Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j‖ ≤ 1 := by
  have hv : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix G₁ G₂ G₃ U j ∈ unitaryGroup H ℂ :=
    (unitaryGroup H ℂ).mul_mem
      ((unitaryGroup H ℂ).mul_mem ((unitaryGroup H ℂ).mul_mem (h₁ j) (h₂ j)) hU) (h₃ j)
  exact (Qatlib.Concepts.BlockEncoding.Encoding.compress_norm_le hF hF _).trans
      (Qatlib.Concepts.BlockEncoding.Encoding.unitary_norm_le_one hv)

/-- The error of the weighted Neumann sum relative to the weighted pseudoinverse sum is bounded
by the weighted reciprocal errors. -/
theorem weighted_actual_polynomial_error (b : ℕ)
    (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (d : J → ℂ) (δ : J → ℝ)
    (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hgap : ∀ j (i : Fin (Fintype.card I)),
      0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) i →
        δ j ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) i) :
    ‖(∑ j, d j • Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) b) -
      ∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j)‖ ≤
      ∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (δ j) b := by
  have he (j : J) :
      ‖Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) b -
        Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j)‖ ≤ Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (δ j) b := by
    rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann_eq_reciprocalMatrixApprox]
    exact Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalMatrixApprox_error_le _ (hδ j) (hδ1 j)
      (fun i => (Qatlib.Concepts.WalkSearch.Spectral.matrixSingularValues_le_spectralNorm _ i).trans
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock_norm_le_one F hF G₁ G₂ G₃ h₁ h₂ h₃ U hU j)) (hgap j) b
  calc
    _ = ‖∑ j, d j • (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) b -
        Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j))‖ := by
      simp only [smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ j, ‖d j • (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) b -
        Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j))‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (he j) (norm_nonneg _)

/-- The weighted original word block-encodes the weighted actual-node pseudoinverses with the
stated scale, reciprocal error, and resource counts. -/
theorem weightedOriginal_pseudoinverse_encoding (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (d : J → ℂ) (j₀ : J) (hmass : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d)
    (δ : J → ℝ) (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hgap : ∀ j (i : Fin (Fintype.card I)),
      0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) i →
        δ j ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) i) :
    let O :=
        Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J)
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U)
    let W :=
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weightedOriginalWord b hb F G₁ G₂ G₃ d j₀
    O ∈ unitaryGroup _ ℂ ∧ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W ∧
    Qatlib.Concepts.BlockEncoding.BlockEncoding (∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F))
      ((b : ℝ) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) (∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (δ j) b) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b := by
  have hw :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weightedOriginal_encoding_cost b hb F hF G₁ G₂ G₃ h₁ h₂ h₃ U hU d j₀ hmass
  have hp := hw.2.2.1
  have herr :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weighted_actual_polynomial_error b F hF G₁ G₂ G₃ h₁ h₂ h₃ U hU d δ hδ hδ1 hgap
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hmc : (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d : ℂ) ≠ 0 := by
    exact_mod_cast hmass.ne'
  have hscale : ((b : ℝ) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) •
      (∑ j, (d j / (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d : ℂ)) •
        (((b : ℂ)⁻¹) • Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) b)) =
      ∑ j, d j • Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) b := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ext x y
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_natCast]
    field_simp [hbc, hmc]
  refine ⟨hw.1, hw.2.1, ?_, hw.2.2.2.1, hw.2.2.2.2⟩
  refine ⟨hp.unitary, hp.left_isometry, hp.right_isometry,
    mul_pos (Nat.cast_pos.mpr hb) hmass, (norm_nonneg _).trans herr, ?_⟩
  rw [hp.encoded]
  change ‖_ - ((b : ℝ) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) •
    (∑ j, (d j / (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d : ℂ)) •
      (((b : ℂ)⁻¹) • Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) b))‖ ≤ _
  rw [hscale, norm_sub_rev]
  exact herr

def precisionCutoff (K k : ℕ) : ℕ := K*K*(k + Nat.clog 2 K + 2)

/-- The precision cutoff is positive when `K` is at least two. -/
theorem precisionCutoff_pos {K : ℕ} (hK : 2 ≤ K) (k : ℕ) : 0 < Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff K k := by
  unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff
  have : 0 < K := by omega
  positivity

/-- The precision cutoff gives a weighted pseudoinverse encoding whose error is coefficient mass
times the stated inverse power of two. -/
theorem weightedOriginal_precision (K k : ℕ) (hK : 2 ≤ K)
    (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (d : J → ℂ) (j₀ : J) (hmass : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d)
    (hgap : ∀ j (i : Fin (Fintype.card I)),
      0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) i →
        (K : ℝ)⁻¹ ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) i) :
    let b := Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff K k
    let O :=
        Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J)
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U)
    let W :=
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weightedOriginalWord b
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff_pos hK k) F G₁ G₂ G₃ d j₀
    O ∈ unitaryGroup _ ℂ ∧ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W ∧
    Qatlib.Concepts.BlockEncoding.BlockEncoding (∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff_pos hK k) F))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff_pos hK k) F))
      ((b : ℝ) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d * ((2 : ℝ)⁻¹)^(k+2)) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hKi : (K : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hKp).mpr (by exact_mod_cast (by omega : 1 ≤ K))
  have h := Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weightedOriginal_pseudoinverse_encoding (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff K k) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff_pos hK k)
    F hF G₁ G₂ G₃ h₁ h₂ h₃ U hU d j₀ hmass (fun _ => (K : ℝ)⁻¹)
    (fun _ => inv_pos.mpr hKp) (fun _ => hKi) hgap
  refine ⟨h.1, h.2.1, h.2.2.1.mono ?_, h.2.2.2.1, h.2.2.2.2⟩
  calc
    (∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (K : ℝ)⁻¹ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.precisionCutoff K k)) ≤
        ∑ j, ‖d j‖ * ((2 : ℝ)⁻¹)^(k+2) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.LogarithmicReciprocalTail.logarithmic_reciprocal_tail K k hK) (norm_nonneg _)
    _ = Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d * ((2 : ℝ)⁻¹)^(k+2) := by rw [← Finset.sum_mul]; rfl

/-- For an invertible matrix, the matrix pseudoinverse equals the ring inverse. -/
theorem pseudoinverse_eq_ringInverse (S : Matrix I I ℂ) (hS : IsUnit S) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse S = Ring.inverse S := by
  apply Eq.symm
  apply Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse_unique S (Ring.inverse S)
  · rw [Ring.mul_inverse_cancel S hS, Matrix.one_mul]
  · rw [Ring.inverse_mul_cancel S hS, Matrix.one_mul]
  · rw [Ring.mul_inverse_cancel S hS, Matrix.conjTranspose_one]
  · rw [Ring.inverse_mul_cancel S hS, Matrix.conjTranspose_one]

/-- For invertible actual node blocks, the weighted original word encodes their weighted
inverses with the stated reciprocal error and resource counts. -/
theorem weightedOriginal_inverse_encoding (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (d : J → ℂ) (j₀ : J) (hmass : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d)
    (δ : J → ℝ) (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hgap : ∀ j (i : Fin (Fintype.card I)),
      0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) i →
        δ j ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) i)
    (hinv : ∀ j, IsUnit (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j)) :
    let O :=
        Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J)
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U)
    let W :=
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weightedOriginalWord b hb F G₁ G₂ G₃ d j₀
    O ∈ unitaryGroup _ ℂ ∧ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W ∧
    Qatlib.Concepts.BlockEncoding.BlockEncoding (∑ j, d j • Ring.inverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F))
      ((b : ℝ) * Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) (∑ j, ‖d j‖ * Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalError (δ j) b) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b := by
  have h := Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weightedOriginal_pseudoinverse_encoding b hb F hF G₁ G₂ G₃ h₁ h₂ h₃ U hU
    d j₀ hmass δ hδ hδ1 hgap
  have ht : (∑ j, d j • Qatlib.Concepts.CoherentSim.CoherentOAA.matrixPseudoinverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j)) =
      ∑ j, d j • Ring.inverse (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.actualNodeBlock F G₁ G₂ G₃ U j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.pseudoinverse_eq_ringInverse _ (hinv j)]
  rw [ht] at h
  exact h

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
