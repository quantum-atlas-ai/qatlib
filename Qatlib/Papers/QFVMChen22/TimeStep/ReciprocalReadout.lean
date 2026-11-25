/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.SparseEncoding
public import Qatlib.Concepts.QRAM.AmplitudeAccess.UnitaryPreparation
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
public import Qatlib.Concepts.BlockEncoding.Postselection
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

/-!
# Pre-amplification linear solve on a cached residual

[ChenXueChenEtAl2022], Sections 3.2–3.3, load their signed residual from
QRAM, solve the linearized system and measure a solution register. The
fixed-length Chebyshev circuit below is a block encoding of the inverse
of the normalized Hermitian stencil. We apply it to the residual branch
and prove when postselection succeeds and how accurately it normalizes
the inverse applied to that state. Variable-time amplification and
signed classical tomography are separate parts of the algorithm.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.BlockEncoding (BlockEncoding)
open Qatlib.Concepts.BlockEncoding.LCU (prepareLift prepareLift_isIsometry)
open Qatlib.Concepts.BlockEncoding.Postselection (stateVector IsNormalizedApplication
  normalized_iff_stateVector_norm stateVector_mulVec_norm_le)
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.Execution.WorkspaceCP (IsIsometry compress)
open Qatlib.Concepts.QsvtCore.PhaseExistence (sparseAlpha blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Concepts.BlockEncoding.EncodingCore (relabelGate_mem_unitary)
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend (relabelState_ket)
open Qatlib.Concepts.WalkSearch.Spectral (basisColumns basisColumns_adjoint_mul
  eq_spectralDiagonal_of_action spectralDiagonal spectralDiagonal_const spectralDiagonal_norm_le)
open Qatlib.Foundations.PureStateMath (ApplyGate Ket Normalized QState ZeroStr applyGate_one
  normalized_applyGate normalized_ket)
open Qatlib.Foundations.PureStateMath.BornBridge (relabelGate applyGate_relabelGate)
open Qatlib.Foundations.MatrixAlgebra.HermitianLift (lift_adjoint)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass)
open Qatlib.Concepts.QRAM.AmplitudeAccess (pathAmplitude
  signedTreePreparation signed_tree_preparation_unitary signed_tree_preparation_apply applyGate_blockDiagFirst_slice)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry Snapshot)
open scoped BigOperators Classical Matrix.Norms.L2Operator

variable {depth columnSlots : ℕ}

/-- The signed residual occupies the left half of the lifted stencil register. -/
def liftedResidual (residual : Tree ℝ depth) : QState (Address depth ⊕ Address depth) :=
  Sum.elim (fun row => (pathAmplitude residual row : ℂ)) 0

/-- The residual preparation acts by the signed QRAM loader on the left half of the dilation. -/
def liftedResidualPreparation (residual : Tree ℝ depth) :
    Matrix (Address depth ⊕ Address depth) (Address depth ⊕ Address depth) ℂ :=
  relabelGate (Equiv.boolProdEquivSum (Address depth))
    (blockDiagFirst (fun bit => if bit then 1 else signedTreePreparation residual))

/-- The lifted QRAM residual preparation is unitary. -/
theorem lifted_residual_preparation_unitary (residual : Tree ℝ depth) (h : Valid residual) :
    liftedResidualPreparation residual ∈ Matrix.unitaryGroup (Address depth ⊕ Address depth) ℂ := by
  unfold liftedResidualPreparation
  apply relabelGate_mem_unitary
  apply blockDiagFirst_unitary
  intro bit
  cases bit
  · exact signed_tree_preparation_unitary residual h
  · exact (Matrix.unitaryGroup (Address depth) ℂ).one_mem

/-- Loading the residual into a clean left address gives the state consumed by the inverse solve. -/
theorem lifted_residual_preparation_apply (residual : Tree ℝ depth) (h : Valid residual)
    (hMass : 0 < mass residual) :
    ApplyGate (liftedResidualPreparation residual) (Ket (Sum.inl (ZeroStr depth))) = liftedResidual residual := by
  let e := Equiv.boolProdEquivSum (Address depth)
  let blocks (b : Bool) := if b then (1 : Matrix (Address depth) (Address depth) ℂ)
    else signedTreePreparation residual
  change ApplyGate (relabelGate e (blockDiagFirst blocks)) (Ket (e (false, ZeroStr depth))) = _
  rw [← relabelState_ket e (false, ZeroStr depth), applyGate_relabelGate]
  funext side
  cases side with
  | inl row =>
    change ApplyGate (blockDiagFirst blocks) (Ket (false, ZeroStr depth)) (false, row) = _
    rw [applyGate_blockDiagFirst_slice]
    have hSlice : (fun j => Ket (false, ZeroStr depth) (false, j)) = Ket (ZeroStr depth) := by
      funext j
      simp [Ket]
    rw [hSlice]
    exact signed_tree_preparation_apply residual h hMass row
  | inr row =>
    change ApplyGate (blockDiagFirst blocks) (Ket (false, ZeroStr depth)) (true, row) = _
    rw [applyGate_blockDiagFirst_slice]
    change ApplyGate 1 (fun j => Ket (false, ZeroStr depth) (true, j)) row = 0
    simp [applyGate_one, Ket]

/-- A positive, valid residual cache loads a unit state on the lifted register. -/
theorem lifted_residual_normalized (residual : Tree ℝ depth)
    (hValid : Valid residual) (hMass : 0 < mass residual) : Normalized (liftedResidual residual) := by
  rw [← lifted_residual_preparation_apply residual hValid hMass]
  exact normalized_applyGate (lifted_residual_preparation_unitary residual hValid) (normalized_ket _)

/-- The frame for measuring success requires both the clean LCU label and the range of the
stencil walk frame. -/
def stencilSuccessFrame (condition precision : ℝ) (depth : ℕ) {rowSlots columnSlots : ℕ}
    (rowScratch : Fin rowSlots) (columnScratch : Fin columnSlots) :
    Matrix (ReciprocalTerm condition precision × StencilWorkspace depth rowSlots columnSlots)
      (Address depth ⊕ Address depth) ℂ :=
  prepareLift (Ket (0 : ReciprocalTerm condition precision)) *
    stencilWalkFrame depth rowScratch columnScratch

/-- The LCU preparation frame and the stencil frame compose isometrically. -/
private theorem stencil_success_frame_isometry (condition precision : ℝ) (depth : ℕ)
    {rowSlots columnSlots : ℕ} (rowScratch : Fin rowSlots) (columnScratch : Fin columnSlots)
    (hFrame : IsIsometry (stencilWalkFrame depth rowScratch columnScratch)) :
    IsIsometry (stencilSuccessFrame condition precision depth rowScratch columnScratch) := by
  let ket := Ket (0 : ReciprocalTerm condition precision)
  have hKet : IsIsometry (prepareLift (I := StencilWorkspace depth rowSlots columnSlots) ket) := by
    apply prepareLift_isIsometry
    simp [ket, Ket]
  have h := hKet
  unfold IsIsometry at h hFrame ⊢
  unfold stencilSuccessFrame
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc
    (stencilWalkFrame depth rowScratch columnScratch)ᴴ, h, Matrix.mul_one, hFrame]

/-- Specialize the reciprocal unitary to the data of the current stencil. -/
def stencilReciprocalCircuit (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (entryScale condition precision : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columnSlots) :
    Matrix (ReciprocalTerm condition precision × StencilWorkspace depth geometry.stencilSize columnSlots)
      (ReciprocalTerm condition precision × StencilWorkspace depth geometry.stencilSize columnSlots) ℂ :=
  reciprocalUnitary condition precision (stencilWalkFrame depth rowScratch columnScratch)
    (stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch)

/-- The lifted stencil is Hermitian for every stencil and scale. -/
theorem stencil_signal_hermitian (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale : ℝ) :
    (stencilSignal geometry coefficients scale).IsHermitian :=
  lift_adjoint _

/-- Diagonalize the normalized Hermitian stencil and reciprocate its real eigenvalues. -/
def stencilSpectralInverse (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale : ℝ) :
    Matrix (Address depth ⊕ Address depth) (Address depth ⊕ Address depth) ℂ :=
  let h := stencil_signal_hermitian geometry coefficients scale
  spectralDiagonal h.eigenvectorBasis fun j => (h.eigenvalues j : ℂ)⁻¹

/-- The Hermitian stencil acts on each column of its orthonormal eigenbasis by the real
eigenvalue of that column. -/
theorem stencil_eigenbasis_action (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale : ℝ)
    (j : Address depth ⊕ Address depth) :
    let T := stencilSignal geometry coefficients scale
    let h := stencil_signal_hermitian geometry coefficients scale
    T.toEuclideanLin (h.eigenvectorBasis j) = (h.eigenvalues j : ℂ) • h.eigenvectorBasis j := by
  let h := stencil_signal_hermitian geometry coefficients scale
  apply PiLp.ext
  intro i
  simpa only [Matrix.toLpLin_apply, PiLp.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
    Pi.smul_apply] using! congrFun (h.mulVec_eigenvectorBasis j) i

/-- Products in a common orthonormal spectral basis multiply the diagonal coefficients. -/
theorem spectral_diagonal_mul {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (basis : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) (f g : J → ℂ) :
    spectralDiagonal basis f * spectralDiagonal basis g =
      spectralDiagonal basis (fun j => f j * g j) := by
  let B := basisColumns basis
  change (B * diagonal f * Bᴴ) * (B * diagonal g * Bᴴ) =
    B * diagonal (fun j => f j * g j) * Bᴴ
  calc
    _ = B * diagonal f * (Bᴴ * B) * diagonal g * Bᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [basisColumns_adjoint_mul basis, Matrix.mul_one, Matrix.mul_assoc B, diagonal_mul_diagonal]

/-- A signed spectral gap excludes zero eigenvalues, so the spectral reciprocal is a
two-sided inverse of the normalized stencil. -/
theorem stencil_spectral_inverse_mul (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale condition : ℝ)
    (hCondition : 1 < condition)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients scale).eigenvalues j| ∈
      Set.Icc condition⁻¹ 1) :
    let T := stencilSignal geometry coefficients scale
    let X := stencilSpectralInverse geometry coefficients scale
    X * T = 1 ∧ T * X = 1 := by
  let T := stencilSignal geometry coefficients scale
  let h := stencil_signal_hermitian geometry coefficients scale
  let eigenvalue : Address depth ⊕ Address depth → ℂ := fun j => h.eigenvalues j
  let X := spectralDiagonal h.eigenvectorBasis fun j => (eigenvalue j)⁻¹
  have hT : T = spectralDiagonal h.eigenvectorBasis eigenvalue :=
    eq_spectralDiagonal_of_action h.eigenvectorBasis T eigenvalue
      (stencil_eigenbasis_action geometry coefficients scale)
  have hNonzero (j : Address depth ⊕ Address depth) : eigenvalue j ≠ 0 := by
    have hPos : 0 < |h.eigenvalues j| :=
      (inv_pos.mpr (zero_lt_one.trans hCondition)).trans_le (hGap j).1
    exact Complex.ofReal_ne_zero.mpr (abs_pos.mp hPos)
  have hLeft : (fun j => (eigenvalue j)⁻¹ * eigenvalue j) = fun _ => 1 :=
    funext fun j => inv_mul_cancel₀ (hNonzero j)
  have hRight : (fun j => eigenvalue j * (eigenvalue j)⁻¹) = fun _ => 1 :=
    funext fun j => mul_inv_cancel₀ (hNonzero j)
  change X * T = 1 ∧ T * X = 1
  simp [X, hT, spectral_diagonal_mul, hLeft, hRight, spectralDiagonal_const]

/-- The spectral upper bound makes the stencil a contraction. Its inverse therefore maps
any unit residual to a vector of norm at least one. -/
theorem stencil_inverse_output_norm_ge_one (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale condition : ℝ)
    (hCondition : 1 < condition)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients scale).eigenvalues j| ∈
      Set.Icc condition⁻¹ 1)
    (ψ : QState (Address depth ⊕ Address depth)) (hNormalized : Normalized ψ) :
    1 ≤ ‖stateVector (stencilSpectralInverse geometry coefficients scale *ᵥ ψ)‖ := by
  let T := stencilSignal geometry coefficients scale
  let X := stencilSpectralInverse geometry coefficients scale
  let h := stencil_signal_hermitian geometry coefficients scale
  have hT : T = spectralDiagonal h.eigenvectorBasis (fun j => (h.eigenvalues j : ℂ)) :=
    eq_spectralDiagonal_of_action h.eigenvectorBasis T _
      (stencil_eigenbasis_action geometry coefficients scale)
  have hContract : ‖T‖ ≤ 1 := by
    rw [hT]
    apply spectralDiagonal_norm_le _ _ zero_le_one
    intro j
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hGap j).2
  have hRestore : T *ᵥ (X *ᵥ ψ) = ψ := by
    rw [Matrix.mulVec_mulVec,
      (stencil_spectral_inverse_mul geometry coefficients scale condition hCondition hGap).2,
      Matrix.one_mulVec]
  calc
    1 = ‖stateVector (T *ᵥ (X *ᵥ ψ))‖ := by
      rw [hRestore, (normalized_iff_stateVector_norm ψ).mp hNormalized]
    _ ≤ ‖T‖ * ‖stateVector (X *ᵥ ψ)‖ := stateVector_mulVec_norm_le T _
    _ ≤ ‖stateVector (X *ᵥ ψ)‖ := mul_le_of_le_one_left (norm_nonneg _) hContract

/-- For a signed spectral gap in the normalized stencil, the circuit is an approximate block
encoding of its inverse with error at most twice the requested Chebyshev tolerance. -/
theorem stencil_reciprocal_block_encoding (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (entryScale condition precision : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columnSlots)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columnSlots)
    (hCondition : 1 < condition) (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columnSlots)).eigenvalues j| ∈
        Set.Icc condition⁻¹ 1) :
    BlockEncoding
      (stencilSpectralInverse geometry coefficients (entryScale * sparseAlpha geometry.stencilSize columnSlots))
      (stencilReciprocalCircuit geometry coefficients entryScale condition precision rowScratch columnScratch)
      (stencilSuccessFrame condition precision depth rowScratch columnScratch)
      (stencilSuccessFrame condition precision depth rowScratch columnScratch)
      (reciprocalMass condition precision) (2 * precision) := by
  let scale := entryScale * sparseAlpha geometry.stencilSize columnSlots
  let C := stencilWalkFrame depth rowScratch columnScratch
  let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
  let h := stencil_signal_hermitian geometry coefficients scale
  have hWire := stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  have hC : Cᴴ * C = 1 := hWire.1
  have hFrame := stencil_success_frame_isometry condition precision depth rowScratch columnScratch hC
  have hMass := reciprocal_mass_pos condition precision hCondition hPrecision hHalf
  have hUnitary := reciprocal_unitary_mem condition precision C U hC hWire.2.1 hWire.2.2.1 hMass
  refine ⟨hUnitary, hFrame, hFrame, hMass, mul_nonneg zero_le_two hPrecision.le, ?_⟩
  have hEigen : ∀ j, (Qatlib.Concepts.PolynomialCalc.QubitizedPower.signal C U).toEuclideanLin
      (h.eigenvectorBasis j) = (h.eigenvalues j : ℂ) • h.eigenvectorBasis j := by
    intro j
    rw [hWire.2.2.2]
    exact stencil_eigenbasis_action geometry coefficients scale j
  have hError := reciprocal_clean_block_error condition precision hCondition hPrecision hHalf
    C U hC hWire.2.2.1 h.eigenvectorBasis h.eigenvalues hEigen hGap
  let P := prepareLift (I := StencilWorkspace depth geometry.stencilSize columnSlots)
    (Ket (0 : ReciprocalTerm condition precision))
  have hCompress :
      compress (stencilSuccessFrame condition precision depth rowScratch columnScratch)
        (stencilReciprocalCircuit geometry coefficients entryScale condition precision rowScratch columnScratch)
        (stencilSuccessFrame condition precision depth rowScratch columnScratch) =
      Cᴴ * compress P (reciprocalUnitary condition precision C U) P * C := by
    change (P * C)ᴴ * reciprocalUnitary condition precision C U * (P * C) = _
    simp only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [norm_sub_rev, hCompress]
  change ‖reciprocalMass condition precision •
      (Cᴴ * compress P (reciprocalUnitary condition precision C U) P * C) -
        spectralDiagonal h.eigenvectorBasis (fun j => (h.eigenvalues j : ℂ)⁻¹)‖ ≤ _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact hError

/-- Applied to the current QRAM residual, the solve has positive success probability and a
normalized inverse-state error bound for Chebyshev tolerance below one half. -/
theorem stencil_reciprocal_residual_readout (geometry : Geometry depth)
    (linearize : Address depth → (Fin geometry.stencilSize → ℝ) → Fin geometry.stencilSize → ℝ)
    (snapshot : Snapshot depth) (entryScale condition precision : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columnSlots)
    (hValid : Valid snapshot.residual) (hMass : 0 < mass snapshot.residual)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column,
      |stencilMatrix geometry (rowCoefficient geometry linearize snapshot) row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columnSlots)
    (hCondition : 1 < condition) (hPrecision : 0 < precision) (hHalf : precision < 1 / 2)
    (hGap : ∀ j, |(stencil_signal_hermitian geometry (rowCoefficient geometry linearize snapshot)
      (entryScale * sparseAlpha geometry.stencilSize columnSlots)).eigenvalues j| ∈
        Set.Icc condition⁻¹ 1) :
    let coefficients := rowCoefficient geometry linearize snapshot
    let ψ := liftedResidual snapshot.residual
    let X := stencilSpectralInverse geometry coefficients (entryScale * sparseAlpha geometry.stencilSize columnSlots)
    let circuit := stencilReciprocalCircuit geometry coefficients entryScale condition precision rowScratch columnScratch
    let frame := stencilSuccessFrame condition precision depth rowScratch columnScratch
    0 < postselectionProbability circuit frame frame ψ ∧
      ∃ φ, postselectionOutput circuit frame frame ψ = some φ ∧
        IsNormalizedApplication X ψ φ (2 * (2 * precision) / ‖stateVector (X *ᵥ ψ)‖) := by
  have hNormalized := lifted_residual_normalized snapshot.residual hValid hMass
  have hInverse := stencil_inverse_output_norm_ge_one geometry (rowCoefficient geometry linearize snapshot)
    (entryScale * sparseAlpha geometry.stencilSize columnSlots) condition hCondition hGap _ hNormalized
  have hPrecision' : 2 * precision < 1 := by linarith
  exact BlockEncoding.postselection_output_of_gap
    (stencil_reciprocal_block_encoding geometry (rowCoefficient geometry linearize snapshot)
      entryScale condition precision rowScratch columnScratch hScale hEntry hColumns
      hCondition hPrecision hHalf.le hGap)
    hNormalized (hPrecision'.trans_le hInverse)

end Qatlib.Papers.QFVMChen22.TimeStep
