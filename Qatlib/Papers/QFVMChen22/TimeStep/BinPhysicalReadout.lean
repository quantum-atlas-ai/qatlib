/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.BinHistoryUncompute

@[expose] public section

/-!
# Physical readout of the staged stencil solve

For [ChenXueChenEtAl2022], Appendix C.3, select the successful
right-register output of the staged QRAM solve and erase its phase
history. The normalized state is compared with the embedded inverse
stencil solution. The error includes the forward classification,
reverse classification, and reciprocal approximation.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.InstrumentCore.Measurement (Collapse PostMeasure Projector)
open Qatlib.Foundations.MatrixAlgebra.HermitianLift (lift)
open Qatlib.Foundations.PureStateMath (Inner Ket MeasureProb QState TensorState normalized_ket)
open Qatlib.Foundations.PureStateMath.BornBridge (normalized_iff_norm_toEuclidean_fromVec toEuclidean_fromVec)
open Qatlib.Foundations.QueryWordCore.Circuit (Run)
open Qatlib.Concepts.BlockEncoding.Postselection (stateVector_mulVec_norm_le)
open Qatlib.Concepts.Execution.WorkspaceCP (IsIsometry)
open Qatlib.Concepts.PolynomialCalc.QubitizedPower (signal walk)
open Qatlib.Concepts.QlsReadoutSpec.Amplification
  (clockState extendClock legal nestedWord plainAmplitude quasinorm23 weightedCost)
open Qatlib.Concepts.QsvtCore.PhaseExistence (sparseAlpha)
open Qatlib.Concepts.ReferenceError.RefTraceError (tensorState_l2_norm)
open Qatlib.Concepts.SketchArith.GramAction (norm_toEuclidean_collapse_sub_le)
open Qatlib.Concepts.WalkSearch.Spectral (spectralDiagonal)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped BigOperators Classical Matrix.Norms.L2Operator

variable {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]

/-- The total classification budget of the phase word, weighted by the packet still running
at each test. -/
def binPhaseErrorBudget (width : Fin n → ℕ) (threshold η : Fin n → ℝ) (eigenvalue : J → ℝ) (c : J → ℂ) : ℝ :=
  ∑ t, Real.sqrt 2 * (Real.sqrt (∑ j, ‖runningBinWeight threshold eigenvalue c t.val j‖ ^ 2) *
    (1 / (2 * Real.sqrt (width t) * η t)))

/-- Embedding a packet in an isometric matrix frame and adjoining clean labels does not
increase its Euclidean error. -/
private theorem seeded_frame_error_le {M N : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (C : Matrix M N ℂ) (hC : IsIsometry C) (width : Fin n → ℕ)
    (condition : Fin n → ℝ) (precision : ℝ) (tape : PhaseTape width) (x y : QState N) :
    ‖toEuclidean_fromVec (seededBinState width condition precision tape (C *ᵥ x) -
      seededBinState width condition precision tape (C *ᵥ y))‖ ≤ ‖toEuclidean_fromVec (x - y)‖ := by
  have hDiff : seededBinState width condition precision tape (C *ᵥ x) -
      seededBinState width condition precision tape (C *ᵥ y) =
      seededBinState width condition precision tape (C *ᵥ (x - y)) := by
    rw [Matrix.mulVec_sub]
    funext p
    simp [seededBinState, TensorState, mul_sub]
  rw [hDiff, seededBinState, tensorState_l2_norm, tensorState_l2_norm,
    (normalized_iff_norm_toEuclidean_fromVec _).1 (normalized_ket tape),
    (normalized_iff_norm_toEuclidean_fromVec _).1 (normalized_ket (cleanReciprocalTape condition precision)),
    one_mul, one_mul]
  exact (stateVector_mulVec_norm_le C (x - y)).trans
    (mul_le_of_le_one_left (norm_nonneg _) (Qatlib.Concepts.BlockEncoding.Encoding.IsIsometry.norm_le_one hC))

set_option maxHeartbeats 2200000 in
/-- Decode the selected QRAM stencil output before normalization. The
forward and reverse classification budgets and the reciprocal error
control both the decoded packet and the raw success amplitude. -/
theorem stencil_bin_unnormalized_physical_readout {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (hValid : Valid residual) (hResidual : 0 < mass residual)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (width : Fin n → ℕ) (hWidth : ∀ t, 2 ≤ width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hCondition : ∀ t, 1 < condition t) (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (hCutoff : ∀ t, (condition t)⁻¹ ≤ threshold t)
    (hSignalBound : ∀ i, |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columns)).eigenvalues i| ≤ 1)
    (hSignalCovered : ∀ i, ∃ t, threshold t ≤ |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columns)).eigenvalues i|)
    (v : J → QState (StencilWorkspace depth geometry.stencilSize columns))
    (coord : QState (StencilWorkspace depth geometry.stencilSize columns) → J → ℂ)
    (phase μ : J → ℝ) (η : Fin n → ℝ)
    (hη : ∀ t, 0 < η t) (hEtaHalf : ∀ t, η t ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = μ j)
    (hMargin : ∀ t j, 2 * Real.pi * η t < abs (|μ j| - threshold t))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hWalk : ∀ j, walk (stencilWalkFrame depth rowScratch columnScratch)
      (stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch) *ᵥ v j =
        Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (hWalkCovered : ∀ j, ∃ t, threshold t ≤ |μ j|)
    (hComplete : ∀ ψ, (∑ j, coord ψ j • v j) = ψ) :
    let pos : ∀ t, 0 < width t := fun t => by have := hWidth t; omega
    let mass := commonBinMass condition precision
    let C := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    let b := liftedResidual residual
    let scale := entryScale * sparseAlpha geometry.stencilSize columns
    let H := stencil_signal_hermitian geometry coefficients scale
    let P t := spectralDiagonal H.eigenvectorBasis (fun i => binSpectralMask threshold t (H.eigenvalues i))
    let right : Matrix (Address depth ⊕ Address depth) (Address depth ⊕ Address depth) ℂ :=
      diagonal (Sum.elim 0 1)
    let z t := right *ᵥ (compressedBinReciprocal (condition t) precision mass C U *ᵥ (P t *ᵥ b))
    let target := seededBinState width condition precision (cleanPhaseTape width pos)
      (C *ᵥ ((mass : ℂ)⁻¹ • (stencilSpectralInverse geometry coefficients scale *ᵥ b)))
    let output := stencilBinOutput geometry coefficients entryScale rowScratch columnScratch
      residual width pos condition threshold precision
    let success := stencilBinSuccess rowScratch columnScratch width condition precision
    let error := binPhaseErrorBudget width threshold η μ (coord (C *ᵥ b)) +
      binPhaseErrorBudget width threshold η μ (coord (C *ᵥ (∑ t, z t))) + (2 * precision) / mass
    ‖toEuclidean_fromVec (Run 1 (stencilBinHistoryUncompute width condition threshold precision C U)
      (Collapse output success) - target)‖ ≤ error ∧
      |Real.sqrt (MeasureProb output success) - ‖toEuclidean_fromVec target‖| ≤ error := by
  intro pos α C U b scale H P right z target output success error
  let recovered := seededBinState width condition precision (cleanPhaseTape width pos) (C *ᵥ (∑ t, z t))
  let A := (((scale⁻¹ : ℝ) • stencilMatrix geometry coefficients).map Complex.ofReal)
  let c := coord (C *ᵥ b)
  let d := coord (C *ᵥ (∑ t, z t))
  let reference := idealBinReference width pos condition threshold precision C U v c μ (Fin.last n)
  let δ := binPhaseErrorBudget width threshold η μ c
  let δ' := binPhaseErrorBudget width threshold η μ d
  let inverseWord := stencilBinHistoryUncompute width condition threshold precision C U
  obtain ⟨hC, hU, hSq, hEnc⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  have hLift : signal C U = lift A := hEnc
  have hEigen (i : Address depth ⊕ Address depth) :
      (lift A).toEuclideanLin (H.eigenvectorBasis i) = (H.eigenvalues i : ℂ) • H.eigenvectorBasis i :=
    stencil_eigenbasis_action geometry coefficients scale i
  have hForward : ‖toEuclidean_fromVec (output - reference)‖ ≤ δ :=
    stencil_bin_spectral_reference_error geometry coefficients entryScale rowScratch columnScratch residual
      width hWidth condition threshold precision hScale hEntry hColumns v c phase μ η hη hEtaHalf
      hCos hMargin hOrthogonal hWalk (hComplete (C *ᵥ b))
  have hLabel : Collapse reference success =
      idealPhaseBinReference width pos condition threshold precision v d μ (Fin.last n) :=
    stencil_bin_reference_phase_labels rowScratch columnScratch U hC hU hSq A hLift H.eigenvectorBasis
      H.eigenvalues hEigen v c d phase μ b (hComplete _) hCos hWalk width pos condition threshold precision
      hWalkCovered hSignalCovered (hComplete _)
  have hObserved := (norm_toEuclidean_collapse_sub_le reference output success).trans hForward
  rw [hLabel] at hObserved
  have hUndo : ‖toEuclidean_fromVec (Run 1 inverseWord (Collapse output success) - recovered)‖ ≤ δ + δ' := by
    have he := stencil_bin_history_uncompute_error width hWidth condition threshold precision C U hC hU hSq
      v d phase μ η hη hEtaHalf hCos hMargin hOrthogonal hWalk (Collapse output success) δ hObserved
    rw [hComplete (C *ᵥ (∑ t, z t))] at he
    exact he
  have hDecoded : ‖toEuclidean_fromVec ((∑ t, z t) - (α : ℂ)⁻¹ •
      (stencilSpectralInverse geometry coefficients scale *ᵥ b))‖ ≤ (2 * precision) / α := by
    have he := (decoded_bin_right_solution_bounds A C U hC hSq hLift H.eigenvectorBasis H.eigenvalues
      hEigen condition threshold precision hCondition hPrecision hHalf hSignalCovered hSignalBound
      hCutoff b (fun _ => rfl)).1
    rw [(normalized_iff_norm_toEuclidean_fromVec b).1 (lifted_residual_normalized residual hValid hResidual),
      mul_one] at he
    exact he
  have hApprox : ‖toEuclidean_fromVec (recovered - target)‖ ≤ (2 * precision) / α :=
    (seeded_frame_error_le C hC width condition precision (cleanPhaseTape width pos) _ _).trans hDecoded
  have hTotal : ‖toEuclidean_fromVec (Run 1 inverseWord (Collapse output success) - target)‖ ≤ error := by
    change ‖toEuclidean_fromVec (Run 1 inverseWord (Collapse output success)) - toEuclidean_fromVec target‖ ≤ _
    rw [← sub_add_sub_cancel (toEuclidean_fromVec (Run 1 inverseWord (Collapse output success)))
      (toEuclidean_fromVec recovered) (toEuclidean_fromVec target)]
    exact (norm_add_le _ _).trans (add_le_add hUndo hApprox)
  exact ⟨hTotal, stencil_bin_history_success_amplitude_error width condition threshold precision
    C U hC hU hSq pos output target success error hTotal⟩

set_option maxHeartbeats 2200000 in
/-- The normalized physical readout of the QRAM-initialized solver, on the success event,
approximates the inverse stencil solution with a clean phase and coefficient tape. The same
bound holds for a legal variable-time amplified solver whose success probability is at least
`1/100` and whose oracle word obeys the weighted cost bound. The total unnormalized error must
be smaller than the ideal norm. -/
theorem stencil_bin_normalized_physical_readout {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (hValid : Valid residual) (hResidual : 0 < mass residual)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (width : Fin n → ℕ) (hWidth : ∀ t, 2 ≤ width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hn : 0 < n) (prices : ℕ → ℕ)
    (hCondition : ∀ t, 1 < condition t) (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (hCutoff : ∀ t, (condition t)⁻¹ ≤ threshold t)
    (hSignalBound : ∀ i, |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columns)).eigenvalues i| ≤ 1)
    (hSignalCovered : ∀ i, ∃ t, threshold t ≤ |(stencil_signal_hermitian geometry coefficients
      (entryScale * sparseAlpha geometry.stencilSize columns)).eigenvalues i|)
    (v : J → QState (StencilWorkspace depth geometry.stencilSize columns))
    (coord : QState (StencilWorkspace depth geometry.stencilSize columns) → J → ℂ)
    (phase μ : J → ℝ) (η : Fin n → ℝ)
    (hη : ∀ t, 0 < η t) (hEtaHalf : ∀ t, η t ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = μ j)
    (hMargin : ∀ t j, 2 * Real.pi * η t < abs (|μ j| - threshold t))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hWalk : ∀ j, walk (stencilWalkFrame depth rowScratch columnScratch)
      (stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch) *ᵥ v j =
        Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (hWalkCovered : ∀ j, ∃ t, threshold t ≤ |μ j|)
    (hComplete : ∀ ψ, (∑ j, coord ψ j • v j) = ψ) :
    let pos : ∀ t, 0 < width t := fun t => by have := hWidth t; omega
    let mass := commonBinMass condition precision
    let C := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    let b := liftedResidual residual
    let scale := entryScale * sparseAlpha geometry.stencilSize columns
    let H := stencil_signal_hermitian geometry coefficients scale
    let P t := spectralDiagonal H.eigenvectorBasis (fun i => binSpectralMask threshold t (H.eigenvalues i))
    let right : Matrix (Address depth ⊕ Address depth) (Address depth ⊕ Address depth) ℂ :=
      diagonal (Sum.elim 0 1)
    let z t := right *ᵥ (compressedBinReciprocal (condition t) precision mass C U *ᵥ (P t *ᵥ b))
    let target := seededBinState width condition precision (cleanPhaseTape width pos)
      (C *ᵥ ((mass : ℂ)⁻¹ • (stencilSpectralInverse geometry coefficients scale *ᵥ b)))
    let output := stencilBinOutput geometry coefficients entryScale rowScratch columnScratch
      residual width pos condition threshold precision
    let success := stencilBinSuccess rowScratch columnScratch width condition precision
    let error := binPhaseErrorBudget width threshold η μ (coord (C *ᵥ b)) +
      binPhaseErrorBudget width threshold η μ (coord (C *ᵥ (∑ t, z t))) + (2 * precision) / mass
    let decode ψ := toEuclidean_fromVec (Run 1 (stencilBinHistoryUncompute width condition threshold precision C U)
      (PostMeasure ψ success))
    let E := extendClock n (binClockProjection (M := StencilWorkspace depth geometry.stencilSize columns)
      width condition precision)
    let bad := Projector (stencilBinFailure (depth := depth) rowScratch columnScratch width condition precision)
    let V := binStageOracle width condition threshold precision C U
    let initial := stencilBinInput rowScratch columnScratch residual width pos condition precision
    let a := plainAmplitude E bad V initial n
    error < ‖toEuclidean_fromVec target‖ →
      0 < MeasureProb output success ∧
      ‖decode output - NormedSpace.normalize (toEuclidean_fromVec target)‖ ≤
        2 * error / ‖toEuclidean_fromVec target‖ ∧
      ∃ (K : ℝ) (rs : ℕ → ℕ),
        let word := nestedWord E bad initial rs n
        let amplified := clockState V word initial
        0 < K ∧ legal (n + 1) word ∧ 1 / 100 ≤ MeasureProb amplified success ∧
        ‖decode amplified - NormedSpace.normalize (toEuclidean_fromVec target)‖ ≤
          2 * error / ‖toEuclidean_fromVec target‖ ∧
        (weightedCost prices word : ℝ) ≤ K / a *
          (((prices 0 + prices 1 : ℕ) : ℝ) + quasinorm23 (fun j : Fin (n - 1) =>
            plainAmplitude E bad V initial (j.val + 1) * prices (j.val + 2))) := by
  intro pos α C U b scale H P right z target output success error decode E bad V initial a hBudget
  let inverseWord := stencilBinHistoryUncompute width condition threshold precision C U
  obtain ⟨hC, hU, hSq, _⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  obtain ⟨hTotal, _⟩ := stencil_bin_unnormalized_physical_readout geometry coefficients entryScale
    rowScratch columnScratch residual hValid hResidual hScale hEntry hColumns width hWidth
    condition threshold precision hCondition hPrecision hHalf hCutoff hSignalBound hSignalCovered
    v coord phase μ η hη hEtaHalf hCos hMargin hOrthogonal hWalk hWalkCovered hComplete
  obtain ⟨hRawProb, hRawError⟩ := stencil_bin_history_postmeasure_error width condition threshold precision
    C U hC hU hSq pos output target success error hTotal hBudget
  refine ⟨hRawProb, hRawError, ?_⟩
  obtain ⟨K, hK, _, rs, _, _, _, hLegal, _, hAmpProb, hCost, hState⟩ :=
    encoded_stencil_bin_amplification geometry coefficients entryScale rowScratch columnScratch residual hValid hResidual
      width condition threshold precision prices hScale hEntry hColumns hn pos hRawProb
  refine ⟨K, rs, hK, hLegal, hAmpProb, ?_, hCost⟩
  change ‖toEuclidean_fromVec (Run 1 inverseWord
    (PostMeasure (clockState V (nestedWord E bad initial rs n) initial) success)) -
      NormedSpace.normalize (toEuclidean_fromVec target)‖ ≤ 2 * error / ‖toEuclidean_fromVec target‖
  rw [hState]
  exact hRawError

end Qatlib.Papers.QFVMChen22.TimeStep
