/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.BinSpectralReadout

@[expose] public section

/-!
# Reversing the phase history of the staged stencil solver

The variable-time solve in [ChenXueChenEtAl2022], Appendix C.3, uses a
phase-only program to erase the decision history. Reversing the
phase tests takes the ideal first-acceptance labels of a spectral
packet back to a clean tape, up to the accumulated classification
error of those same tests.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.InstrumentCore.Measurement (Collapse PostMeasure)
open Qatlib.Foundations.MatrixAlgebra.HermitianLift (lift)
open Qatlib.Foundations.PureStateMath
  (ApplyGate Inner MeasureProb QState TensorGate applyGate_mul applyGate_one tensorGate_unitary)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Foundations.QueryWordCore.Circuit (Circuit Run Step conjTranspose_mem_unitaryGroup run_gate run_nil)
open Qatlib.Concepts.BlockEncoding.Postselection (normalize_error_of_gap)
open Qatlib.Concepts.LchsSimulation.StaticLchs (norm_applyGate_of_mem_unitaryGroup)
open Qatlib.Concepts.PolynomialCalc.QubitizedPower (signal walk walk_unitary)
open Qatlib.Concepts.SketchArith.GramAction (norm_toEuclidean_collapse_eq_sqrt_measureProb)
open Qatlib.Concepts.WalkSearch.Spectral (spectralDiagonal)
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open scoped BigOperators Classical

variable {n : ℕ} {M N J : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
  [Fintype J] [DecidableEq J]

/-- The phase tests on the full bin workspace, in chronological execution order. -/
def binPhaseGates (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (C : Matrix M N ℂ) (U : Matrix M M ℂ) :
    List (Matrix (BinStageWorkspace width condition precision M) (BinStageWorkspace width condition precision M) ℂ) :=
  let W := TensorGate (1 : Matrix (ReciprocalTape condition precision)
    (ReciprocalTape condition precision) ℂ) (walk C U)
  (List.finRange n).map fun t => routedMagnitudeStage width t W (threshold t)

/-- The actual history-erasure circuit executes the adjoints of the phase tests in reverse order. -/
def stencilBinHistoryUncompute (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (C : Matrix M N ℂ) (U : Matrix M M ℂ) : Circuit (BinStageWorkspace width condition precision M) :=
  (binPhaseGates width condition threshold precision C U).reverse.map fun V => Step.gate Vᴴ

/-- Matrix semantics of the forward phase-only preparation word. -/
def stencilBinPhasePreparation (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (C : Matrix M N ℂ) (U : Matrix M M ℂ) :
    Matrix (BinStageWorkspace width condition precision M) (BinStageWorkspace width condition precision M) ℂ :=
  (binPhaseGates width condition threshold precision C U).reverse.prod

/-- The reverse product applies the forward list of gates in execution order. -/
theorem run_gate_list_eq_apply_reverse_product {H : Type} [Fintype H] [DecidableEq H]
    (gates : List (Matrix H H ℂ)) (ψ : QState H) :
    Run 1 (gates.map Step.gate) ψ = ApplyGate gates.reverse.prod ψ := by
  induction gates generalizing ψ with
  | nil => simp [run_nil, applyGate_one]
  | cons V gates ih =>
    rw [List.map_cons, run_gate, List.reverse_cons, List.prod_append, List.prod_singleton, applyGate_mul, ih]

omit [DecidableEq N] in
/-- The forward phase word acts by its matrix product. -/
theorem stencil_bin_phase_preparation_apply (width : Fin n → ℕ) (condition threshold : Fin n → ℝ)
    (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (ψ : QState (BinStageWorkspace width condition precision M)) :
    let W := TensorGate (1 : Matrix (ReciprocalTape condition precision)
      (ReciprocalTape condition precision) ℂ) (walk C U)
    ApplyGate (stencilBinPhasePreparation width condition threshold precision C U) ψ =
      Run 1 (stencilPhaseProgram width threshold W) ψ := by
  intro W
  unfold stencilBinPhasePreparation
  rw [← run_gate_list_eq_apply_reverse_product]
  simp only [binPhaseGates, stencilPhaseProgram, List.map_map, Function.comp_def, W]

set_option maxHeartbeats 500000 in
/-- The phase-only word is unitary for the encoded walk and nonempty counter registers. -/
theorem stencil_bin_phase_preparation_unitary (width : Fin n → ℕ) (condition threshold : Fin n → ℝ)
    (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1) (hWidth : ∀ t, 0 < width t) :
    stencilBinPhasePreparation width condition threshold precision C U ∈ Matrix.unitaryGroup _ ℂ := by
  let W := TensorGate (1 : Matrix (ReciprocalTape condition precision)
    (ReciprocalTape condition precision) ℂ) (walk C U)
  have hW : W ∈ Matrix.unitaryGroup _ ℂ :=
    tensorGate_unitary (Submonoid.one_mem _) (Matrix.mem_unitaryGroup_iff'.2 (walk_unitary C U hC hU hSq))
  unfold stencilBinPhasePreparation
  apply Submonoid.list_prod_mem
  intro V hV
  obtain ⟨t, _, ht⟩ := List.mem_map.mp (List.mem_reverse.mp hV)
  rw [← ht]
  exact routed_magnitude_stage_unitary width t W hW (hWidth t) (threshold t)

/-- Conjugate-transposing a forward gate product reverses the underlying execution order. -/
private theorem reverse_product_adjoint {H : Type} [Fintype H] [DecidableEq H]
    (gates : List (Matrix H H ℂ)) :
    (gates.reverse.prod)ᴴ = (gates.map Matrix.conjTranspose).prod := by
  induction gates with
  | nil => simp
  | cons V gates ih =>
    rw [List.reverse_cons, List.prod_append, List.prod_singleton, Matrix.conjTranspose_mul,
      List.map_cons, List.prod_cons, ih]

omit [DecidableEq N] in
/-- Executing the reversed phase circuit acts by the adjoint of the forward preparation. -/
theorem stencil_bin_history_uncompute_apply (width : Fin n → ℕ) (condition threshold : Fin n → ℝ)
    (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (ψ : QState (BinStageWorkspace width condition precision M)) :
    Run 1 (stencilBinHistoryUncompute width condition threshold precision C U) ψ =
      ApplyGate (stencilBinPhasePreparation width condition threshold precision C U)ᴴ ψ := by
  let gates := binPhaseGates width condition threshold precision C U
  change Run 1 (gates.reverse.map (Step.gate ∘ Matrix.conjTranspose)) ψ = ApplyGate (gates.reverse.prod)ᴴ ψ
  rw [← List.map_map (f := Matrix.conjTranspose) (g := Step.gate), run_gate_list_eq_apply_reverse_product, List.map_reverse,
    List.reverse_reverse, reverse_product_adjoint]

set_option maxHeartbeats 1000000 in
/-- Reversing the actual phase word on the ideal labelled packet returns the clean spectral
packet up to the forward classification error. Perturbing the labeled input adds its
Euclidean error to that bound. -/
theorem stencil_bin_history_uncompute_error (width : Fin n → ℕ) (hWidth : ∀ t, 2 ≤ width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1)
    (v : J → QState M) (c : J → ℂ) (phase eigenvalue : J → ℝ)
    (η : Fin n → ℝ) (hη : ∀ t, 0 < η t) (hHalf : ∀ t, η t ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ t j, 2 * Real.pi * η t < abs (|eigenvalue j| - threshold t))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hSpectrum : ∀ j, walk C U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (observed : QState (BinStageWorkspace width condition precision M)) (δ : ℝ) :
    let pos : ∀ s, 0 < width s := fun s => by have := hWidth s; omega
    let labeled := idealPhaseBinReference width pos condition threshold precision v c eigenvalue (Fin.last n)
    let clean := seededBinState width condition precision (cleanPhaseTape width pos) (∑ j, c j • v j)
    ‖toEuclidean_fromVec (observed - labeled)‖ ≤ δ →
      ‖toEuclidean_fromVec (Run 1 (stencilBinHistoryUncompute width condition threshold precision C U)
        observed - clean)‖ ≤
        δ + ∑ t, Real.sqrt 2 * (Real.sqrt (∑ j, ‖runningBinWeight threshold eigenvalue c t.val j‖ ^ 2) *
          (1 / (2 * Real.sqrt (width t) * η t))) := by
  intro pos labeled clean hObserved
  let V := stencilBinPhasePreparation width condition threshold precision C U
  have hV := stencil_bin_phase_preparation_unitary width condition threshold precision C U hC hSelf hSq pos
  have hAdj := conjTranspose_mem_unitaryGroup hV
  have hLeft : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hV
  have hPrep := stencil_bin_phase_preparation_error width hWidth condition threshold precision C U
    hC hSelf hSq v c phase eigenvalue η hη hHalf hCos hMargin hOrthogonal hSpectrum
  have hForward : ‖toEuclidean_fromVec (ApplyGate V clean - labeled)‖ ≤
      ∑ t, Real.sqrt 2 * (Real.sqrt (∑ j, ‖runningBinWeight threshold eigenvalue c t.val j‖ ^ 2) *
        (1 / (2 * Real.sqrt (width t) * η t))) := by
    rw [show ApplyGate V clean = _ from stencil_bin_phase_preparation_apply width condition threshold precision C U clean]
    exact hPrep
  have hDiff : ApplyGate Vᴴ (observed - ApplyGate V clean) = ApplyGate Vᴴ observed - clean := by
    change Vᴴ *ᵥ (observed - V *ᵥ clean) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hLeft, Matrix.one_mulVec]; rfl
  rw [stencil_bin_history_uncompute_apply]
  change ‖toEuclidean_fromVec (ApplyGate Vᴴ observed - clean)‖ ≤ _
  rw [← hDiff, norm_applyGate_of_mem_unitaryGroup hAdj]
  change ‖toEuclidean_fromVec observed - toEuclidean_fromVec (ApplyGate V clean)‖ ≤ _
  calc
    _ ≤ ‖toEuclidean_fromVec observed - toEuclidean_fromVec labeled‖ +
        ‖toEuclidean_fromVec labeled - toEuclidean_fromVec (ApplyGate V clean)‖ := by
      rw [← sub_add_sub_cancel (toEuclidean_fromVec observed) (toEuclidean_fromVec labeled)
        (toEuclidean_fromVec (ApplyGate V clean))]
      exact norm_add_le _ _
    _ ≤ _ := by
      rw [norm_sub_rev (toEuclidean_fromVec labeled) (toEuclidean_fromVec (ApplyGate V clean))]
      exact add_le_add hObserved hForward

omit [DecidableEq J] [Fintype M] [DecidableEq M] in
/-- When the threshold schedule covers the spectrum, the phase-only terminal reference
contains precisely the labelled output packets. -/
theorem ideal_phase_bin_reference_terminal (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition threshold : Fin n → ℝ) (precision : ℝ)
    (v : J → QState M) (c : J → ℂ) (eigenvalue : J → ℝ)
    (hCovered : ∀ j, ∃ t, threshold t ≤ |eigenvalue j|) :
    idealPhaseBinReference width hWidth condition threshold precision v c eigenvalue (Fin.last n) =
      ∑ t, seededBinState width condition precision (binDecisionTape width hWidth t true)
        (∑ j, acceptingBinWeight threshold eigenvalue c t j • v j) := by
  have hReject (j : J) : ¬∀ s : Fin n, s.val < n → |eigenvalue j| < threshold s := by
    obtain ⟨s, hs⟩ := hCovered j
    exact fun h => (not_le.mpr (h s s.isLt)) hs
  have hZero : (∑ j, runningBinWeight threshold eigenvalue c n j • v j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [runningBinWeight, ite_eq_right (hReject j), zero_smul]
  have hSeed : seededBinState (M := M) width condition precision (cleanPhaseTape width hWidth) 0 = 0 := by
    funext p
    simp [seededBinState, Qatlib.Foundations.PureStateMath.TensorState]
  simp [idealPhaseBinReference, hZero, hSeed]

variable {L : Type} [Fintype L] [DecidableEq L]

omit [DecidableEq J] in
set_option maxHeartbeats 1200000 in
/-- The selected ideal solver output is the first-acceptance phase labeling of the
combined decoded solution. Each right-register reciprocal stays in its own
magnitude interval, so the phase-only word assigns it the same acceptance label. -/
theorem stencil_bin_reference_phase_labels {depth rows columns : ℕ}
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (U : Matrix (StencilWorkspace depth rows columns) (StencilWorkspace depth rows columns) ℂ)
    (hC : (stencilWalkFrame depth rowScratch columnScratch)ᴴ * stencilWalkFrame depth rowScratch columnScratch = 1)
    (hU : Uᴴ = U) (hSq : U * U = 1)
    (A : Matrix (Address depth) (Address depth) ℂ)
    (hLift : signal (stencilWalkFrame depth rowScratch columnScratch) U = lift A)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ (Address depth ⊕ Address depth))) (eigenvalue : L → ℝ)
    (hEigen : ∀ i, (lift A).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (v : J → QState (StencilWorkspace depth rows columns)) (c decoded : J → ℂ) (phase μ : J → ℝ)
    (b : QState (Address depth ⊕ Address depth))
    (hInput : (∑ j, c j • v j) = stencilWalkFrame depth rowScratch columnScratch *ᵥ b)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = μ j)
    (hWalk : ∀ j, walk (stencilWalkFrame depth rowScratch columnScratch) U *ᵥ v j =
      Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hWalkCovered : ∀ j, ∃ t, threshold t ≤ |μ j|)
    (hSignalCovered : ∀ i, ∃ t, threshold t ≤ |eigenvalue i|) :
    let C := stencilWalkFrame depth rowScratch columnScratch
    let right : Matrix (Address depth ⊕ Address depth) (Address depth ⊕ Address depth) ℂ :=
      diagonal (Sum.elim 0 1)
    let P t := spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i))
    let z t := right *ᵥ (compressedBinReciprocal (condition t) precision (commonBinMass condition precision) C U *ᵥ
      (P t *ᵥ b))
    let reference := idealBinReference width hWidth condition threshold precision C U v c μ (Fin.last n)
    (∑ j, decoded j • v j) = C *ᵥ (∑ t, z t) →
      Collapse reference (stencilBinSuccess rowScratch columnScratch width condition precision) =
        idealPhaseBinReference width hWidth condition threshold precision v decoded μ (Fin.last n) := by
  intro C right P z reference hDecoded
  have hSignal (i : L) : (signal C U).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i := by
    rw [hLift]
    exact hEigen i
  have hReadout : Collapse reference (stencilBinSuccess rowScratch columnScratch width condition precision) =
      ∑ t, seededBinState width condition precision (binDecisionTape width hWidth t true) (C *ᵥ z t) :=
    (stencil_bin_reference_readout rowScratch columnScratch U hC hU hSq basis eigenvalue hSignal
      v c phase μ b hInput hCos hWalk width hWidth condition threshold precision hWalkCovered).2
  have hProj (s t : Fin n) : P s *ᵥ z t = if s = t then z t else 0 :=
    (decoded_bin_right_projection A C U hC hSq hLift basis eigenvalue hEigen condition threshold precision
      hSignalCovered b).2 s t
  have hSelect (s : Fin n) : P s *ᵥ (∑ t, z t) = z s := by
    rw [Matrix.mulVec_sum]
    simp only [hProj]
    simp
  rw [hReadout, ideal_phase_bin_reference_terminal width hWidth condition threshold precision v decoded μ hWalkCovered]
  apply Finset.sum_congr rfl
  intro t _
  have hPacket := ideal_bin_packet_in_frame C U hC hU hSq basis eigenvalue hSignal
    v decoded phase μ (∑ s, z s) hDecoded hCos hWalk threshold t
  change (∑ j, acceptingBinWeight threshold μ decoded t j • v j) = C *ᵥ (P t *ᵥ (∑ s, z s)) at hPacket
  rw [hPacket, hSelect]

/-- Reversing the phase history preserves the norm of the selected packet.
Its distance from an ideal packet therefore bounds the error of the raw
success amplitude. -/
theorem stencil_bin_history_success_amplitude_error
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1) (hWidth : ∀ t, 0 < width t)
    (output ideal : QState (BinStageWorkspace width condition precision M))
    (success : Finset (BinStageWorkspace width condition precision M)) (ε : ℝ)
    (hClose : ‖toEuclidean_fromVec (Run 1
      (stencilBinHistoryUncompute width condition threshold precision C U) (Collapse output success) - ideal)‖ ≤ ε) :
    |Real.sqrt (MeasureProb output success) - ‖toEuclidean_fromVec ideal‖| ≤ ε := by
  rw [stencil_bin_history_uncompute_apply] at hClose
  let V := stencilBinPhasePreparation width condition threshold precision C U
  let decoded := toEuclidean_fromVec (ApplyGate Vᴴ (Collapse output success))
  have hAdj := conjTranspose_mem_unitaryGroup
    (stencil_bin_phase_preparation_unitary width condition threshold precision C U hC hU hSq hWidth)
  have hAmplitude : ‖decoded‖ = Real.sqrt (MeasureProb output success) := by
    change ‖toEuclidean_fromVec (ApplyGate Vᴴ (Collapse output success))‖ = _
    rw [norm_applyGate_of_mem_unitaryGroup hAdj, norm_toEuclidean_collapse_eq_sqrt_measureProb]
  rw [← hAmplitude]
  exact (abs_norm_sub_norm_le decoded (toEuclidean_fromVec ideal)).trans hClose

set_option maxHeartbeats 900000 in
/-- An error bound on the unnormalized selected output after uncomputation gives a
normalized readout bound, provided the error is smaller than the ideal solution norm. -/
theorem stencil_bin_history_postmeasure_error (width : Fin n → ℕ) (condition threshold : Fin n → ℝ)
    (precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1) (hWidth : ∀ t, 0 < width t)
    (output ideal : QState (BinStageWorkspace width condition precision M))
    (success : Finset (BinStageWorkspace width condition precision M)) (ε : ℝ)
    (hClose : ‖toEuclidean_fromVec (Run 1
      (stencilBinHistoryUncompute width condition threshold precision C U) (Collapse output success) - ideal)‖ ≤ ε)
    (hGap : ε < ‖toEuclidean_fromVec ideal‖) :
    0 < MeasureProb output success ∧
      ‖toEuclidean_fromVec (Run 1 (stencilBinHistoryUncompute width condition threshold precision C U)
        (PostMeasure output success)) - NormedSpace.normalize (toEuclidean_fromVec ideal)‖ ≤
        2 * ε / ‖toEuclidean_fromVec ideal‖ := by
  let V := stencilBinPhasePreparation width condition threshold precision C U
  let unnormalized := toEuclidean_fromVec (ApplyGate Vᴴ (Collapse output success))
  have hV := stencil_bin_phase_preparation_unitary width condition threshold precision C U hC hU hSq hWidth
  have hAdj := conjTranspose_mem_unitaryGroup hV
  have hUnnorm : ‖unnormalized‖ = Real.sqrt (MeasureProb output success) := by
    change ‖toEuclidean_fromVec (ApplyGate Vᴴ (Collapse output success))‖ = _
    rw [norm_applyGate_of_mem_unitaryGroup hAdj, norm_toEuclidean_collapse_eq_sqrt_measureProb]
  have hClose' : ‖unnormalized - toEuclidean_fromVec ideal‖ ≤ ε := by
    rw [stencil_bin_history_uncompute_apply] at hClose
    exact hClose
  obtain ⟨hNonzero, hNorm⟩ := normalize_error_of_gap hClose' hGap
  have hPositive : 0 < ‖unnormalized‖ := norm_pos_iff.mpr hNonzero
  rw [hUnnorm] at hPositive
  refine ⟨Real.sqrt_pos.mp hPositive, ?_⟩
  have hPost : toEuclidean_fromVec (Run 1 (stencilBinHistoryUncompute width condition threshold precision C U)
      (PostMeasure output success)) = NormedSpace.normalize unnormalized := by
    rw [stencil_bin_history_uncompute_apply]
    change toEuclidean_fromVec (Vᴴ *ᵥ (((Real.sqrt (MeasureProb output success) : ℂ)⁻¹) •
      Collapse output success)) = _
    rw [Matrix.mulVec_smul, NormedSpace.normalize, hUnnorm]
    change (Real.sqrt (MeasureProb output success) : ℂ)⁻¹ • unnormalized =
      (Real.sqrt (MeasureProb output success))⁻¹ • unnormalized
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact congrArg (fun a : ℂ => a • unnormalized) (Complex.ofReal_inv _).symm
  rw [hPost]
  exact hNorm

end Qatlib.Papers.QFVMChen22.TimeStep
