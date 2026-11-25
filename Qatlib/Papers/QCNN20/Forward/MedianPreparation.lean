/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Forward.MedianSampling
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
public import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

@[expose] public section

/-!
# Unitary preparation of the median convolution sampler

[KerenidisLandmanPrakash2020], Section D.1.4, amplifies the zero flag of
the convolution sampler. A supplied address-preparation unitary is
followed by the actual repeated estimation, reversible label write,
activation rotation, and estimator reversal. The product is unitary
and maps a single basis seed to the previously defined sampler state.
The factors use exact matrices and allow a separate synthesis of the
address preparation and arithmetic.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Forward

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge (applyGate_relabelGate relabelGate)
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend (relabelState_ket)
open Qatlib.Concepts.BlockEncoding.EncodingCore (relabelGate_mem_unitary)
open Qatlib.Concepts.QueryComplexity.Amplification (PiTensorState piTensorState_const_ket)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid valid_subtree)
open Qatlib.Papers.QCNN20.PatchMemory (patchTree)
open scoped Classical

variable {positions window : ℕ} {Filter : Type} [Fintype Filter]

/-- A basis vector is independent of the equality decision procedure used for its amplitudes. -/
private theorem ket_with_decidable_eq {I : Type} {d e : DecidableEq I} (j : I) : @Ket I d j = @Ket I e j := by
  have hde : d = e := Subsingleton.elim _ _
  subst e
  rfl

/-- The source order puts the label and flag after the estimation history. -/
abbrev MedianFlagBasis (C : Type) (window M r : ℕ) := ((C × ConvolutionMedianRecord window M r) × Fin M) × Bool

/-- The measurement order puts retained data before the estimation history. -/
abbrev MedianReadoutBasis (C : Type) (window M r : ℕ) := ((C × Fin M) × Bool) × ConvolutionMedianRecord window M r

/-- Each history copy begins with the zero counter, zero mark, and initial signal ket. -/
def convolutionMedianBlankRecord (window M : ℕ) (hM : 0 < M) (r : ℕ) : ConvolutionMedianRecord window M r :=
  fun _ => (⟨0, hM⟩, (false, (false, ZeroStr window)))

/-- Basis seed before switching to the readout order. -/
def convolutionMedianFlagSeed (a : Address positions × Filter) (window M : ℕ) (hM : 0 < M) (r : ℕ) :
    MedianFlagBasis (Address positions × Filter) window M r :=
  (((a, convolutionMedianBlankRecord window M hM r), ⟨0, hM⟩), false)

/-- The same basis seed in the layout used for readout and amplification. -/
def convolutionMedianSeed (a : Address positions × Filter) (window M : ℕ) (hM : 0 < M) (r : ℕ) :
    MedianReadoutBasis (Address positions × Filter) window M r :=
  medianReadoutLayout _ _ _ (convolutionMedianFlagSeed a window M hM r)

/-- Compose address preparation, addressed repeated AE, median label write and flag rotation. -/
def convolutionMedianFlagPreparation (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ) :
    Matrix (MedianFlagBasis (Address positions × Filter) window M r)
      (MedianFlagBasis (Address positions × Filter) window M r) ℂ :=
  let counter := addressedAERepeatedGate (2 * r + 1) M
    (fun a => convolutionPreparation (patchTree memory a.1) (filters a.2))
    (false, ZeroStr window) (fun _ => differenceOutcomes window)
  let recordIdentity : Matrix (ConvolutionMedianRecord window M r) (ConvolutionMedianRecord window M r) ℂ := 1
  let labelIdentity : Matrix (Fin M) (Fin M) ℂ := 1
  let write := permMatrix (writeMedianActivationLabel (convolutionMedianLabelMap memory filters cap M r) ⟨0, hM⟩)
  activationFlagGate (convolutionMedianFlagWeight memory filters cap M r) *
    LiftGate (write * TensorGate (counter * TensorGate addressPreparation recordIdentity) labelIdentity)

set_option maxHeartbeats 1200000 in
/-- The composed flag preparation acts on its basis seed exactly as the median sampler. -/
theorem convolution_median_flag_preparation_apply [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (a : Address positions × Filter) :
    ApplyGate (convolutionMedianFlagPreparation memory filters cap M hM r addressPreparation)
      (Ket (convolutionMedianFlagSeed a window M hM r)) =
      convolutionMedianFlagOutput memory filters cap M hM r (ApplyGate addressPreparation (Ket a)) := by
  let blank : Fin M := ⟨0, hM⟩
  let record := convolutionMedianBlankRecord window M hM r
  have hSeed : TensorState (TensorState (TensorState (Ket a) (Ket record)) (Ket blank)) (Ket false) =
      Ket (convolutionMedianFlagSeed a window M hM r) := by
    simp only [tensorState_ket_ket, convolutionMedianFlagSeed, record, blank]
    exact ket_with_decidable_eq (convolutionMedianFlagSeed a window M hM r)
  have hRecord : PiTensorState (fun _ : Fin (2 * r + 1) =>
      TensorState (Ket blank) (TensorState (Ket false) (Ket (false, ZeroStr window)))) = Ket record := by
    simp only [tensorState_ket_ket, piTensorState_const_ket, record, blank]
    exact ket_with_decidable_eq (convolutionMedianBlankRecord window M hM r)
  rw [← hSeed]
  simp only [convolutionMedianFlagPreparation, applyGate_mul, applyGate_liftGate, applyGate_tensorGate, applyGate_one]
  unfold convolutionMedianFlagOutput convolutionMedianCounters addressedAERepeatedOutput
  rw [hRecord]

set_option maxHeartbeats 1200000 in
/-- Each factor of the composed flag preparation is unitary for a valid memory and positive cap. -/
theorem convolution_median_flag_preparation_unitary [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (hAddress : addressPreparation ∈ Matrix.unitaryGroup (Address positions × Filter) ℂ) :
    convolutionMedianFlagPreparation memory filters cap M (by omega) r addressPreparation ∈
      Matrix.unitaryGroup (MedianFlagBasis (Address positions × Filter) window M r) ℂ := by
  let C := Address positions × Filter
  let R := ConvolutionMedianRecord window M r
  let blank : Fin M := ⟨0, by omega⟩
  let A (a : C) := convolutionPreparation (patchTree memory a.1) (filters a.2)
  have hA (a : C) : A a ∈ Matrix.unitaryGroup (Bool × Reg window) ℂ :=
    convolution_preparation_unitary _ _ (valid_subtree positions memory a.1 hMemory) (hFilters a.2)
  have hCount := addressed_ae_repeated_gate_unitary (2 * r + 1) M hM A (false, ZeroStr window)
    (fun _ => differenceOutcomes window) hA
  have hAddr := tensorGate_unitary hAddress (Matrix.unitaryGroup R ℂ).one_mem
  have hEstimate := (Matrix.unitaryGroup (C × R) ℂ).mul_mem
    (unitary_with_decidable_eq hCount) (unitary_with_decidable_eq hAddr)
  have hWithLabel := tensorGate_unitary hEstimate (Matrix.unitaryGroup (Fin M) ℂ).one_mem
  have hWrite := write_median_label_unitary (convolutionMedianLabelMap memory filters cap M r) blank
  have hFlag := activation_flag_gate_unitary (convolutionMedianFlagWeight memory filters cap M r) (fun p => by
    unfold convolutionMedianFlagWeight
    exact ⟨div_nonneg (capped_relu_nonneg _ _) hCap.le, (div_le_one hCap).mpr (max_le hCap.le (min_le_left _ _))⟩)
  have hLabelled := (Matrix.unitaryGroup ((C × R) × Fin M) ℂ).mul_mem
    (unitary_with_decidable_eq hWrite) (unitary_with_decidable_eq hWithLabel)
  exact unitary_with_decidable_eq ((Matrix.unitaryGroup (MedianFlagBasis C window M r) ℂ).mul_mem
    (unitary_with_decidable_eq hFlag) (unitary_with_decidable_eq (liftGate_unitary hLabelled)))

/-- The sampler preparation in readout order, including the address-controlled estimator adjoint. -/
def convolutionMedianPreparation (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ) :
    Matrix (MedianReadoutBasis (Address positions × Filter) window M r)
      (MedianReadoutBasis (Address positions × Filter) window M r) ℂ :=
  convolutionMedianReverse memory filters M r * relabelGate (medianReadoutLayout _ _ _)
    (convolutionMedianFlagPreparation memory filters cap M hM r addressPreparation)

/-- The preparation used for amplification reproduces the actual final sampler. -/
theorem convolution_median_preparation_apply [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (a : Address positions × Filter) :
    ApplyGate (convolutionMedianPreparation memory filters cap M hM r addressPreparation)
      (Ket (convolutionMedianSeed a window M hM r)) =
      convolutionMedianReadout memory filters cap M hM r (ApplyGate addressPreparation (Ket a)) := by
  unfold convolutionMedianPreparation convolutionMedianSeed convolutionMedianReadout
  rw [applyGate_mul, ← relabelState_ket, applyGate_relabelGate, convolution_median_flag_preparation_apply]

set_option maxHeartbeats 1200000 in
/-- The full preparation is unitary, including the reversal on the estimation workspaces. -/
theorem convolution_median_preparation_unitary [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (hAddress : addressPreparation ∈ Matrix.unitaryGroup (Address positions × Filter) ℂ) :
    convolutionMedianPreparation memory filters cap M (by omega) r addressPreparation ∈
      Matrix.unitaryGroup (MedianReadoutBasis (Address positions × Filter) window M r) ℂ := by
  have hReverse := convolution_median_reverse_unitary memory filters hMemory hFilters M hM r
  have hFlag := convolution_median_flag_preparation_unitary memory filters hMemory hFilters cap hCap M hM r
    addressPreparation hAddress
  exact (Matrix.unitaryGroup (MedianReadoutBasis (Address positions × Filter) window M r) ℂ).mul_mem
    hReverse (relabelGate_mem_unitary hFlag (medianReadoutLayout _ _ _))

end Qatlib.Papers.QCNN20.Forward
