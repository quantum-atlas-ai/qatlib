/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.UnitaryPreparation
public import Qatlib.Papers.QCNN20.Forward.HadamardReadout
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Coherent preparation of the convolution amplitudes

[KerenidisLandmanPrakash2020], Algorithm 1 and Section D.1.1, use a flag to
load the patch and filter in superposition, then apply a Hadamard to that
flag. Here both loads are the exact signed QRAM tree preparations. The
preparation is also controlled by the location and filter indices, so each
address slice has the corresponding interference amplitudes. The
amplitude-estimation bound below concerns a basis address. Coherent
estimation on all addresses and encoded rotation costs remain separate.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Forward

open Matrix
open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open Qatlib.Papers.QCNN20.PatchMemory (patchTree)
open Qatlib.Concepts.LchsSimulation.StaticLchs (preparedAAState)
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Foundations.PureStateMath
open scoped BigOperators

variable {positions window : ℕ}

/-- Interfere the signed QRAM preparations for a patch and a filter. -/
def convolutionPreparation (patch filter : Tree ℝ window) :
    Matrix (Bool × Address window) (Bool × Address window) ℂ :=
  let H := TensorGate Hadamard (1 : Matrix (Address window) (Address window) ℂ)
  H * (blockDiagFirst (fun bit => signedTreePreparation (if bit then filter else patch)) * H)

/-- Both controlled tree preparations and both Hadamards are unitary. -/
theorem convolution_preparation_unitary (patch filter : Tree ℝ window) (hp : Valid patch) (hf : Valid filter) :
    convolutionPreparation patch filter ∈ Matrix.unitaryGroup (Bool × Address window) ℂ := by
  have hH := tensorGate_unitary hadamard_unitary (Matrix.unitaryGroup (Address window) ℂ).one_mem
  refine (Matrix.unitaryGroup (Bool × Address window) ℂ).mul_mem hH
    ((Matrix.unitaryGroup (Bool × Address window) ℂ).mul_mem ?_ hH)
  apply blockDiagFirst_unitary
  intro bit
  apply signed_tree_preparation_unitary
  cases bit
  · exact hp
  · exact hf

/-- A Hadamard on the flag mixes each pair of amplitudes at the same slot. -/
private theorem apply_hadamard_flag (ψ : QState (Bool × Address window)) (bit : Bool) (slot : Address window) :
    ApplyGate (TensorGate Hadamard 1) ψ (bit, slot) = ∑ b : Bool, Hadamard bit b * ψ (b, slot) := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorGate_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The actual circuit's true flag contains the signed patch–filter differences. -/
theorem convolution_preparation_difference (patch filter : Tree ℝ window)
    (hp : Valid patch) (hf : Valid filter) (hpPos : 0 < mass patch) (hfPos : 0 < mass filter)
    (slot : Address window) :
    preparedAAState (convolutionPreparation patch filter) (false, ZeroStr window) (true, slot) =
      (differenceBranch patch filter slot : ℂ) := by
  let H := TensorGate Hadamard (1 : Matrix (Address window) (Address window) ℂ)
  let trees : Bool → Tree ℝ window := fun bit => if bit then filter else patch
  let v : QState (Bool × Address window) := ApplyGate H (Ket (false, ZeroStr window))
  let loaded := ApplyGate (blockDiagFirst (fun bit => signedTreePreparation (trees bit))) v
  let r : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hv (bit : Bool) : (fun k => v (bit, k)) = r • Ket (ZeroStr window) := by
    unfold v H
    rw [← tensorState_ket_ket, applyGate_tensorGate, applyGate_hadamard_ket_false, applyGate_one]
    funext k
    simp only [TensorState, Plus, hadamard_apply_false, Pi.smul_apply, smul_eq_mul, r]
  have hLoaded (bit : Bool) : loaded (bit, slot) = r * (pathAmplitude (trees bit) slot : ℂ) := by
    have hValid : Valid (trees bit) := by
      cases bit
      · exact hp
      · exact hf
    have hPos : 0 < mass (trees bit) := by
      cases bit
      · exact hpPos
      · exact hfPos
    unfold loaded
    rw [applyGate_blockDiagFirst_slice, hv]
    change (signedTreePreparation (trees bit) *ᵥ (r • Ket (ZeroStr window))) slot = _
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun z : ℂ => r * z) (signed_tree_preparation_apply _ hValid hPos slot)
  change ApplyGate (H * (blockDiagFirst (fun bit => signedTreePreparation (trees bit)) * H))
    (Ket (false, ZeroStr window)) (true, slot) = _
  rw [applyGate_mul, applyGate_mul]
  change ApplyGate H loaded (true, slot) = _
  have hHadTrue : Hadamard true true = -r := by simp [Hadamard, r]
  rw [apply_hadamard_flag, Fintype.sum_bool, hLoaded true, hLoaded false, hadamard_apply_false, hHadTrue]
  change (-r) * (r * (pathAmplitude filter slot : ℂ)) + r * (r * (pathAmplitude patch slot : ℂ)) = _
  calc
    _ = r * r * ((pathAmplitude patch slot : ℂ) - (pathAmplitude filter slot : ℂ)) := by ring
    _ = _ := by
      rw [show r * r = (2 : ℂ)⁻¹ from inv_sqrt2_mul_self]
      unfold differenceBranch
      push_cast
      ring

/-- Select the interference preparation coherently by position and filter address. -/
def addressedConvolutionPreparation {Filter : Type} (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) :
    Matrix ((Address positions × Filter) × (Bool × Address window))
      ((Address positions × Filter) × (Bool × Address window)) ℂ :=
  blockDiagFirst (fun a => convolutionPreparation (patchTree memory a.1) (filters a.2))

/-- A valid patch memory and valid filters give a unitary preparation on the address register. -/
theorem addressed_convolution_preparation_unitary {Filter : Type} [Fintype Filter] [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f)) :
    addressedConvolutionPreparation memory filters ∈
      Matrix.unitaryGroup ((Address positions × Filter) × (Bool × Address window)) ℂ := by
  apply blockDiagFirst_unitary
  intro a
  exact convolution_preparation_unitary _ _ (valid_subtree positions memory a.1 hMemory) (hFilters a.2)

/-- The prepared difference slice at a positive-mass address is multiplied by that address's
input amplitude. The equality applies to arbitrary superpositions of location and filter indices. -/
theorem addressed_convolution_difference {Filter : Type} [Fintype Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f)) (α : QState (Address positions × Filter))
    (location : Address positions) (filter : Filter)
    (hPatch : 0 < mass (patchTree memory location)) (hFilter : 0 < mass (filters filter))
    (slot : Address window) :
    ApplyGate (addressedConvolutionPreparation memory filters)
      (TensorState α (Ket (false, ZeroStr window))) ((location, filter), (true, slot)) =
      α (location, filter) * (differenceBranch (patchTree memory location) (filters filter) slot : ℂ) := by
  rw [addressedConvolutionPreparation, applyGate_blockDiagFirst_slice]
  change (convolutionPreparation (patchTree memory location) (filters filter) *ᵥ
    (α (location, filter) • Ket (false, ZeroStr window))) (true, slot) = _
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  exact congrArg (fun z : ℂ => α (location, filter) * z)
    (convolution_preparation_difference _ _ (valid_subtree positions memory location hMemory)
      (hFilters filter) hPatch hFilter slot)

/-- BHMT estimation of the actual QRAM interference circuit gives a capped convolution estimate.
When either input has zero mass the rescaled output is exact at every label. -/
theorem qram_convolution_estimation_success (patch filter : Tree ℝ window) (hp : Valid patch) (hf : Valid filter)
    (cap : ℝ) (M : ℕ) (hM : 2 ≤ M) :
    let a := differenceWeight patch filter
    let ε := 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |cappedRelu cap (estimateFromDifferenceWeight patch filter (aeEstimate M z)) -
          cappedRelu cap (convolutionEntry patch filter)| ≤
          (2 * (Real.sqrt (mass patch) * Real.sqrt (mass filter))) * ε),
        (aeLaw M (convolutionPreparation patch filter) (false, ZeroStr window) (differenceOutcomes window)
          (convolution_preparation_unitary patch filter hp hf) hM).prob z := by
  intro a ε
  by_cases hBoth : 0 < mass patch ∧ 0 < mass filter
  · exact capped_convolution_estimation_success patch filter hp hf hBoth.1 hBoth.2 cap M hM _ _
      (convolution_preparation_unitary patch filter hp hf)
      (convolution_preparation_difference patch filter hp hf hBoth.1 hBoth.2)
  · have hScale : Real.sqrt (mass patch) * Real.sqrt (mass filter) = 0 := by
      by_cases hPatch : 0 < mass patch
      · have hFilter : mass filter = 0 :=
          le_antisymm (le_of_not_gt fun hfPos => hBoth ⟨hPatch, hfPos⟩) (mass_nonneg filter hf)
        simp [hFilter]
      · have hz : mass patch = 0 := le_antisymm (le_of_not_gt hPatch) (mass_nonneg patch hp)
        simp [hz]
    simp only [estimateFromDifferenceWeight, convolutionEntry, hScale, mul_zero, zero_mul, sub_self,
      abs_zero, le_refl, Finset.filter_true]
    rw [(aeLaw M (convolutionPreparation patch filter) (false, ZeroStr window) (differenceOutcomes window)
      (convolution_preparation_unitary patch filter hp hf) hM).sum_one]
    apply (div_le_one (pow_pos Real.pi_pos 2)).2
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]

end Qatlib.Papers.QCNN20.Forward
