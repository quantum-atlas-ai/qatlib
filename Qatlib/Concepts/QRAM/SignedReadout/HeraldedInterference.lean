/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.UnitaryPreparation
public import Qatlib.Concepts.QRAM.SignedReadout.Sampling
public import Qatlib.Foundations.InstrumentCore.Measurement.Basic
public import Qatlib.Concepts.QueryComplexity.PrepQueries.NativeOracle

@[expose] public section

/-!
# Interference with a heralded preparation

The signed readout of [KerenidisLandmanPrakash2020], Appendix G.4, interferes
an unknown state with a known reference. A coherent implementation can use a
preparation whose desired output is marked by success. Copy the success test to
a fresh flag before decoding the workspace, then give the reference the same
success amplitude. Measuring the common flag after the controlled preparations
and the Hadamard recovers the exact interference amplitudes of the normalized
branches. The reference calibration uses the exact success probability.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Matrix
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open Qatlib.Concepts.QRAM.AmplitudeAccess (applyGate_blockDiagFirst_slice pathAmplitude)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Concepts.QueryComplexity.PrepQueries (rotation rotation_unitary)
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Classical

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Put the target and reference on the two branches of a Hadamard control. -/
def interferencePreparation (target reference : Matrix I I ℂ) : Matrix (Bool × I) (Bool × I) ℂ :=
  TensorGate Hadamard 1 * blockDiagFirst (fun b : Bool => if b then reference else target) * TensorGate Hadamard 1

/-- The controlled target and reference yield a unitary interference circuit. -/
theorem interference_preparation_unitary (target reference : Matrix I I ℂ)
    (hTarget : target ∈ Matrix.unitaryGroup I ℂ) (hReference : reference ∈ Matrix.unitaryGroup I ℂ) :
    interferencePreparation target reference ∈ Matrix.unitaryGroup (Bool × I) ℂ := by
  have hH := tensorGate_unitary hadamard_unitary (Matrix.unitaryGroup I ℂ).one_mem
  unfold interferencePreparation
  refine Submonoid.mul_mem _ (Submonoid.mul_mem _ hH (blockDiagFirst_unitary _ ?_)) hH
  intro b
  cases b <;> simp [hTarget, hReference]

/-- A Hadamard on the flag combines the two workspace slices without changing any address. -/
private theorem applyGate_hadamard_slice (ψ : QState (Bool × I)) (b : Bool) (i : I) :
    ApplyGate (TensorGate Hadamard 1) ψ (b, i) = ∑ k : Bool, Hadamard b k * ψ (k, i) := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, TensorGate,
    Matrix.kronecker_apply, mul_assoc, ← Finset.mul_sum]
  simp [Matrix.one_apply]

/-- The signed or unsigned sum of raw amplitudes, divided by two, is the actual output. -/
theorem interference_preparation_entry (target reference : Matrix I I ℂ) (seed : I) (b : Bool) (i : I) :
    ApplyGate (interferencePreparation target reference) (Ket (false, seed)) (b, i) =
      (if b then ApplyGate target (Ket seed) i - ApplyGate reference (Ket seed) i
      else ApplyGate target (Ket seed) i + ApplyGate reference (Ket seed) i) / 2 := by
  rw [interferencePreparation, applyGate_mul, applyGate_mul, ← tensorState_ket_ket,
    applyGate_tensorGate, applyGate_hadamard_ket_false, applyGate_one, applyGate_hadamard_slice]
  have hBranch (k : Bool) :
      ApplyGate (blockDiagFirst (fun a : Bool => if a then reference else target)) (TensorState Plus (Ket seed)) (k, i) =
        Plus k * ApplyGate (if k then reference else target) (Ket seed) i := by
    rw [applyGate_blockDiagFirst_slice]
    change ApplyGate (if k then reference else target) (Plus k • Ket seed) i = _
    simp only [ApplyGate, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hRoot : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by rw [inv_pow, sqrt2_sq]
  simp only [hBranch, Fintype.sum_bool]
  cases b
  · simp [Hadamard, Plus]
    linear_combination (ApplyGate target (Ket seed) i + ApplyGate reference (Ket seed) i) * hRoot
  · simp [Hadamard, Plus]
    linear_combination (ApplyGate target (Ket seed) i - ApplyGate reference (Ket seed) i) * hRoot

/-- Measuring both interference branches preserves the average marked mass of the two
preparations. -/
theorem interference_preparation_success (target reference : Matrix I I ℂ) (seed : I) (S : Finset I) :
    MeasureProb (ApplyGate (interferencePreparation target reference) (Ket (false, seed))) (Finset.univ ×ˢ S) =
      (MeasureProb (ApplyGate target (Ket seed)) S + MeasureProb (ApplyGate reference (Ket seed)) S) / 2 := by
  let u := ApplyGate target (Ket seed)
  let v := ApplyGate reference (Ket seed)
  have hPair (i : I) : ‖(u i - v i) / (2 : ℂ)‖ ^ 2 + ‖(u i + v i) / (2 : ℂ)‖ ^ 2 =
      (‖u i‖ ^ 2 + ‖v i‖ ^ 2) / 2 := by
    calc
      _ = (‖u i + v i‖ ^ 2 + ‖u i - v i‖ ^ 2) / 4 := by norm_num [norm_div]; ring
      _ = _ := by rw [parallelogram_law_with_norm ℂ]; ring
  simp only [MeasureProb, Finset.sum_product, BornProb]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Fintype.sum_bool, interference_preparation_entry, u, v, Bool.false_eq_true, ite_false, ite_true] using hPair i

/-- When both input branches have the same positive marked mass, selection after the
Hadamard gives their normalized signed or unsigned sum without a relative phase. -/
theorem interference_preparation_postMeasure_entry (target reference : Matrix I I ℂ) (seed : I)
    (S : Finset I) (hMatch : MeasureProb (ApplyGate reference (Ket seed)) S = MeasureProb (ApplyGate target (Ket seed)) S)
    (b : Bool) (i : I) :
    PostMeasure (ApplyGate (interferencePreparation target reference) (Ket (false, seed))) (Finset.univ ×ˢ S) (b, i) =
      (if b then PostMeasure (ApplyGate target (Ket seed)) S i - PostMeasure (ApplyGate reference (Ket seed)) S i
      else PostMeasure (ApplyGate target (Ket seed)) S i + PostMeasure (ApplyGate reference (Ket seed)) S i) / 2 := by
  have hMass := interference_preparation_success target reference seed S
  rw [hMatch, add_self_div_two] at hMass
  by_cases hi : i ∈ S
  · have hb : (b, i) ∈ Finset.univ ×ˢ S := Finset.mem_product.mpr ⟨Finset.mem_univ _, hi⟩
    simp only [PostMeasure, collapse_apply, hb, hi, ite_true, hMass, hMatch, interference_preparation_entry]
    cases b <;> simp <;> ring
  · have hb : (b, i) ∉ Finset.univ ×ˢ S := fun h => hi (Finset.mem_product.mp h).2
    rw [postMeasure_apply_of_not_mem _ _ hb, postMeasure_apply_of_not_mem _ _ hi,
      postMeasure_apply_of_not_mem _ _ hi]
    cases b <;> simp

/-- Mark membership in the success set by toggling a separate bit. -/
def stampSuccess (S : Finset I) (input : Bool × I) : Bool × I :=
  (if input.2 ∈ S then !input.1 else input.1, input.2)

omit [Fintype I] in
/-- The membership toggle is a reversible basis permutation. -/
theorem stamp_success_involutive (S : Finset I) : Function.Involutive (stampSuccess S) := by
  rintro ⟨b, i⟩
  by_cases hi : i ∈ S <;> simp [stampSuccess, hi]

/-- Compute the membership bit before applying the workspace decoder. -/
def markedPreparation (target decoder : Matrix I I ℂ) (S : Finset I) :
    Matrix (Bool × I) (Bool × I) ℂ :=
  TensorGate 1 decoder * (permMatrix (stampSuccess S) * TensorGate 1 target)

/-- The preparation, membership toggle and workspace decoder are jointly unitary. -/
theorem marked_preparation_unitary (target decoder : Matrix I I ℂ) (S : Finset I)
    (hTarget : target ∈ Matrix.unitaryGroup I ℂ) (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ) :
    markedPreparation target decoder S ∈ Matrix.unitaryGroup (Bool × I) ℂ :=
  Submonoid.mul_mem _ (tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem hDecoder)
    (Submonoid.mul_mem _ (permMatrix_unitary (stamp_success_involutive S))
      (tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem hTarget))

/-- The marked slice is the decoded, unnormalized success projection of the original target. -/
theorem marked_preparation_success_slice (target decoder : Matrix I I ℂ) (S : Finset I) (seed i : I) :
    ApplyGate (markedPreparation target decoder S) (Ket (false, seed)) (true, i) =
      ApplyGate decoder (Collapse (ApplyGate target (Ket seed)) S) i := by
  have hTensor : TensorGate (1 : Matrix Bool Bool ℂ) decoder = blockDiagFirst (fun _ : Bool => decoder) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases h : a = b <;> simp [tensorGate_apply, blockDiagFirst, h]
  rw [markedPreparation, applyGate_mul, applyGate_mul, ← tensorState_ket_ket, applyGate_tensorGate,
    applyGate_one, hTensor, applyGate_blockDiagFirst_slice]
  apply congrArg (fun ψ : QState I => ApplyGate decoder ψ i)
  funext j
  rw [applyGate_permMatrix (stamp_success_involutive S), collapse_apply]
  by_cases h : j ∈ S <;> simp [stampSuccess, h, TensorState, Qatlib.Foundations.PureStateMath.Ket]

/-- The marked probability is unchanged by unitary decoding after the flag was written. -/
theorem marked_preparation_success (target decoder : Matrix I I ℂ) (S : Finset I) (seed : I)
    (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ) :
    MeasureProb (ApplyGate (markedPreparation target decoder S) (Ket (false, seed)))
      ({true} ×ˢ (Finset.univ : Finset I)) = MeasureProb (ApplyGate target (Ket seed)) S := by
  rw [← sum_normSq_collapse (ApplyGate target (Ket seed)) S]
  simp only [MeasureProb, Finset.sum_product, Finset.sum_singleton, BornProb, marked_preparation_success_slice]
  change ∑ i, ‖(decoder *ᵥ Collapse (ApplyGate target (Ket seed)) S) i‖ ^ 2 = _
  simp_rw [← Complex.normSq_eq_norm_sq]
  exact sum_normSq_mulVec_of_mem_unitaryGroup hDecoder _

/-- Load the reference and give it the same marked amplitude as the target. -/
def markedReference (reference : Matrix I I ℂ) (p : ℝ) : Matrix (Bool × I) (Bool × I) ℂ :=
  TensorGate (rotation (Real.sqrt (1 - p)) (Real.sqrt p)) reference

/-- The reference rotation is unitary for a valid probability. -/
theorem marked_reference_unitary (reference : Matrix I I ℂ) (hReference : reference ∈ Matrix.unitaryGroup I ℂ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : markedReference reference p ∈ Matrix.unitaryGroup (Bool × I) ℂ := by
  refine tensorGate_unitary (rotation_unitary _ _ ?_) hReference
  rw [Real.sq_sqrt (sub_nonneg.mpr hp1), Real.sq_sqrt hp0, sub_add_cancel]

/-- The positive square root of the calibrated probability multiplies the reference slice. -/
theorem marked_reference_slice (reference : Matrix I I ℂ) (p : ℝ) (seed i : I) :
    ApplyGate (markedReference reference p) (Ket (false, seed)) (true, i) =
      (Real.sqrt p : ℂ) * ApplyGate reference (Ket seed) i := by
  rw [markedReference, ← tensorState_ket_ket, applyGate_tensorGate]
  have hRotation : ApplyGate (rotation (Real.sqrt (1 - p)) (Real.sqrt p)) (Ket false) true = (Real.sqrt p : ℂ) := by
    simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, rotation]
  rw [TensorState, hRotation]

/-- The calibrated reference has exactly the prescribed probability of the common flag. -/
theorem marked_reference_success (reference : Matrix I I ℂ) (hReference : reference ∈ Matrix.unitaryGroup I ℂ)
    (p : ℝ) (hp : 0 ≤ p) (seed : I) :
    MeasureProb (ApplyGate (markedReference reference p) (Ket (false, seed)))
      ({true} ×ˢ (Finset.univ : Finset I)) = p := by
  have hNorm := normalized_applyGate hReference (normalized_ket seed)
  unfold Normalized at hNorm
  simp only [MeasureProb, Finset.sum_product, Finset.sum_singleton, BornProb, marked_reference_slice,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, ← Finset.mul_sum, hNorm, mul_one, sq_abs, Real.sq_sqrt hp]

/-- Interfere the flagged target with a reference using the supplied calibration probability. -/
def heraldedInterferencePreparation (target decoder reference : Matrix I I ℂ) (S : Finset I) (p : ℝ) :
    Matrix (Bool × (Bool × I)) (Bool × (Bool × I)) ℂ :=
  interferencePreparation (markedPreparation target decoder S) (markedReference reference p)

/-- The conditional output of the experiment after both branches use the common success flag. -/
def heraldedInterferenceReadout (target decoder reference : Matrix I I ℂ) (S : Finset I) (p : ℝ) (seed : I) :
    QState (Bool × (Bool × I)) :=
  PostMeasure (ApplyGate (heraldedInterferencePreparation target decoder reference S p) (Ket (false, false, seed)))
    (Finset.univ ×ˢ ({true} ×ˢ (Finset.univ : Finset I)))

/-- A valid calibration keeps the entire flagged interference circuit unitary. -/
theorem heralded_interference_preparation_unitary (target decoder reference : Matrix I I ℂ) (S : Finset I) (p : ℝ)
    (hTarget : target ∈ Matrix.unitaryGroup I ℂ) (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ)
    (hReference : reference ∈ Matrix.unitaryGroup I ℂ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    heraldedInterferencePreparation target decoder reference S p ∈ Matrix.unitaryGroup (Bool × (Bool × I)) ℂ :=
  interference_preparation_unitary _ _ (marked_preparation_unitary _ _ _ hTarget hDecoder)
    (marked_reference_unitary _ hReference p hp0 hp1)

/-- The probability of retaining an interference shot averages the target and calibration masses. -/
theorem heralded_interference_success (target decoder reference : Matrix I I ℂ) (S : Finset I) (p : ℝ) (seed : I)
    (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ) (hReference : reference ∈ Matrix.unitaryGroup I ℂ) (hp : 0 ≤ p) :
    MeasureProb (ApplyGate (heraldedInterferencePreparation target decoder reference S p) (Ket (false, false, seed)))
      (Finset.univ ×ˢ ({true} ×ˢ (Finset.univ : Finset I))) = (MeasureProb (ApplyGate target (Ket seed)) S + p) / 2 := by
  rw [heraldedInterferencePreparation, interference_preparation_success,
    marked_preparation_success _ _ _ _ hDecoder, marked_reference_success _ hReference p hp]

/-- After matching the physical success probabilities, the accepted interference slice is
the Hadamard interference of the decoded target and the loaded reference. -/
theorem heralded_interference_entry (target decoder reference : Matrix I I ℂ) (S : Finset I) (seed : I)
    (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ) (hReference : reference ∈ Matrix.unitaryGroup I ℂ)
    (hPos : 0 < MeasureProb (ApplyGate target (Ket seed)) S) (b : Bool) (i : I) :
    let p := MeasureProb (ApplyGate target (Ket seed)) S
    let U := heraldedInterferencePreparation target decoder reference S p
    let G := Finset.univ ×ˢ ({true} ×ˢ (Finset.univ : Finset I))
    let ψ := ApplyGate decoder (PostMeasure (ApplyGate target (Ket seed)) S)
    let φ := ApplyGate reference (Ket seed)
    PostMeasure (ApplyGate U (Ket (false, false, seed))) G (b, true, i) =
      (if b then ψ i - φ i else ψ i + φ i) / 2 := by
  intro p U G ψ φ
  let marked := ({true} : Finset Bool) ×ˢ (Finset.univ : Finset I)
  have hMem : (true, i) ∈ marked := by simp [marked]
  have hT := marked_preparation_success target decoder S seed hDecoder
  have hR := marked_reference_success reference hReference p hPos.le seed
  have hOutT : PostMeasure (ApplyGate (markedPreparation target decoder S) (Ket (false, seed))) marked (true, i) = ψ i := by
    rw [PostMeasure, collapse_apply, ite_eq_left hMem, hT, marked_preparation_success_slice]
    change _ = ApplyGate decoder (((Real.sqrt p : ℂ)⁻¹) • Collapse (ApplyGate target (Ket seed)) S) i
    simp only [p, ApplyGate, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hOutR : PostMeasure (ApplyGate (markedReference reference p) (Ket (false, seed))) marked (true, i) = φ i := by
    rw [PostMeasure, collapse_apply, ite_eq_left hMem, hR, marked_reference_slice, ← mul_assoc,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hPos).ne'), one_mul]
  change PostMeasure (ApplyGate (interferencePreparation (markedPreparation target decoder S)
    (markedReference reference p)) (Ket (false, (false, seed)))) (Finset.univ ×ˢ marked) (b, (true, i)) = _
  rw [interference_preparation_postMeasure_entry _ _ _ _ (hR.trans hT.symm), hOutT, hOutR]

/-- A heralded real target and its empirical reference give the interference-shot law at
the designated physical address labels, with calibration at the actual marked probability. -/
theorem interference_sample_born_of_heralded_preparation {depth : ℕ}
    (target decoder reference : Matrix I I ℂ) (S : Finset I) (seed : I) (label : Address depth → I)
    (state : Address depth → ℝ) (hState : ∑ a, state a ^ 2 = 1)
    (samples : List (Address depth)) (hSamples : samples ≠ [])
    (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ) (hReference : reference ∈ Matrix.unitaryGroup I ℂ)
    (hPos : 0 < MeasureProb (ApplyGate target (Ket seed)) S)
    (hTargetEntry : ∀ a, ApplyGate decoder (PostMeasure (ApplyGate target (Ket seed)) S) (label a) = (state a : ℂ))
    (hReferenceEntry : ∀ a, ApplyGate reference (Ket seed) (label a) = (pathAmplitude (empiricalTree samples) a : ℂ))
    (b : Bool) (a : Address depth) :
    let p := MeasureProb (ApplyGate target (Ket seed)) S
    let U := heraldedInterferencePreparation target decoder reference S p
    (interferenceSampleLaw state hState samples hSamples).prob (b, a) =
      BornProb (PostMeasure (ApplyGate U (Ket (false, false, seed)))
        (Finset.univ ×ˢ ({true} ×ˢ (Finset.univ : Finset I)))) (b, true, label a) := by
  intro p U
  rw [interference_sample_born]
  unfold BornProb
  rw [heralded_interference_entry target decoder reference S seed hDecoder hReference hPos b (label a),
    hTargetEntry a, hReferenceEntry a]
  cases b <;> simp [interferenceAmplitude, positiveAmplitude, Complex.ofReal_div]

end Qatlib.Concepts.QRAM.SignedReadout
