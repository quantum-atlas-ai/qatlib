/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.MagnitudeThreshold
public import Qatlib.Concepts.QRAM.AmplitudeAccess.UnitaryPreparation
public import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError

@[expose] public section

/-!
# Reversible magnitude decision for a stencil stage

[ChenXueChenEtAl2022], Appendix C.3, uses the gapped phase estimation in
[ChildsKothariSomma2017], Section 5. The phase word writes a decision to a
fresh Boolean register and is then inverted. The true slice is the
uncomputed accepted component of the phase-estimation state. The guarded
stage fixes any history containing an acceptance. Scheduling the stages
on a common clock and applying the conditioned reciprocal require
additional operations.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec norm_toEuclidean_fromVec_sq)
open Qatlib.Foundations.InstrumentCore.Measurement (Collapse collapse_apply)
open Qatlib.Concepts.LchsSimulation.StaticLchs (norm_applyGate_of_mem_unitaryGroup)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Concepts.QRAM.AmplitudeAccess (applyGate_blockDiagFirst_slice)
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter (spectralTargetState)
open Qatlib.Concepts.WalkSearch.MultiBandFilter
  (bandAccepted bandEmbed bandEvent bandQPEMatrix bandQPEMatrix_unitary
    bandMasked_norm_sq multiband_actual_eigenstate_misclassification)
open scoped BigOperators Classical

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Toggle the fresh decision bit when the phase counter belongs to the accepted clean event. -/
def toggleMagnitudeFlag {M : ℕ} (labels : Finset (Fin M)) (p : Bool × (Fin M × (Bool × I))) :
    Bool × (Fin M × (Bool × I)) :=
  (if p.2 ∈ bandEvent M labels then !p.1 else p.1, p.2)

/-- The controlled toggle is a basis involution. -/
theorem toggle_magnitude_flag_involutive {M : ℕ} (labels : Finset (Fin M)) :
    Function.Involutive (toggleMagnitudeFlag (I := I) labels) := by
  rintro ⟨flag, p⟩
  by_cases h : p ∈ bandEvent M labels <;> simp [toggleMagnitudeFlag, h]

/-- Compute the counted phase, write its magnitude decision, and uncompute the phase. -/
def countedMagnitudeFlag (U : Matrix I I ℂ) (M : ℕ) (threshold : ℝ) :
    Matrix (Bool × (Fin M × (Bool × I))) (Bool × (Fin M × (Bool × I))) ℂ :=
  let Q := bandQPEMatrix U M
  blockDiagFirst (fun _ : Bool => Qᴴ) *
    permMatrix (toggleMagnitudeFlag (magnitudeThresholdLabels M threshold)) *
    blockDiagFirst (fun _ : Bool => Q)

/-- The decision and uncomputation give a unitary stage on the full workspace. -/
theorem counted_magnitude_flag_unitary (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (M : ℕ) (hM : 0 < M) (threshold : ℝ) :
    countedMagnitudeFlag U M threshold ∈ Matrix.unitaryGroup (Bool × (Fin M × (Bool × I))) ℂ := by
  have hQ := bandQPEMatrix_unitary U M hM hU
  have hQadj : (bandQPEMatrix U M)ᴴ ∈ Matrix.unitaryGroup (Fin M × (Bool × I)) ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hQ
  unfold countedMagnitudeFlag
  apply Submonoid.mul_mem
  · apply Submonoid.mul_mem
    · exact blockDiagFirst_unitary _ (fun _ => hQadj)
    · exact permMatrix_unitary (toggle_magnitude_flag_involutive _)
  · exact blockDiagFirst_unitary _ (fun _ => hQ)

/-- A decision slice is the uncomputed part of the phase estimate selected by that decision. -/
private theorem counted_magnitude_flag_slice (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (threshold : ℝ)
    (ψ : QState I) (b : Bool) :
    let Q := bandQPEMatrix U M
    let S := bandEvent (I := I) M (magnitudeThresholdLabels M threshold)
    (fun p => ApplyGate (countedMagnitudeFlag U M threshold) (TensorState (Ket false) (bandEmbed M hM ψ))
      (b, p)) = Qᴴ *ᵥ (fun p => if (p ∈ S ↔ b = true) then (Q *ᵥ bandEmbed M hM ψ) p else 0) := by
  intro phase event
  let Q := bandQPEMatrix U M
  let labels := magnitudeThresholdLabels M threshold
  let init := TensorState (Ket false) (bandEmbed M hM ψ)
  let fwd := blockDiagFirst (fun _ : Bool => Q)
  let output := Q *ᵥ bandEmbed M hM ψ
  let toggle := toggleMagnitudeFlag (I := I) labels
  let moved := ApplyGate (permMatrix toggle) (ApplyGate fwd init)
  have hFwd (b : Bool) (p : Fin M × (Bool × I)) :
      ApplyGate fwd init (b, p) = Ket false b * output p := by
    unfold fwd
    rw [applyGate_blockDiagFirst_slice]
    change (Q *ᵥ (Ket false b • bandEmbed M hM ψ)) p = _
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, output]
  have hMarked : (fun p => moved (b, p)) =
      (fun p => if (p ∈ bandEvent M labels ↔ b = true) then output p else 0) := by
    funext p
    unfold moved
    rw [applyGate_permMatrix (toggle_magnitude_flag_involutive labels)]
    cases b <;> by_cases h : p ∈ bandEvent M labels <;> simp [toggleMagnitudeFlag, h, hFwd, ket_apply]
  funext p
  unfold countedMagnitudeFlag
  rw [applyGate_mul, applyGate_mul]
  change ApplyGate (blockDiagFirst (fun _ : Bool => Qᴴ)) moved (b, p) =
    ApplyGate Qᴴ (fun q => if (q ∈ bandEvent M labels ↔ b = true) then output q else 0) p
  rw [applyGate_blockDiagFirst_slice, hMarked]

/-- Starting the decision bit and the phase workspace clean, the true slice of the actual
unitary is exactly the uncomputed accepted component. -/
theorem counted_magnitude_flag_true (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (threshold : ℝ)
    (ψ : QState I) :
    (fun p => ApplyGate (countedMagnitudeFlag U M threshold) (TensorState (Ket false) (bandEmbed M hM ψ))
      (true, p)) = bandAccepted U M hM (magnitudeThresholdLabels M threshold) ψ := by
  rw [counted_magnitude_flag_slice]
  unfold bandAccepted
  congr 1
  funext p
  simp [collapse_apply]

/-- The false decision slice is the untouched clean input minus the uncomputed accepted slice. -/
theorem counted_magnitude_flag_false (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (M : ℕ) (hM : 0 < M) (threshold : ℝ) (ψ : QState I) :
    (fun p => ApplyGate (countedMagnitudeFlag U M threshold) (TensorState (Ket false) (bandEmbed M hM ψ))
      (false, p)) = bandEmbed M hM ψ - bandAccepted U M hM (magnitudeThresholdLabels M threshold) ψ := by
  let Q := bandQPEMatrix U M
  let W := bandEmbed M hM ψ
  let S := bandEvent (I := I) M (magnitudeThresholdLabels M threshold)
  have hMask : (fun p => if (p ∈ S ↔ false = true) then (Q *ᵥ W) p else 0) =
      Q *ᵥ W - Collapse (Q *ᵥ W) S := by
    funext p
    by_cases hp : p ∈ S <;> simp [collapse_apply, hp]
  have hQ : Qᴴ * Q = 1 := by
    have hu := Matrix.mem_unitaryGroup_iff'.mp (bandQPEMatrix_unitary U M hM hU)
    simpa only [Matrix.star_eq_conjTranspose] using hu
  rw [counted_magnitude_flag_slice]
  change Qᴴ *ᵥ (fun p => if (p ∈ S ↔ false = true) then (Q *ᵥ W) p else 0) =
    W - Qᴴ *ᵥ Collapse (Q *ᵥ W) S
  rw [hMask, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]

/-- For a separated threshold, the true decision approximates the ideal above-threshold
component. The error scales with the norm of the incoming spectral packet. -/
theorem counted_magnitude_flag_error {J : Type} [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (M : ℕ) (hM : 2 ≤ M)
    (v : J → QState I) (c : J → ℂ) (phase eigenvalue : J → ℝ)
    (threshold η : ℝ) (hη : 0 < η) (hHalf : η ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ j, 2 * Real.pi * η < abs (|eigenvalue j| - threshold))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hSpectrum : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) :
    let input := TensorState (Ket false) (bandEmbed M (by omega) (∑ j, c j • v j))
    let target := Finset.univ.filter fun j => threshold ≤ |eigenvalue j|
    ‖toEuclidean_fromVec ((fun p => ApplyGate (countedMagnitudeFlag U M threshold) input (true, p)) -
      bandEmbed M (by omega) (spectralTargetState v c target))‖ ≤
        Real.sqrt (∑ j, ‖c j‖ ^ 2) * (1 / (2 * Real.sqrt M * η)) := by
  intro input target
  let Q := bandQPEMatrix U M
  let labels := magnitudeThresholdLabels M threshold
  let ψ := bandEmbed M (by omega) (∑ j, c j • v j)
  let good := bandEmbed M (by omega) (spectralTargetState v c target)
  let masked := Collapse (Q *ᵥ ψ) (bandEvent M labels)
  have hQ := bandQPEMatrix_unitary U M (by omega) hU
  have hAdjoint : Qᴴ ∈ Matrix.unitaryGroup (Fin M × (Bool × I)) ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hQ
  have hInverse : Qᴴ * Q = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hQ
  change ‖toEuclidean_fromVec ((fun p => ApplyGate (countedMagnitudeFlag U M threshold)
    (TensorState (Ket false) ψ) (true, p)) - good)‖ ≤ _
  rw [counted_magnitude_flag_true U M (by omega) threshold (∑ j, c j • v j)]
  have hDefect : Qᴴ *ᵥ masked - good = ApplyGate Qᴴ (masked - Q *ᵥ good) := by
    unfold ApplyGate
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hInverse, Matrix.one_mulVec]
  change ‖toEuclidean_fromVec (Qᴴ *ᵥ masked - good)‖ ≤ _
  rw [hDefect, norm_applyGate_of_mem_unitaryGroup hAdjoint]
  have hCoefficients : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hNonneg : 0 ≤ Real.sqrt (∑ j, ‖c j‖ ^ 2) * (1 / (2 * Real.sqrt M * η)) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hNonneg).mp
  have hScale : (1 / (2 * Real.sqrt M * η)) ^ 2 = 1 / (4 * (M : ℝ) * η ^ 2) := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ M)]
    norm_num
  have hGap := magnitude_threshold_classification_gap M phase eigenvalue threshold η hCos hMargin
  change ‖toEuclidean_fromVec (Collapse (Q *ᵥ ψ) (bandEvent M labels) - Q *ᵥ good)‖ ^ 2 ≤ _
  rw [bandMasked_norm_sq U M (by omega) labels v c phase target hOrthogonal hSpectrum,
    mul_pow, Real.sq_sqrt hCoefficients, hScale, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (multiband_actual_eigenstate_misclassification I J U M labels phase target η hM hη hHalf hGap j)
    (sq_nonneg _)

/-- The actual stage approximates the coherent spectral decision across both decision values.
The squared error is twice the squared error of the accepted slice. -/
theorem counted_magnitude_flag_full_error {J : Type} [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (M : ℕ) (hM : 2 ≤ M)
    (v : J → QState I) (c : J → ℂ) (phase eigenvalue : J → ℝ)
    (threshold η : ℝ) (hη : 0 < η) (hHalf : η ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ j, 2 * Real.pi * η < abs (|eigenvalue j| - threshold))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hSpectrum : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) :
    let seed := bandEmbed M (by omega) (∑ j, c j • v j)
    let accept := bandEmbed M (by omega)
      (spectralTargetState v c (Finset.univ.filter fun j => threshold ≤ |eigenvalue j|))
    let output := ApplyGate (countedMagnitudeFlag U M threshold) (TensorState (Ket false) seed)
    let ideal : QState (Bool × (Fin M × (Bool × I))) :=
      fun p => if p.1 then accept p.2 else (seed - accept) p.2
    ‖toEuclidean_fromVec (output - ideal)‖ ≤
      Real.sqrt 2 * (Real.sqrt (∑ j, ‖c j‖ ^ 2) * (1 / (2 * Real.sqrt M * η))) := by
  intro seed accept output ideal
  let defect := (fun p => output (true, p)) - accept
  have hSlice : ‖toEuclidean_fromVec defect‖ ≤
      Real.sqrt (∑ j, ‖c j‖ ^ 2) * (1 / (2 * Real.sqrt M * η)) :=
    counted_magnitude_flag_error U hU M hM v c phase eigenvalue threshold η hη hHalf
      hCos hMargin hOrthogonal hSpectrum
  have hTrue := counted_magnitude_flag_true U M (by omega) threshold (∑ j, c j • v j)
  have hFalse := counted_magnitude_flag_false U hU M (by omega) threshold (∑ j, c j • v j)
  change (fun p => output (false, p)) = seed - _ at hFalse
  change (fun p => output (true, p)) = _ at hTrue
  rw [← hTrue] at hFalse
  have hReject (p : Fin M × (Bool × I)) : (output - ideal) (false, p) = -defect p := by
    have hp := congrFun hFalse p
    change output (false, p) = seed p - output (true, p) at hp
    change output (false, p) - (seed p - accept p) = -(output (true, p) - accept p)
    rw [hp]
    ring
  have hAccept (p : Fin M × (Bool × I)) : (output - ideal) (true, p) = defect p := rfl
  have hSq : ‖toEuclidean_fromVec (output - ideal)‖ ^ 2 =
      (Real.sqrt 2 * ‖toEuclidean_fromVec defect‖) ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [hReject, hAccept, norm_neg, two_mul]
  have hExact := (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))).mp hSq
  rw [hExact]
  exact mul_le_mul_of_nonneg_left hSlice (Real.sqrt_nonneg 2)

/-- Run the magnitude decision only when every previous decision is false. -/
def guardedMagnitudeStage (stages : ℕ) (U : Matrix I I ℂ) (M : ℕ) (threshold : ℝ) :
    Matrix ((Fin stages → Bool) × (Bool × (Fin M × (Bool × I))))
      ((Fin stages → Bool) × (Bool × (Fin M × (Bool × I)))) ℂ :=
  blockDiagFirst fun history =>
    if ∃ i, history i = true then 1 else countedMagnitudeFlag U M threshold

/-- The guarded operation is unitary over every history, including those that have accepted. -/
theorem guarded_magnitude_stage_unitary (stages : ℕ) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (M : ℕ) (hM : 0 < M) (threshold : ℝ) :
    guardedMagnitudeStage stages U M threshold ∈ Matrix.unitaryGroup _ ℂ := by
  apply blockDiagFirst_unitary
  intro history
  split_ifs
  · exact Submonoid.one_mem _
  · exact counted_magnitude_flag_unitary U hU M hM threshold

/-- A history with a prior acceptance is fixed pointwise, also when it is entangled with
other histories in the input. -/
theorem guarded_magnitude_stage_stopped (stages : ℕ) (U : Matrix I I ℂ) (M : ℕ) (threshold : ℝ)
    (ψ : QState ((Fin stages → Bool) × (Bool × (Fin M × (Bool × I)))))
    (history : Fin stages → Bool) (stopped : ∃ i, history i = true) (work : Bool × (Fin M × (Bool × I))) :
    ApplyGate (guardedMagnitudeStage stages U M threshold) ψ (history, work) = ψ (history, work) := by
  unfold guardedMagnitudeStage
  rw [applyGate_blockDiagFirst_slice, ite_eq_left stopped, applyGate_one]

/-- A history with all decisions false executes the current magnitude test on its slice. -/
theorem guarded_magnitude_stage_running (stages : ℕ) (U : Matrix I I ℂ) (M : ℕ) (threshold : ℝ)
    (ψ : QState ((Fin stages → Bool) × (Bool × (Fin M × (Bool × I)))))
    (history : Fin stages → Bool) (running : ∀ i, history i = false) (work : Bool × (Fin M × (Bool × I))) :
    ApplyGate (guardedMagnitudeStage stages U M threshold) ψ (history, work) =
      ApplyGate (countedMagnitudeFlag U M threshold) (fun p => ψ (history, p)) work := by
  have h : ¬∃ i, history i = true := by
    rintro ⟨i, hi⟩
    simp [running i] at hi
  unfold guardedMagnitudeStage
  rw [applyGate_blockDiagFirst_slice, ite_eq_right h]

end Qatlib.Papers.QFVMChen22.TimeStep
