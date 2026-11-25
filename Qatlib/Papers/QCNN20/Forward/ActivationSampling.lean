/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Forward.AddressedAmplitudeEstimation
public import Qatlib.Foundations.InstrumentCore.Measurement.MeasurementLaws

@[expose] public section

/-!
# Activation sampling from the actual addressed counter

[KerenidisLandmanPrakash2020], Section D.1.4, Eq. (12), gives a zero-flag
probability proportional to the capped activation. The rotation uses the
square root of the activation divided by its cap to realize this probability.
Section D.1.3 prints the unsquared ratio as the amplitude. Here the rotation is
controlled by the actual address and counter. Counter labels are retained
until measurement, so the exact sampled law includes the local counter
probabilities. The real activation calculation specifies the rotation
parameters. Finite-word arithmetic, median amplification, and rotation
synthesis require separate circuits.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Forward

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.QueryComplexity.PrepQueries (rotation rotation_unitary)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Concepts.AmplitudeCore.PreparedReadout (aeLaw)
open Qatlib.Concepts.QRAM.AmplitudeAccess (applyGate_blockDiagFirst_slice)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid valid_subtree)
open Qatlib.Papers.QCNN20.PatchMemory (patchTree)
open scoped BigOperators Classical

/-- Attach a flag whose zero component has squared amplitude equal to the supplied weight. -/
def activationFlagGate {J : Type} (weight : J → ℝ) : Matrix (J × Bool) (J × Bool) ℂ :=
  blockDiagFirst fun j => rotation (Real.sqrt (weight j)) (Real.sqrt (1 - weight j))

/-- The controlled activation rotation is unitary for weights in the unit interval. -/
theorem activation_flag_gate_unitary {J : Type} [Fintype J] [DecidableEq J] (weight : J → ℝ)
    (h : ∀ j, 0 ≤ weight j ∧ weight j ≤ 1) :
    activationFlagGate weight ∈ Matrix.unitaryGroup (J × Bool) ℂ := by
  apply blockDiagFirst_unitary
  intro j
  apply rotation_unitary
  rw [Real.sq_sqrt (h j).1, Real.sq_sqrt (sub_nonneg.mpr (h j).2)]
  ring

/-- The good flag multiplies each source amplitude by the square root of its weight. -/
theorem activation_flag_amplitude {J : Type} [Fintype J] (weight : J → ℝ) (ψ : QState J) (j : J) :
    ApplyGate (activationFlagGate weight) (TensorState ψ (Ket false)) (j, false) =
      ψ j * (Real.sqrt (weight j) : ℂ) := by
  rw [activationFlagGate, applyGate_blockDiagFirst_slice]
  change (rotation (Real.sqrt (weight j)) (Real.sqrt (1 - weight j)) *ᵥ (ψ j • Ket false)) false = _
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  simp [rotation, Matrix.mulVec, dotProduct, Ket]

/-- Measuring a source event together with the good flag multiplies its original Born
weights by the activation probabilities. -/
theorem activation_flag_event {J : Type} [Fintype J] (weight : J → ℝ) (hw : ∀ j, 0 ≤ weight j)
    (ψ : QState J) (event : J → Prop) :
    MeasureProb (ApplyGate (activationFlagGate weight) (TensorState ψ (Ket false)))
      (Finset.univ.filter fun p => p.2 = false ∧ event p.1) =
      ∑ j ∈ Finset.univ.filter event, weight j * BornProb ψ j := by
  rw [MeasureProb, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_bool]
  simp only [Bool.true_eq_false, eq_self, false_and, ite_false, zero_add, true_and]
  by_cases hj : event j
  · simp only [hj, ite_true, BornProb, activation_flag_amplitude, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hw j), mul_comm]
  · simp [hj]

variable {positions window : ℕ} {Filter : Type} [Fintype Filter]

/-- The counter probability at a particular patch–filter address. -/
def convolutionCounterProbability (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f)) (M : ℕ) (hM : 2 ≤ M)
    (a : Address positions × Filter) (z : Fin M) : ℝ :=
  (aeLaw M (convolutionPreparation (patchTree memory a.1) (filters a.2)) (false, ZeroStr window)
    (differenceOutcomes window)
    (convolution_preparation_unitary _ _ (valid_subtree positions memory a.1 hMemory) (hFilters a.2)) hM).prob z

/-- Activation-weighted mass of an address and counter event under the actual counter law. -/
def convolutionActivationMass (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f)) (cap : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (α : QState (Address positions × Filter)) (event : (Address positions × Filter) → Fin M → Prop) : ℝ :=
  ∑ a, ‖α a‖ ^ 2 * ∑ z, (if event a z then convolutionCounterActivation
    (patchTree memory a.1) (filters a.2) cap M z else 0) *
      convolutionCounterProbability memory filters hMemory hFilters M hM a z

/-- Execute the addressed AE circuit and append the activation-weighted sampling flag. -/
def convolutionActivationOutput (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (α : QState (Address positions × Filter)) :
    QState (((Address positions × Filter) × (Fin M × (Bool × (Bool × Address window)))) × Bool) :=
  ApplyGate (activationFlagGate fun p =>
    convolutionCounterActivation (patchTree memory p.1.1) (filters p.1.2) cap M p.2.1 / cap)
    (TensorState (convolutionAEOutput memory filters M hM α) (Ket false))

/-- The full flagged activation output is normalized for a positive cap and
normalized address input. -/
theorem convolution_activation_output_normalized (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (α : QState (Address positions × Filter))
    (hα : Normalized α) : Normalized (convolutionActivationOutput memory filters cap M (by omega) α) := by
  unfold convolutionActivationOutput
  let J := (Address positions × Filter) × (Fin M × (Bool × (Bool × Address window)))
  let decJ : DecidableEq J := inferInstance
  let weight (p : J) :=
    convolutionCounterActivation (patchTree memory p.1.1) (filters p.1.2) cap M p.2.1 / cap
  have hw (p : J) : 0 ≤ weight p ∧ weight p ≤ 1 := by
    refine ⟨div_nonneg (capped_relu_nonneg _ _) hCap.le, (div_le_one hCap).mpr ?_⟩
    exact max_le hCap.le (min_le_left _ _)
  have hGate := @activation_flag_gate_unitary J inferInstance decJ weight hw
  let A (a : Address positions × Filter) := convolutionPreparation (patchTree memory a.1) (filters a.2)
  have hA (a : Address positions × Filter) : A a ∈ Matrix.unitaryGroup (Bool × Address window) ℂ :=
    convolution_preparation_unitary (patchTree memory a.1) (filters a.2)
      (valid_subtree positions memory a.1 hMemory) (hFilters a.2)
  have hOut : Normalized (convolutionAEOutput memory filters M (by omega) α) := by
    change Normalized (addressedAEOutput M (by omega) A (false, ZeroStr window) (fun _ => differenceOutcomes window) α)
    exact addressed_ae_output_normalized M hM A (false, ZeroStr window) (fun _ => differenceOutcomes window) hA α hα
  exact @normalized_applyGate (J × Bool) inferInstance (@instDecidableEqProd J Bool decJ inferInstance)
    (activationFlagGate weight) hGate _ (normalized_tensorState hOut (normalized_ket false))

/-- The good-flag probability for an arbitrary output event is its activation-weighted mass
divided by the cap. -/
theorem convolution_activation_flag_probability (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (α : QState (Address positions × Filter))
    (event : (Address positions × Filter) → Fin M → Prop) :
    MeasureProb (convolutionActivationOutput memory filters cap M (by omega) α)
      (Finset.univ.filter fun p => p.2 = false ∧ event p.1.1 p.1.2.1) =
      convolutionActivationMass memory filters hMemory hFilters cap M hM α event / cap := by
  let A (a : Address positions × Filter) := convolutionPreparation (patchTree memory a.1) (filters a.2)
  let S : Address positions × Filter → Finset (Bool × Address window) := fun _ => differenceOutcomes window
  let f (a : Address positions × Filter) := convolutionCounterActivation (patchTree memory a.1) (filters a.2) cap M
  have hA (a : Address positions × Filter) : A a ∈ Matrix.unitaryGroup (Bool × Address window) ℂ :=
    convolution_preparation_unitary _ _ (valid_subtree positions memory a.1 hMemory) (hFilters a.2)
  let weight (p : (Address positions × Filter) × (Fin M × (Bool × (Bool × Address window)))) :=
    f p.1 p.2.1 / cap
  have hFlag := activation_flag_event weight
    (fun p => div_nonneg (capped_relu_nonneg cap _) hCap.le)
    (convolutionAEOutput memory filters M (by omega) α) (fun p => event p.1 p.2.1)
  unfold convolutionActivationOutput
  rw [hFlag, Finset.sum_filter]
  have hLaw := addressed_ae_weighted_probability M hM A (false, ZeroStr window) S hA α
    (fun a z => if event a z then f a z / cap else 0)
  simp only [ite_mul, zero_mul] at hLaw
  change (∑ p, if event p.1 p.2.1 then (f p.1 p.2.1 / cap) *
    BornProb (convolutionAEOutput memory filters M (by omega) α) p else 0) = _
  rw [show (∑ p, if event p.1 p.2.1 then (f p.1 p.2.1 / cap) *
      BornProb (convolutionAEOutput memory filters M (by omega) α) p else 0) = _ from hLaw]
  unfold convolutionActivationMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_div_assoc, Finset.sum_div]
  apply congrArg (fun s : ℝ => ‖α a‖ ^ 2 * s)
  apply Finset.sum_congr rfl
  intro z _
  let p := convolutionCounterProbability memory filters hMemory hFilters M hM a z
  change (if event a z then f a z / cap * p else 0) = (if event a z then f a z else 0) * p / cap
  by_cases h : event a z <;> simp [h, div_mul_eq_mul_div₀]

/-- Condition on the final zero flag to obtain the normalized activation-weighted law.
This statement keeps the actual counter uncertainty and allows any event determined by
the address and the reconstructed activation. -/
theorem convolution_activation_postselect (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (α : QState (Address positions × Filter))
    (event : (Address positions × Filter) → Fin M → Prop)
    (hMass : 0 < convolutionActivationMass memory filters hMemory hFilters cap M hM α (fun _ _ => True)) :
    let out := convolutionActivationOutput memory filters cap M (by omega) α
    let success := Finset.univ.filter fun p => p.2 = false
    0 < MeasureProb out success ∧
      MeasureProb (PostMeasure out success) (Finset.univ.filter fun p => event p.1.1 p.1.2.1) =
        convolutionActivationMass memory filters hMemory hFilters cap M hM α event /
          convolutionActivationMass memory filters hMemory hFilters cap M hM α (fun _ _ => True) := by
  intro out success
  have hTotal : MeasureProb out success =
      convolutionActivationMass memory filters hMemory hFilters cap M hM α (fun _ _ => True) / cap := by
    simpa only [and_true] using convolution_activation_flag_probability memory filters hMemory hFilters
      cap hCap M hM α (fun _ _ => True)
  have hPos : 0 < MeasureProb out success := by rw [hTotal]; exact div_pos hMass hCap
  refine ⟨hPos, ?_⟩
  rw [measureProb_postMeasure hPos, hTotal]
  have hi : success ∩ (Finset.univ.filter fun p => event p.1.1 p.1.2.1) =
      Finset.univ.filter fun p => p.2 = false ∧ event p.1.1 p.1.2.1 := by
    ext p
    simp [success]
  rw [hi, convolution_activation_flag_probability memory filters hMemory hFilters cap hCap M hM α event]
  exact div_div_div_cancel_right₀ hCap.ne' _ _

end Qatlib.Papers.QCNN20.Forward
