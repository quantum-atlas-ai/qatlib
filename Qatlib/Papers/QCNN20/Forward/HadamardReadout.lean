/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Forward.Convolution
public import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
public import Qatlib.Papers.MatProdVerify04.MainResults.HadamardTest

@[expose] public section

/-!
# Signed convolution from interference of patch and filter states

[KerenidisLandmanPrakash2020], Algorithm 1 and Section D.1.1, prepare two
branches by coherent patch and filter reads and apply a Hadamard to the
distinguishing flag. The difference branch recovers the signed normalized
inner product. The exact branch law yields an amplitude-estimation bound
for each addressed patch–filter pair, given a unitary that loads the two
states and interferes them. Address control, coherent median amplification,
and preparation costs require additional arguments.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QCNN20.Forward

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open Qatlib.Papers.MatProdVerify04.MainResults (hadamardFirstQubit hadamard_test_reflects)
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs (preparedAAState)
open Qatlib.Foundations.PureStateMath (MeasureProb)
open scoped BigOperators

variable {window : ℕ}

/-- The real difference-branch amplitudes of a patch–filter interference measurement. -/
noncomputable def differenceBranch (patch filter : Tree ℝ window) (slot : Address window) : ℝ :=
  (pathAmplitude patch slot - pathAmplitude filter slot) / 2

/-- The difference branch agrees pointwise with the Hadamard transformation of the loaded states. -/
theorem difference_branch_from_hadamard (patch filter : Tree ℝ window) (slot : Address window) :
    (hadamardFirstQubit
      ((Real.sqrt 2)⁻¹ • (fun j : Address window => (pathAmplitude patch j : ℂ)))
      ((Real.sqrt 2)⁻¹ • (fun j : Address window => (pathAmplitude filter j : ℂ)))).2 slot =
        (differenceBranch patch filter slot : ℂ) := by
  rw [hadamard_test_reflects]
  simp [differenceBranch, div_eq_mul_inv, mul_comm]

/-- The probability of measuring the difference-branch flag. -/
noncomputable def differenceWeight (patch filter : Tree ℝ window) : ℝ :=
  ∑ slot, differenceBranch patch filter slot ^ 2

/-- The difference-branch probability is half of one minus the signed real overlap. -/
theorem difference_weight_eq (patch filter : Tree ℝ window) (hp : Valid patch) (hf : Valid filter)
    (hpPos : 0 < mass patch) (hfPos : 0 < mass filter) :
    differenceWeight patch filter =
      (1 - ∑ slot, pathAmplitude patch slot * pathAmplitude filter slot) / 2 := by
  unfold differenceWeight differenceBranch
  simp_rw [div_pow, sub_sq]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_path_amplitude_sq patch hp hpPos, sum_path_amplitude_sq filter hf hfPos]
  have hFactor : (∑ slot, 2 * pathAmplitude patch slot * pathAmplitude filter slot) =
      2 * ∑ slot, pathAmplitude patch slot * pathAmplitude filter slot := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [hFactor]
  ring

/-- Rescaling the signed interference readout recovers the convolution entry. -/
theorem convolution_entry_from_difference_weight (patch filter : Tree ℝ window)
    (hp : Valid patch) (hf : Valid filter) (hpPos : 0 < mass patch) (hfPos : 0 < mass filter) :
    convolutionEntry patch filter =
      Real.sqrt (mass patch) * Real.sqrt (mass filter) * (1 - 2 * differenceWeight patch filter) := by
  rw [difference_weight_eq patch filter hp hf hpPos hfPos, convolutionEntry]
  ring

/-- Recover a preactivation from an estimate of the difference-branch probability. -/
noncomputable def estimateFromDifferenceWeight (patch filter : Tree ℝ window)
    (estimatedWeight : ℝ) : ℝ :=
  Real.sqrt (mass patch) * Real.sqrt (mass filter) * (1 - 2 * estimatedWeight)

/-- For a probability estimate of error at most epsilon, the activated convolution has error
at most twice epsilon times the product of the input norms. -/
theorem capped_convolution_error_le (patch filter : Tree ℝ window)
    (hp : Valid patch) (hf : Valid filter) (hpPos : 0 < mass patch) (hfPos : 0 < mass filter)
    (cap estimatedWeight epsilon : ℝ)
    (h : |estimatedWeight - differenceWeight patch filter| ≤ epsilon) :
    |cappedRelu cap (estimateFromDifferenceWeight patch filter estimatedWeight) -
      cappedRelu cap (convolutionEntry patch filter)| ≤
        (2 * (Real.sqrt (mass patch) * Real.sqrt (mass filter))) * epsilon := by
  refine (capped_relu_error_le _ _ _).trans ?_
  rw [estimateFromDifferenceWeight, convolution_entry_from_difference_weight patch filter hp hf hpPos hfPos]
  let scale := Real.sqrt (mass patch) * Real.sqrt (mass filter)
  change |scale * (1 - 2 * estimatedWeight) -
    scale * (1 - 2 * differenceWeight patch filter)| ≤ 2 * scale * epsilon
  have hDifference :
      scale * (1 - 2 * estimatedWeight) - scale * (1 - 2 * differenceWeight patch filter) =
        -(2 * scale) * (estimatedWeight - differenceWeight patch filter) := by ring
  have hScale : 0 ≤ 2 * scale :=
    mul_nonneg zero_le_two (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [hDifference, abs_mul, abs_neg, abs_of_nonneg hScale]
  exact mul_le_mul_of_nonneg_left h hScale

/-- The basis outcomes with the Hadamard flag in the difference branch. -/
noncomputable def differenceOutcomes (window : ℕ) : Finset (Bool × Address window) :=
  Finset.univ.map ⟨fun slot => (true, slot), fun _ _ h => congrArg Prod.snd h⟩

/-- Preparing the difference amplitudes gives the marked Born probability used in convolution. -/
theorem difference_outcomes_probability (patch filter : Tree ℝ window)
    (A : Matrix (Bool × Address window) (Bool × Address window) ℂ)
    (initial : Bool × Address window)
    (hBranch : ∀ slot, preparedAAState A initial (true, slot) =
      (differenceBranch patch filter slot : ℂ)) :
    MeasureProb (preparedAAState A initial) (differenceOutcomes window) =
      differenceWeight patch filter := by
  unfold MeasureProb differenceOutcomes differenceWeight
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro slot _
  change ‖preparedAAState A initial (true, slot)‖ ^ 2 = differenceBranch patch filter slot ^ 2
  rw [hBranch, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A single quantum amplitude-estimation readout attains the capped convolution error from
the BHMT probability bound. The supplied unitary prepares the Hadamard difference branch
of this patch–filter pair. -/
theorem capped_convolution_estimation_success (patch filter : Tree ℝ window)
    (hp : Valid patch) (hf : Valid filter) (hpPos : 0 < mass patch) (hfPos : 0 < mass filter)
    (cap : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix (Bool × Address window) (Bool × Address window) ℂ)
    (initial : Bool × Address window) (hA : A ∈ Matrix.unitaryGroup (Bool × Address window) ℂ)
    (hBranch : ∀ slot, preparedAAState A initial (true, slot) =
      (differenceBranch patch filter slot : ℂ)) :
    let a := differenceWeight patch filter
    let ε := 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |cappedRelu cap (estimateFromDifferenceWeight patch filter (aeEstimate M z)) -
          cappedRelu cap (convolutionEntry patch filter)| ≤
          (2 * (Real.sqrt (mass patch) * Real.sqrt (mass filter))) * ε),
        (aeLaw M A initial (differenceOutcomes window) hA hM).prob z := by
  dsimp only
  let a := differenceWeight patch filter
  let ε := 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2
  have h := (prepared_ae_bhmt_error_and_endpoints M hM A initial
    (differenceOutcomes window) hA).1
  rw [difference_outcomes_probability patch filter A initial hBranch] at h
  refine h.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact capped_convolution_error_le patch filter hp hf hpPos hfPos cap (aeEstimate M z) ε hz
  · intro z _ _
    exact (aeLaw M A initial (differenceOutcomes window) hA hM).nonneg z

end Qatlib.Papers.QCNN20.Forward
