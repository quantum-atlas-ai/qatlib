/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Forward.MedianSampling

@[expose] public section

/-!
# Accuracy of the median activation sampler

[KerenidisLandmanPrakash2020], Sections D.1.4–D.1.5, read addresses with
weights proportional to the estimated activations. For the exact capped
activations the corresponding ideal weights are their products with the
initial address probabilities. An address-averaged inner product error
and the bad median mass control the difference before normalization.
When the ideal total activation dominates that error, conditioning on
the sampling flag is defined and the error bound holds for every address
event. The estimates use exact real rotations and repeated AE words.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Forward

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.AmplitudeCore.PreparedReadout (prepared_ae_expanded_access_and_output)
open Qatlib.Concepts.QueryComplexity.Amplification (PiTensorState normalized_piTensorState)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid valid_subtree)
open Qatlib.Papers.QCNN20.PatchMemory (patchTree)
open scoped BigOperators Classical

variable {positions window : ℕ} {Filter : Type} [Fintype Filter]

/-- The weight of an event if every address uses its actual capped convolution. -/
def convolutionIdealActivationMass (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (α : QState (Address positions × Filter)) (event : (Address positions × Filter) → Prop) : ℝ :=
  ∑ a ∈ Finset.univ.filter event,
    cappedRelu cap (convolutionEntry (patchTree memory a.1) (filters a.2)) * BornProb α a

/-- Good median records contribute the address-averaged resolution radius. Bad records
contribute at most the cap times their probability. -/
def convolutionMedianMassError (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M r : ℕ) (α : QState (Address positions × Filter)) : ℝ :=
  (∑ a, convolutionActivationRadius (patchTree memory a.1) (filters a.2) M * BornProb α a) + cap * (8 / 9) ^ r

/-- Any weight depending only on the address has the same expectation after the repeated word. -/
private theorem convolution_median_address_expectation (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (α : QState (Address positions × Filter)) (weight : Address positions × Filter → ℝ) :
    (∑ p, weight p.1 * BornProb (convolutionMedianCounters memory filters M (by omega) r α) p) =
      ∑ a, weight a * BornProb α a := by
  let A (a : Address positions × Filter) := convolutionPreparation (patchTree memory a.1) (filters a.2)
  let seed := (false, ZeroStr window)
  let S := differenceOutcomes window
  unfold convolutionMedianCounters
  rw [show (∑ p, weight p.1 * BornProb (addressedAERepeatedOutput (2 * r + 1) M (by omega) A seed
      (fun _ => S) α) p) = _ from addressed_ae_repeated_weighted_probability (2 * r + 1) M (by omega) A
      seed (fun _ => S) α (fun a _ => weight a)]
  apply Finset.sum_congr rfl
  intro a _
  let ψ := localCounterOutput M (by omega) (A a) seed S
  have hA := convolution_preparation_unitary _ _ (valid_subtree positions memory a.1 hMemory) (hFilters a.2)
  have hψ : Normalized ψ := (prepared_ae_expanded_access_and_output M hM (A a) seed S hA).2.2.2.1
  have hSum : (∑ p, BornProb (PiTensorState (fun _ : Fin (2 * r + 1) => ψ)) p) = 1 :=
    normalized_piTensorState (fun _ => hψ)
  change ‖α a‖ ^ 2 * (∑ p, weight a * BornProb (PiTensorState (fun _ : Fin (2 * r + 1) => ψ)) p) =
    weight a * ‖α a‖ ^ 2
  rw [← Finset.mul_sum, hSum, mul_one, mul_comm]

/-- Every decoded activation median remains within the cap interval. -/
private theorem convolution_median_activation_bounds {R : Type} (patch filter : Tree ℝ window) (cap : ℝ)
    (hCap : 0 ≤ cap) (M r : ℕ) (record : Fin (2 * r + 1) → Fin M × R) :
    0 ≤ convolutionMedianActivation patch filter cap M r record ∧
      convolutionMedianActivation patch filter cap M r record ≤ cap := by
  rw [← convolution_median_label_value patch filter cap M r record]
  exact ⟨capped_relu_nonneg _ _, max_le hCap (min_le_left _ _)⟩

/-- The actual median weights differ from the ideal activation weights by the same bound
for every address event. -/
theorem convolution_median_mass_error (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f)) (cap : ℝ) (hCap : 0 ≤ cap)
    (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (α : QState (Address positions × Filter)) (hα : Normalized α)
    (event : (Address positions × Filter) → Prop) :
    |convolutionMedianActivationMass memory filters cap M (by omega) r α (fun a _ => event a) -
      convolutionIdealActivationMass memory filters cap α event| ≤ convolutionMedianMassError memory filters cap M r α := by
  let J := (Address positions × Filter) × ConvolutionMedianRecord window M r
  let ψ := convolutionMedianCounters memory filters M (by omega) r α
  let estimate (p : J) := convolutionMedianActivation (patchTree memory p.1.1) (filters p.1.2) cap M r p.2
  let exactValue (a : Address positions × Filter) := cappedRelu cap (convolutionEntry (patchTree memory a.1) (filters a.2))
  let radius (a : Address positions × Filter) := convolutionActivationRadius (patchTree memory a.1) (filters a.2) M
  let failed (p : J) : Prop := radius p.1 < |estimate p - exactValue p.1|
  have hFail : MeasureProb ψ (Finset.univ.filter failed) ≤ (8 / 9 : ℝ) ^ r :=
    convolution_ae_median_failure memory filters hMemory hFilters cap M hM r α hα
  have hExpect (f : Address positions × Filter → ℝ) :=
    convolution_median_address_expectation memory filters hMemory hFilters M hM r α f
  have hDiff : convolutionMedianActivationMass memory filters cap M (by omega) r α (fun a _ => event a) -
      convolutionIdealActivationMass memory filters cap α event =
      ∑ p : J, (if event p.1 then estimate p - exactValue p.1 else 0) * BornProb ψ p := by
    unfold convolutionMedianActivationMass convolutionIdealActivationMass
    simp only [Finset.sum_filter]
    have hIdeal := hExpect (fun a => if event a then exactValue a else 0)
    simp only [ite_mul, zero_mul] at hIdeal
    change (∑ p : J, if event p.1 then estimate p * BornProb ψ p else 0) -
      (∑ a, if event a then exactValue a * BornProb α a else 0) = _
    rw [← hIdeal, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : event p.1
    · simp [hp, sub_mul, ψ]
    · simp [hp]
  have hPoint (p : J) :
      |(if event p.1 then estimate p - exactValue p.1 else 0) * BornProb ψ p| ≤
        radius p.1 * BornProb ψ p + cap * (if failed p then BornProb ψ p else 0) := by
    have hBorn := bornProb_nonneg ψ p
    have hRadius : 0 ≤ radius p.1 := by
      dsimp [radius, convolutionActivationRadius]
      positivity
    have hRight : 0 ≤ radius p.1 * BornProb ψ p + cap * (if failed p then BornProb ψ p else 0) := by
      exact add_nonneg (mul_nonneg hRadius hBorn) (mul_nonneg hCap (by split_ifs <;> positivity))
    by_cases hp : event p.1
    · rw [ite_eq_left hp, abs_mul, abs_of_nonneg hBorn]
      by_cases hb : failed p
      · rw [ite_eq_left hb]
        obtain ⟨hEstimate, hEstimateCap⟩ := convolution_median_activation_bounds
          (patchTree memory p.1.1) (filters p.1.2) cap hCap M r p.2
        have hExact : 0 ≤ exactValue p.1 := capped_relu_nonneg _ _
        have hExactCap : exactValue p.1 ≤ cap := max_le hCap (min_le_left _ _)
        have hBound : |estimate p - exactValue p.1| ≤ cap := abs_le.mpr ⟨by linarith, by linarith⟩
        exact (mul_le_mul_of_nonneg_right hBound hBorn).trans (le_add_of_nonneg_left (mul_nonneg hRadius hBorn))
      · simpa only [ite_eq_right hb, mul_zero, add_zero] using
          (mul_le_mul_of_nonneg_right (le_of_not_gt hb) hBorn)
    · simpa only [ite_eq_right hp, zero_mul, abs_zero] using hRight
  rw [hDiff]
  calc
    _ ≤ ∑ p : J, |(if event p.1 then estimate p - exactValue p.1 else 0) * BornProb ψ p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : J, (radius p.1 * BornProb ψ p + cap * (if failed p then BornProb ψ p else 0)) :=
      Finset.sum_le_sum fun p _ => hPoint p
    _ = (∑ a, radius a * BornProb α a) + cap * MeasureProb ψ (Finset.univ.filter failed) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, ← MeasureProb, hExpect radius]
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hFail hCap)

/-- Positive actual and ideal totals give a ratio error bound using the ideal total. -/
private theorem activation_ratio_error (x total y ideal ε : ℝ) (hTotal : 0 < total) (hIdeal : 0 < ideal)
    (hx : 0 ≤ x) (hxTotal : x ≤ total) (hEvent : |x - y| ≤ ε) (hMass : |total - ideal| ≤ ε) :
    |x / total - y / ideal| ≤ 2 * ε / ideal := by
  let ratio := x / total
  have hRatio : 0 ≤ ratio := div_nonneg hx hTotal.le
  have hOne : ratio ≤ 1 := (div_le_one hTotal).mpr hxTotal
  have hRearrange : (ratio - y / ideal) * ideal = (x - y) + ratio * (ideal - total) := by
    dsimp [ratio]
    field_simp [hTotal.ne', hIdeal.ne']
    ring
  have hScale : |ideal - total| ≤ ε := by rwa [abs_sub_comm]
  have hProduct : |ratio * (ideal - total)| ≤ ε := by
    rw [abs_mul, abs_of_nonneg hRatio]
    exact (mul_le_mul_of_nonneg_right hOne (abs_nonneg _)).trans (by simpa using hScale)
  apply (le_div_iff₀ hIdeal).mpr
  rw [show |x / total - y / ideal| * ideal = |(ratio - y / ideal) * ideal| by rw [abs_mul, abs_of_pos hIdeal],
    hRearrange]
  exact (abs_add_le _ _).trans (by linarith)

/-- If the ideal total exceeds the error budget, the final sampler has positive success
probability and its conditional address law approximates the ideal activation-weighted law. -/
theorem convolution_median_readout_accuracy (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (α : QState (Address positions × Filter))
    (hα : Normalized α) (event : (Address positions × Filter) → Prop)
    (hSignal : convolutionMedianMassError memory filters cap M r α <
      convolutionIdealActivationMass memory filters cap α (fun _ => True)) :
    let out := convolutionMedianReadout memory filters cap M (by omega) r α
    let good := medianReadoutEvent (R := ConvolutionMedianRecord window M r) (Z := Fin M)
      (fun (_ : Address positions × Filter) _ b => b = false)
    let ideal := convolutionIdealActivationMass memory filters cap α (fun _ => True)
    let ε := convolutionMedianMassError memory filters cap M r α
    0 < MeasureProb out good ∧
      |MeasureProb (PostMeasure out good) (Finset.univ.filter fun p => event p.1.1.1) -
        convolutionIdealActivationMass memory filters cap α event / ideal| ≤ 2 * ε / ideal := by
  intro out good ideal ε
  let x := convolutionMedianActivationMass memory filters cap M (by omega) r α (fun a _ => event a)
  let total := convolutionMedianActivationMass memory filters cap M (by omega) r α (fun _ _ => True)
  have hError : |total - ideal| ≤ ε :=
    convolution_median_mass_error memory filters hMemory hFilters cap hCap.le M hM r α hα (fun _ => True)
  have hEvent : |x - convolutionIdealActivationMass memory filters cap α event| ≤ ε :=
    convolution_median_mass_error memory filters hMemory hFilters cap hCap.le M hM r α hα event
  have hIdeal : 0 < ideal := lt_of_le_of_lt ((abs_nonneg _).trans hError) hSignal
  have hTotal : 0 < total := by
    have hLower := (abs_le.mp hError).1
    change ε < ideal at hSignal
    linarith
  have hx : 0 ≤ x := by
    unfold x convolutionMedianActivationMass
    apply Finset.sum_nonneg
    intro p _
    exact mul_nonneg (convolution_median_activation_bounds _ _ _ hCap.le _ _ _).1 (bornProb_nonneg _ _)
  have hxTotal : x ≤ total := by
    unfold x total convolutionMedianActivationMass
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp
    · intro p _ _
      exact mul_nonneg (convolution_median_activation_bounds _ _ _ hCap.le _ _ _).1 (bornProb_nonneg _ _)
  obtain ⟨hGood, hSample⟩ := convolution_median_readout_postselect memory filters hMemory hFilters cap hCap M hM r α
    (fun a _ => event a) hTotal
  refine ⟨hGood, ?_⟩
  rw [hSample]
  exact activation_ratio_error x total _ ideal ε hTotal hIdeal hx hxTotal hEvent hError

/-- After sampling succeeds, the decoded activation is still accurate outside a conditional
failure mass bounded by the median failure probability divided by the success probability. -/
theorem convolution_median_readout_label_failure (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (α : QState (Address positions × Filter))
    (hα : Normalized α)
    (hMass : 0 < convolutionMedianActivationMass memory filters cap M (by omega) r α (fun _ _ => True)) :
    let out := convolutionMedianReadout memory filters cap M (by omega) r α
    let good := medianReadoutEvent (R := ConvolutionMedianRecord window M r) (Z := Fin M)
      (fun (_ : Address positions × Filter) _ b => b = false)
    let bad (a : Address positions × Filter) (z : Fin M) :=
      convolutionActivationRadius (patchTree memory a.1) (filters a.2) M <
        |convolutionCounterActivation (patchTree memory a.1) (filters a.2) cap M z -
          cappedRelu cap (convolutionEntry (patchTree memory a.1) (filters a.2))|
    0 < MeasureProb out good ∧
      MeasureProb (PostMeasure out good) (Finset.univ.filter fun p => bad p.1.1.1 p.1.1.2) ≤
        (8 / 9 : ℝ) ^ r / MeasureProb out good := by
  intro out good bad
  let J := (Address positions × Filter) × ConvolutionMedianRecord window M r
  let counters := convolutionMedianCounters memory filters M (by omega) r α
  let median (p : J) := convolutionMedianActivation (patchTree memory p.1.1) (filters p.1.2) cap M r p.2
  let failed (p : J) := convolutionActivationRadius (patchTree memory p.1.1) (filters p.1.2) M <
    |median p - cappedRelu cap (convolutionEntry (patchTree memory p.1.1) (filters p.1.2))|
  have hFail : MeasureProb counters (Finset.univ.filter failed) ≤ (8 / 9 : ℝ) ^ r :=
    convolution_ae_median_failure memory filters hMemory hFilters cap M hM r α hα
  have hDecode : (Finset.univ.filter fun p : J => bad p.1
      (convolutionMedianLabel (patchTree memory p.1.1) (filters p.1.2) cap M r p.2)) =
      Finset.univ.filter failed := by
    ext p
    simp [bad, failed, median, convolution_median_label_value]
  have hWeighted : convolutionMedianActivationMass memory filters cap M (by omega) r α bad ≤ cap * (8 / 9) ^ r := by
    unfold convolutionMedianActivationMass
    rw [hDecode]
    calc
      _ ≤ ∑ p ∈ Finset.univ.filter failed, cap * BornProb counters p := by
        apply Finset.sum_le_sum
        intro p _
        exact mul_le_mul_of_nonneg_right (convolution_median_activation_bounds _ _ _ hCap.le _ _ _).2
          (bornProb_nonneg _ _)
      _ = cap * MeasureProb counters (Finset.univ.filter failed) := by rw [MeasureProb, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hFail hCap.le
  let total := convolutionMedianActivationMass memory filters cap M (by omega) r α (fun _ _ => True)
  have hProb : MeasureProb out good = total / cap := by
    dsimp only [out, good]
    rw [convolution_median_readout_event memory filters hMemory hFilters cap M hM r α (fun _ _ b => b = false)]
    simpa only [and_true] using convolution_median_flag_probability memory filters cap hCap M (by omega) r α
      (fun _ _ => True)
  obtain ⟨hGood, hSample⟩ := convolution_median_readout_postselect memory filters hMemory hFilters cap hCap M hM r α
    bad hMass
  refine ⟨hGood, ?_⟩
  rw [hSample, hProb]
  calc
    _ ≤ cap * (8 / 9 : ℝ) ^ r / total := div_le_div_of_nonneg_right hWeighted hMass.le
    _ = _ := by rw [div_div_eq_mul_div, mul_comm cap]

end Qatlib.Papers.QCNN20.Forward
