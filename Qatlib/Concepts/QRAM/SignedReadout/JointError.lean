/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.SqrtFrequency

@[expose] public section

/-!
# Error bounds on the two tomography records

[KerenidisLandmanPrakash2020], Appendix G.4, decides the sign of a
nonzero coordinate by counting the interference flag conditional on
the observed reference. A bad first record is charged its actual
probability. On the other records, the conditional Chernoff bound
controls the error introduced by the second measurement.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces (eventMass_mono eventMass_or_le)
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript (jointLaw)
open scoped BigOperators Classical

/-- A uniform bound on good fibers bounds joint failure by the bad first-record mass
plus the conditional failure allowance. -/
theorem joint_event_le {H T : Type} [Fintype H] [Fintype T] (μ : FinDist H)
    (P : H → FinDist T) (badFirst : H → Prop) (failure : H × T → Prop) (ε : ℝ)
    (hε : 0 ≤ ε) (hf : ∀ h, ¬ badFirst h → eventMass (P h) (fun t => failure (h, t)) ≤ ε) :
    eventMass (jointLaw μ P) failure ≤ eventMass μ badFirst + ε := by
  have hFiber (h : H) : eventMass (P h) (fun t => failure (h, t)) ≤ 1 := by
    unfold eventMass
    calc
      _ ≤ ∑ t, (P h).prob t := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun t _ _ => (P h).nonneg t)
      _ = 1 := (P h).sum_one
  calc
    eventMass (jointLaw μ P) failure =
        ∑ h, μ.prob h * eventMass (P h) (fun t => failure (h, t)) := by
      simp only [eventMass, jointLaw, Finset.sum_filter, Fintype.sum_prod_type,
        Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ ∑ h, μ.prob h * ((if badFirst h then 1 else 0) + ε) := by
      apply Finset.sum_le_sum
      intro h _
      apply mul_le_mul_of_nonneg_left _ (μ.nonneg h)
      by_cases hb : badFirst h
      · rw [ite_eq_left hb]
        exact (hFiber h).trans (le_add_of_nonneg_right hε)
      · simpa only [ite_eq_right hb, zero_add] using hf h hb
    _ = eventMass μ badFirst + ε := by
      simp only [eventMass, Finset.sum_filter, mul_add, Finset.sum_add_distrib,
        mul_ite, mul_one, mul_zero, ← Finset.sum_mul, μ.sum_one, one_mul]

variable {depth : ℕ}

/-- On the first record, a heavy coordinate needs both an accurate magnitude and a
reference probability within the range supporting the sign test. -/
def heavyCoordinateBadBasis (basis : List (Address depth)) (address : Address depth)
    (value tolerance : ℝ) : Prop :=
  tolerance < |Real.sqrt (frequency basis address) - abs value| ∨
    frequency basis address < value ^ 2 / 2 ∨ 3 * value ^ 2 / 2 < frequency basis address

/-- The three ways that the first measurement record can fail on a heavy coordinate
have exponential bounds in the number of basis shots times the squared tolerance. -/
theorem heavy_basis_error_probability (state : Address depth → ℝ) (hState : ∑ i, state i ^ 2 = 1)
    (address : Address depth) (basisShots : ℕ) (hBasis : 0 < basisShots)
    (tolerance : ℝ) (hTolerance : 0 < tolerance) (hHeavy : tolerance < |state address|) :
    eventMass (independentSampleLaw (fun _ : Fin basisShots => basisSampleLaw state hState))
      (fun record => heavyCoordinateBadBasis (List.ofFn record) address (state address) tolerance) ≤
      2 * Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 2) +
      Real.exp (-(3 / 20 : ℝ) * basisShots * tolerance ^ 2) +
      Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 10) := by
  let p := basisSampleLaw state hState
  let μ := independentSampleLaw (fun _ : Fin basisShots => p)
  let magnitudeBad := fun record : Fin basisShots → Address depth =>
    tolerance < |Real.sqrt (frequency (List.ofFn record) address) - abs (state address)|
  let tooSmall := fun record : Fin basisShots → Address depth =>
    frequency (List.ofFn record) address < state address ^ 2 / 2
  let tooLarge := fun record : Fin basisShots → Address depth =>
    3 * state address ^ 2 / 2 < frequency (List.ofFn record) address
  have hn : (0 : ℝ) < basisShots := Nat.cast_pos.mpr hBasis
  have hSquare : tolerance ^ 2 ≤ state address ^ 2 := by
    rw [← sq_abs (state address)]
    exact (sq_le_sq₀ hTolerance.le (abs_nonneg _)).mpr hHeavy.le
  have hMag : eventMass μ magnitudeBad ≤ 2 * Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 2) := by
    refine (eventMass_mono μ magnitudeBad
      (fun record => tolerance ≤ |Real.sqrt (((List.ofFn record).count address : ℝ) / basisShots) -
        Real.sqrt (p.prob address)|) ?_).trans
      (sqrt_frequency_error_probability p address basisShots hBasis tolerance hTolerance)
    intro b h
    simpa only [magnitudeBad, frequency, List.length_ofFn, p, basisSampleLaw, Real.sqrt_sq_eq_abs] using h.le
  have hSmall : eventMass μ tooSmall ≤ Real.exp (-(3 / 20 : ℝ) * basisShots * tolerance ^ 2) := by
    refine (eventMass_mono μ tooSmall (fun record =>
      ((List.ofFn record).count address : ℝ) ≤ basisShots * p.prob address / 2) ?_).trans
      ((count_half_lower p address basisShots).trans (Real.exp_le_exp.mpr ?_))
    · intro b h
      have hh : ((List.ofFn b).count address : ℝ) / basisShots < state address ^ 2 / 2 := by
        simpa only [tooSmall, frequency, List.length_ofFn] using h
      have ht := (div_lt_iff₀ hn).mp hh
      change ((List.ofFn b).count address : ℝ) ≤ (basisShots : ℝ) * state address ^ 2 / 2
      linarith only [ht]
    · change -(3 / 20 : ℝ) * basisShots * state address ^ 2 ≤ _
      exact mul_le_mul_of_nonpos_left hSquare (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hn.le)
  have hLarge : eventMass μ tooLarge ≤ Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 10) := by
    refine (eventMass_mono μ tooLarge (fun record =>
      (3 / 2 : ℝ) * basisShots * p.prob address ≤ ((List.ofFn record).count address : ℝ)) ?_).trans
      ((count_three_halves_upper p address basisShots).trans (Real.exp_le_exp.mpr ?_))
    · intro b h
      have hh : 3 * state address ^ 2 / 2 < ((List.ofFn b).count address : ℝ) / basisShots := by
        simpa only [tooLarge, frequency, List.length_ofFn] using h
      have ht := (lt_div_iff₀ hn).mp hh
      change (3 / 2 : ℝ) * basisShots * state address ^ 2 ≤ ((List.ofFn b).count address : ℝ)
      linarith only [ht]
    · change -((basisShots : ℝ) * state address ^ 2) / 10 ≤ _
      have hRate := div_le_div_of_nonneg_right
        (neg_le_neg (mul_le_mul_of_nonneg_left hSquare hn.le)) (by norm_num : (0 : ℝ) ≤ 10)
      simpa only [neg_mul] using hRate
  refine (eventMass_mono μ
    (fun record => heavyCoordinateBadBasis (List.ofFn record) address (state address) tolerance)
    (fun record => magnitudeBad record ∨ tooSmall record ∨ tooLarge record) (fun _ h => h)).trans ?_
  calc
    _ ≤ eventMass μ magnitudeBad + eventMass μ (fun record => tooSmall record ∨ tooLarge record) :=
      eventMass_or_le μ magnitudeBad _
    _ ≤ eventMass μ magnitudeBad + (eventMass μ tooSmall + eventMass μ tooLarge) :=
      add_le_add le_rfl (eventMass_or_le μ tooSmall tooLarge)
    _ ≤ _ := by
      rw [← add_assoc]
      exact add_le_add (add_le_add hMag hSmall) hLarge

/-- For a coordinate above the tolerance, its signed readout failure probability
is at most the bad first-record mass plus the exponential conditional sign tail. -/
theorem heavy_coordinate_error_probability (state : Address depth → ℝ)
    (hState : ∑ i, state i ^ 2 = 1) (address : Address depth)
    (basisShots interferenceShots : ℕ) (hBasis : 0 < basisShots)
    (tolerance : ℝ) (hTolerance : 0 ≤ tolerance) (hHeavy : tolerance < |state address|) :
    eventMass (signedTomographyLaw state hState basisShots interferenceShots hBasis)
      (fun pair => tolerance <
        |signedCoordinate (List.ofFn pair.1) (List.ofFn pair.2) address - state address|) ≤
      eventMass (independentSampleLaw (fun _ : Fin basisShots => basisSampleLaw state hState))
        (fun record => heavyCoordinateBadBasis (List.ofFn record) address (state address) tolerance) +
      Real.exp (-(interferenceShots : ℝ) * tolerance ^ 2 / 16) := by
  have hNonzero : state address ≠ 0 := by
    intro h
    rw [h, abs_zero] at hHeavy
    exact (not_lt_of_ge hTolerance) hHeavy
  have hSquare : tolerance ^ 2 ≤ state address ^ 2 := by
    rw [← sq_abs (state address)]
    exact (sq_le_sq₀ hTolerance (abs_nonneg _)).mpr hHeavy.le
  unfold signedTomographyLaw
  refine joint_event_le _ _ _ _ _ (Real.exp_nonneg _) ?_
  intro b hGood
  let basis := List.ofFn b
  have hList : basis ≠ [] := by
    intro hEmpty
    have hLength := congrArg List.length hEmpty
    simp only [basis, List.length_ofFn, List.length_nil] at hLength
    exact hBasis.ne' hLength
  have hMagnitude : |Real.sqrt (frequency basis address) - abs (state address)| ≤ tolerance :=
    le_of_not_gt (fun h => hGood (Or.inl h))
  have hLower : state address ^ 2 / 2 ≤ frequency basis address :=
    le_of_not_gt (fun h => hGood (Or.inr (Or.inl h)))
  have hUpper : frequency basis address ≤ 3 * state address ^ 2 / 2 :=
    le_of_not_gt (fun h => hGood (Or.inr (Or.inr h)))
  let threshold := (2 / 5 : ℝ) * interferenceShots * frequency basis address
  let wrongSign := fun record : Fin interferenceShots → Bool × Address depth =>
    if 0 < state address then ((List.ofFn record).count (false, address) : ℝ) ≤ threshold
    else threshold < ((List.ofFn record).count (false, address) : ℝ)
  have hSign := conditional_sign_error_probability state hState basis hList address interferenceShots
    hNonzero hLower hUpper
  refine (eventMass_mono _ _ wrongSign ?_).trans (hSign.trans (Real.exp_le_exp.mpr ?_))
  · intro record hFailure
    by_contra hWrong
    apply (not_lt_of_ge (signed_coordinate_error_of_count_sign basis (List.ofFn record)
      address (state address) tolerance hMagnitude ?_ ?_)) hFailure
    · intro hPos
      simp only [wrongSign, ite_eq_left hPos, not_le] at hWrong
      simpa only [List.length_ofFn] using hWrong
    · intro hNeg
      simp only [wrongSign, ite_eq_right (not_lt_of_ge hNeg.le), not_lt] at hWrong
      simpa only [List.length_ofFn] using hWrong
  · have hFrequency : tolerance ^ 2 / 2 ≤ frequency basis address :=
      (div_le_div_of_nonneg_right hSquare (by norm_num)).trans hLower
    have hMul := mul_le_mul_of_nonneg_left hFrequency (Nat.cast_nonneg interferenceShots : (0 : ℝ) ≤ _)
    nlinarith only [hMul]

/-- The full measured error for a heavy coordinate combines three basis tails with the
conditional interference tail. -/
theorem heavy_coordinate_measured_error_probability (state : Address depth → ℝ)
    (hState : ∑ i, state i ^ 2 = 1) (address : Address depth)
    (basisShots interferenceShots : ℕ) (hBasis : 0 < basisShots)
    (tolerance : ℝ) (hTolerance : 0 < tolerance) (hHeavy : tolerance < |state address|) :
    eventMass (signedTomographyLaw state hState basisShots interferenceShots hBasis)
      (fun pair => tolerance <
        |signedCoordinate (List.ofFn pair.1) (List.ofFn pair.2) address - state address|) ≤
      2 * Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 2) +
      Real.exp (-(3 / 20 : ℝ) * basisShots * tolerance ^ 2) +
      Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 10) +
      Real.exp (-(interferenceShots : ℝ) * tolerance ^ 2 / 16) := by
  exact (heavy_coordinate_error_probability state hState address basisShots interferenceShots hBasis
    tolerance hTolerance.le hHeavy).trans
    (add_le_add (heavy_basis_error_probability state hState address basisShots hBasis
      tolerance hTolerance hHeavy) le_rfl)

/-- A light coordinate is accurate regardless of its measured sign, unless the basis count
exceeds twice the squared tolerance. That event has an exponential first-record bound. -/
theorem light_coordinate_measured_error_probability (state : Address depth → ℝ)
    (hState : ∑ i, state i ^ 2 = 1) (address : Address depth)
    (basisShots interferenceShots : ℕ) (hBasis : 0 < basisShots)
    (tolerance : ℝ) (hTolerance : 0 ≤ tolerance) (hLight : |state address| ≤ tolerance) :
    eventMass (signedTomographyLaw state hState basisShots interferenceShots hBasis)
      (fun pair => (1 + Real.sqrt 2) * tolerance <
        |signedCoordinate (List.ofFn pair.1) (List.ofFn pair.2) address - state address|) ≤
      Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 3) := by
  let p := basisSampleLaw state hState
  let μ := independentSampleLaw (fun _ : Fin basisShots => p)
  let badFirst := fun record : Fin basisShots → Address depth =>
    2 * tolerance ^ 2 < frequency (List.ofFn record) address
  have hn : (0 : ℝ) < basisShots := Nat.cast_pos.mpr hBasis
  have hSmall : p.prob address ≤ tolerance ^ 2 := by
    change state address ^ 2 ≤ tolerance ^ 2
    rw [← sq_abs (state address)]
    exact (sq_le_sq₀ (abs_nonneg _) hTolerance).mpr hLight
  have hBadFirst : eventMass μ badFirst ≤ Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 3) := by
    let threshold := 2 * (basisShots : ℝ) * tolerance ^ 2
    refine (eventMass_mono μ badFirst (fun record => threshold ≤ ((List.ofFn record).count address : ℝ))
      ?_).trans ((count_upper_exp p address basisShots threshold (Real.log 2)
      (Real.log_nonneg (by norm_num))).trans (Real.exp_le_exp.mpr ?_))
    · intro b h
      have hh : 2 * tolerance ^ 2 < ((List.ofFn b).count address : ℝ) / basisShots := by
        simpa only [badFirst, frequency, List.length_ofFn] using h
      have ht := (lt_div_iff₀ hn).mp hh
      dsimp [threshold]
      linarith only [ht]
    · rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hMass := mul_le_mul_of_nonneg_left hSmall hn.le
      have hCompare : (2 / 3 : ℝ) * threshold ≤ Real.log 2 * threshold :=
        mul_le_mul_of_nonneg_right (by linarith [Real.log_two_gt_d9]) (by positivity)
      dsimp [threshold] at hCompare ⊢
      nlinarith only [hMass, hCompare]
  unfold signedTomographyLaw
  refine (joint_event_le μ _ badFirst _ 0 le_rfl ?_).trans (by simpa only [add_zero] using hBadFirst)
  intro b hGood
  refine (eventMass_mono _ _ (fun _ => False) ?_).trans (by simp [eventMass])
  intro record hFailure
  exact (not_lt_of_ge (signed_coordinate_error_of_small_frequency (List.ofFn b) (List.ofFn record)
    address (state address) tolerance hTolerance hLight (le_of_not_gt hGood))) hFailure

/-- The union of bad coordinate events has mass at most the sum of their individual masses. -/
private theorem eventMass_exists_coord_le {Ω A : Type} [Fintype Ω] [Fintype A] (p : FinDist Ω)
    (failure : Ω → A → Prop) :
    eventMass p (fun record => ∃ i, failure record i) ≤ ∑ i, eventMass p (fun record => failure record i) := by
  simp only [eventMass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro record _
  by_cases h : ∃ i, failure record i
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    calc
      p.prob record = if failure record i then p.prob record else 0 := by simp [hi]
      _ ≤ _ := Finset.single_le_sum (f := fun j : A => if failure record j then p.prob record else 0)
        (fun j _ => by by_cases hj : failure record j <;> simp [hj, p.nonneg record])
        (Finset.mem_univ i)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by by_cases hj : failure record j <;> simp [hj, p.nonneg record])

/-- Simultaneous signed-coordinate readout is accurate to
`(1 + sqrt 2) * tolerance` except on the displayed finite-measurement tail.
The bound counts both measurement batches and includes addresses absent from the sparse output. -/
theorem signed_tomography_measured_error_probability (state : Address depth → ℝ)
    (hState : ∑ i, state i ^ 2 = 1) (basisShots interferenceShots : ℕ) (hBasis : 0 < basisShots)
    (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    let law := signedTomographyLaw state hState basisShots interferenceShots hBasis
    let failure := fun pair : (Fin basisShots → Address depth) × (Fin interferenceShots → Bool × Address depth) =>
      fun i => (1 + Real.sqrt 2) * tolerance <
        |signedCoordinate (List.ofFn pair.1) (List.ofFn pair.2) i - state i|
    eventMass law (fun pair => ∃ i, failure pair i) ≤
      (Fintype.card (Address depth) : ℝ) *
        (2 * Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 2) +
          Real.exp (-(3 / 20 : ℝ) * basisShots * tolerance ^ 2) +
          Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 10) +
          Real.exp (-(interferenceShots : ℝ) * tolerance ^ 2 / 16)) := by
  intro law failure
  refine (eventMass_exists_coord_le law failure).trans ?_
  have hSum (bound : ℝ) : (∑ _ : Address depth, bound) =
      (Fintype.card (Address depth) : ℝ) * bound := by simp
  rw [← hSum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hHeavy : tolerance < |state i|
  · have hThreshold : tolerance ≤ (1 + Real.sqrt 2) * tolerance := by
      nlinarith [mul_nonneg (Real.sqrt_nonneg 2) hTolerance.le]
    exact (eventMass_mono law (fun pair => failure pair i)
      (fun pair => tolerance < |signedCoordinate (List.ofFn pair.1) (List.ofFn pair.2) i - state i|)
      (fun _ h => hThreshold.trans_lt h)).trans
      (heavy_coordinate_measured_error_probability state hState i basisShots interferenceShots hBasis
        tolerance hTolerance hHeavy)
  · have hTail := light_coordinate_measured_error_probability state hState i basisShots
      interferenceShots hBasis tolerance hTolerance.le (le_of_not_gt hHeavy)
    refine hTail.trans ?_
    have hn : 0 ≤ (basisShots : ℝ) * tolerance ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hExp : Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 3) ≤
        Real.exp (-(basisShots : ℝ) * tolerance ^ 2 / 10) := Real.exp_le_exp.mpr (by nlinarith)
    linarith only [hExp, Real.exp_nonneg (-(basisShots : ℝ) * tolerance ^ 2 / 2),
      Real.exp_nonneg (-(3 / 20 : ℝ) * basisShots * tolerance ^ 2),
      Real.exp_nonneg (-(interferenceShots : ℝ) * tolerance ^ 2 / 16)]

/-- A count for each of the two measurement batches at an amplitude tolerance and
a prescribed overall failure probability. -/
def tomographyShots (depth : ℕ) (tolerance failure : ℝ) : ℕ :=
  max 1 ⌈16 * Real.log (5 * (Fintype.card (Address depth) : ℝ) / failure) / tolerance ^ 2⌉₊

/-- The prescribed number of basis shots is positive, so every first record can
prepare a normalized empirical reference. -/
theorem tomography_shots_pos (depth : ℕ) (tolerance failure : ℝ) :
    0 < tomographyShots depth tolerance failure :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Using the prescribed count in both batches makes the simultaneous signed-coordinate
failure probability at most the requested budget. -/
theorem signed_tomography_failure_le_budget (state : Address depth → ℝ)
    (hState : ∑ i, state i ^ 2 = 1) (tolerance failure : ℝ)
    (hTolerance : 0 < tolerance) (hFailure : 0 < failure) :
    let n := tomographyShots depth tolerance failure
    let law := signedTomographyLaw state hState n n (tomography_shots_pos depth tolerance failure)
    eventMass law (fun pair => ∃ i, (1 + Real.sqrt 2) * tolerance <
      |signedCoordinate (List.ofFn pair.1) (List.ofFn pair.2) i - state i|) ≤ failure := by
  let n := tomographyShots depth tolerance failure
  let d := (Fintype.card (Address depth) : ℝ)
  have hd : 0 < d := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
  have hSquare : 0 < tolerance ^ 2 := pow_pos hTolerance _
  have hCount : 16 * Real.log (5 * d / failure) / tolerance ^ 2 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hRate : Real.log (5 * d / failure) ≤ (n : ℝ) * tolerance ^ 2 / 16 := by
    have := (div_le_iff₀ hSquare).mp hCount
    linarith
  let e := Real.exp (-(n : ℝ) * tolerance ^ 2 / 16)
  have he : e ≤ failure / (5 * d) := by
    calc
      _ ≤ Real.exp (-Real.log (5 * d / failure)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (div_pos (by positivity) hFailure), inv_div]
  have hNonneg : 0 ≤ (n : ℝ) * tolerance ^ 2 := mul_nonneg (Nat.cast_nonneg _) hSquare.le
  have hFirst : Real.exp (-(n : ℝ) * tolerance ^ 2 / 2) ≤ e :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hHalf : Real.exp (-(3 / 20 : ℝ) * n * tolerance ^ 2) ≤ e :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hLarge : Real.exp (-(n : ℝ) * tolerance ^ 2 / 10) ≤ e :=
    Real.exp_le_exp.mpr (by nlinarith)
  refine (signed_tomography_measured_error_probability state hState n n
    (tomography_shots_pos depth tolerance failure) tolerance hTolerance).trans ?_
  calc
    _ ≤ d * (5 * e) := by
      apply mul_le_mul_of_nonneg_left _ hd.le
      change 2 * Real.exp (-(n : ℝ) * tolerance ^ 2 / 2) +
        Real.exp (-(3 / 20 : ℝ) * n * tolerance ^ 2) +
        Real.exp (-(n : ℝ) * tolerance ^ 2 / 10) + e ≤ 5 * e
      linarith only [hFirst, hHalf, hLarge]
    _ ≤ d * (5 * (failure / (5 * d))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by norm_num)) hd.le
    _ = failure := by field_simp [hd.ne']

end Qatlib.Concepts.QRAM.SignedReadout
