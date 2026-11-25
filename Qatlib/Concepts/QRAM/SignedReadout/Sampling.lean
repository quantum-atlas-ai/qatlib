/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.Tomography
public import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
public import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
public import Qatlib.Concepts.QueryComplexity.Amplification.PiTensorState
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Finite sample laws for signed QRAM tomography

[KerenidisLandmanPrakash2020], Appendix G, samples the unknown real state
in the computational basis and then interferes it with the state prepared
from the empirical square-root frequencies. Each interference shot uses
the reference determined by the first record. The finite joint law
preserves this dependence. The count moment and tail bounds apply to
both the basis shots and the interference shots conditional on a record.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript (jointLaw)
open Qatlib.Concepts.QueryComplexity.Amplification (PiTensorState bornProb_piTensorState)
open Qatlib.Foundations.PureStateMath (BornProb)
open scoped BigOperators Classical

variable {depth : ℕ}

/-- The basis law has probabilities equal to the squared amplitudes of the signed state. -/
def basisSampleLaw (state : Address depth → ℝ) (hState : ∑ i, state i ^ 2 = 1) :
    FinDist (Address depth) where
  prob i := state i ^ 2
  nonneg i := sq_nonneg (state i)
  sum_one := hState

/-- The post-Hadamard real amplitudes occupy both flag branches. -/
def interferenceAmplitude (state : Address depth → ℝ) (samples : List (Address depth))
    (outcome : Bool × Address depth) : ℝ :=
  if outcome.1 then (state outcome.2 - pathAmplitude (empiricalTree samples) outcome.2) / 2
  else positiveAmplitude state samples outcome.2

/-- The empirical reference state has signed amplitudes equal to the square roots of basis
frequencies when there is at least one basis shot. -/
theorem reference_amplitude_eq_sqrt_frequency (samples : List (Address depth)) (h : samples ≠ [])
    (i : Address depth) :
    pathAmplitude (empiricalTree samples) i = Real.sqrt (frequency samples i) := by
  rw [path_amplitude_eq _ (valid_empirical_tree samples), empirical_tree_mass samples h,
    Real.sqrt_one, div_one, read_empirical_tree]

/-- Squaring and summing the two Hadamard branches gives one on normalized inputs. -/
theorem sum_interference_amplitude_sq (state : Address depth → ℝ) (hState : ∑ i, state i ^ 2 = 1)
    (samples : List (Address depth)) (h : samples ≠ []) :
    ∑ z, interferenceAmplitude state samples z ^ 2 = 1 := by
  have hRef : ∑ i, pathAmplitude (empiricalTree samples) i ^ 2 = 1 := by
    apply sum_path_amplitude_sq _ (valid_empirical_tree samples)
    rw [empirical_tree_mass samples h]
    exact zero_lt_one
  have hPair (i : Address depth) :
      interferenceAmplitude state samples (true, i) ^ 2 +
        interferenceAmplitude state samples (false, i) ^ 2 =
        (state i ^ 2 + pathAmplitude (empiricalTree samples) i ^ 2) / 2 := by
    simp [interferenceAmplitude, positiveAmplitude]
    ring
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  simp_rw [hPair, ← Finset.sum_div, Finset.sum_add_distrib, hState, hRef]
  norm_num

/-- The interference shot is distributed according to the squared flag-and-address amplitudes. -/
def interferenceSampleLaw (state : Address depth → ℝ) (hState : ∑ i, state i ^ 2 = 1)
    (samples : List (Address depth)) (h : samples ≠ []) : FinDist (Bool × Address depth) where
  prob outcome := interferenceAmplitude state samples outcome ^ 2
  nonneg _ := sq_nonneg _
  sum_one := sum_interference_amplitude_sq state hState samples h

/-- The probability of a particular basis shot is its Born weight. -/
theorem basis_sample_born (state : Address depth → ℝ) (hState : ∑ i, state i ^ 2 = 1)
    (i : Address depth) :
    (basisSampleLaw state hState).prob i = BornProb (fun j => (state j : ℂ)) i := by
  simp [basisSampleLaw, BornProb, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The probability of an interference shot is the Born weight of the corresponding output. -/
theorem interference_sample_born (state : Address depth → ℝ) (hState : ∑ i, state i ^ 2 = 1)
    (samples : List (Address depth)) (h : samples ≠ []) (outcome : Bool × Address depth) :
    (interferenceSampleLaw state hState samples h).prob outcome =
      BornProb (fun z => (interferenceAmplitude state samples z : ℂ)) outcome := by
  simp [interferenceSampleLaw, BornProb, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The interference reference is chosen after observing the first record. -/
def signedTomographyLaw (state : Address depth → ℝ) (hState : ∑ i, state i ^ 2 = 1)
    (basisShots interferenceShots : ℕ) (hBasis : 0 < basisShots) :
    FinDist ((Fin basisShots → Address depth) × (Fin interferenceShots → Bool × Address depth)) :=
  jointLaw (independentSampleLaw fun _ => basisSampleLaw state hState)
    (fun b => independentSampleLaw fun _ =>
      interferenceSampleLaw state hState (List.ofFn b) (by
        intro hEmpty
        have hLength := congrArg List.length hEmpty
        simp only [List.length_ofFn, List.length_nil] at hLength
        exact hBasis.ne' hLength))

/-- Each pair of records has the product of the first tensor measurement probability
and the second tensor measurement probability for the reference built from the first. -/
theorem signed_tomography_law_born (state : Address depth → ℝ) (hState : ∑ i, state i ^ 2 = 1)
    {basisShots interferenceShots : ℕ} (hBasis : 0 < basisShots)
    (b : Fin basisShots → Address depth) (s : Fin interferenceShots → Bool × Address depth) :
    (signedTomographyLaw state hState basisShots interferenceShots hBasis).prob (b, s) =
      BornProb (PiTensorState fun (_ : Fin basisShots) i => (state i : ℂ)) b *
        BornProb (PiTensorState fun (_ : Fin interferenceShots) z =>
          (interferenceAmplitude state (List.ofFn b) z : ℂ)) s := by
  simp only [signedTomographyLaw, jointLaw, independentSampleLaw, bornProb_piTensorState,
    basis_sample_born, interference_sample_born]

/-- Counting a label in the list of shots equals summing its occurrence indicators. -/
theorem count_shots_eq_sum {X : Type*} [DecidableEq X] {n : ℕ} (shots : Fin n → X) (a : X) :
    ((List.ofFn shots).count a : ℝ) = ∑ i, if shots i = a then (1 : ℝ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    by_cases h : shots 0 = a
    · simp [h, ih, add_comm]
    · simp [h, ih]

/-- The moment of the one-shot occurrence indicator is the Bernoulli exponential moment. -/
private theorem indicator_exp_moment {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (t : ℝ) :
    p.expect (fun x => Real.exp (t * (if x = a then 1 else 0))) =
      1 - p.prob a + p.prob a * Real.exp t := by
  have hPoint (x : X) :
      p.prob x * Real.exp (t * (if x = a then 1 else 0)) =
        p.prob x + (if x = a then p.prob a * (Real.exp t - 1) else 0) := by
    by_cases h : x = a
    · subst x
      simp
      ring
    · simp [h]
  unfold FinDist.expect
  simp_rw [hPoint]
  rw [Finset.sum_add_distrib, p.sum_one, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ a)]
  ring

/-- The count in an independent record has the binomial exponential moment. This statement
uses the same list count consumed by the sparse tomography estimator. -/
theorem count_exp_moment {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) (t : ℝ) :
    (independentSampleLaw (fun _ : Fin n => p)).expect
      (fun shots => Real.exp (t * ((List.ofFn shots).count a : ℝ))) =
        (1 - p.prob a + p.prob a * Real.exp t) ^ n := by
  rw [← independent_fin_eq_sampleLaw]
  simp_rw [count_shots_eq_sum, Finset.mul_sum, Real.exp_sum]
  rw [independent_expect_product (fun _ : Fin n => p)
    (fun _ x => Real.exp (t * (if x = a then 1 else 0)))]
  simp only [indicator_exp_moment, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- An upper count event is bounded by the binomial exponential moment at any nonnegative
Chernoff parameter. -/
theorem count_upper_tail {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) (threshold t : ℝ) (ht : 0 ≤ t) :
    eventMass (independentSampleLaw fun _ : Fin n => p)
      (fun shots => threshold ≤ ((List.ofFn shots).count a : ℝ)) ≤
        Real.exp (-(t * threshold)) * (1 - p.prob a + p.prob a * Real.exp t) ^ n := by
  have h := chernoff_upper (independentSampleLaw fun _ : Fin n => p)
    (fun shots => ((List.ofFn shots).count a : ℝ)) threshold t ht
  rwa [count_exp_moment] at h

/-- A lower count event is bounded by the binomial exponential moment at the opposite
Chernoff parameter. -/
theorem count_lower_tail {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) (threshold t : ℝ) (ht : 0 ≤ t) :
    eventMass (independentSampleLaw fun _ : Fin n => p)
      (fun shots => ((List.ofFn shots).count a : ℝ) ≤ threshold) ≤
        Real.exp (t * threshold) * (1 - p.prob a + p.prob a * Real.exp (-t)) ^ n := by
  have h := chernoff_upper (independentSampleLaw fun _ : Fin n => p)
    (fun shots => -((List.ofFn shots).count a : ℝ)) (-threshold) t ht
  simp only [neg_le_neg_iff, mul_neg, neg_neg, ← neg_mul] at h
  rwa [count_exp_moment] at h

/-- Bound the binomial moment by the exponential of the Bernoulli increment. -/
private theorem count_moment_le_exp {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) (t : ℝ) :
    (1 - p.prob a + p.prob a * Real.exp t) ^ n ≤
      Real.exp (n * (p.prob a * (Real.exp t - 1))) := by
  have hp : p.prob a ≤ 1 := by
    rw [← p.sum_one]
    exact Finset.single_le_sum (fun x _ => p.nonneg x) (Finset.mem_univ a)
  have hNonneg : 0 ≤ 1 - p.prob a + p.prob a * Real.exp t :=
    add_nonneg (sub_nonneg.mpr hp) (mul_nonneg (p.nonneg a) (Real.exp_nonneg _))
  have hTerm : 1 - p.prob a + p.prob a * Real.exp t ≤ Real.exp (p.prob a * (Real.exp t - 1)) :=
    calc
      _ = p.prob a * (Real.exp t - 1) + 1 := by ring
      _ ≤ _ := Real.add_one_le_exp _
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hNonneg hTerm _

/-- Exponential-form upper count bound. -/
theorem count_upper_exp {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) (threshold t : ℝ) (ht : 0 ≤ t) :
    eventMass (independentSampleLaw fun _ : Fin n => p)
      (fun shots => threshold ≤ ((List.ofFn shots).count a : ℝ)) ≤
        Real.exp (-(t * threshold) + n * (p.prob a * (Real.exp t - 1))) := by
  rw [Real.exp_add]
  exact (count_upper_tail p a n threshold t ht).trans
    (mul_le_mul_of_nonneg_left (count_moment_le_exp p a n t) (Real.exp_nonneg _))

/-- Exponential-form lower count bound. -/
theorem count_lower_exp {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) (threshold t : ℝ) (ht : 0 ≤ t) :
    eventMass (independentSampleLaw fun _ : Fin n => p)
      (fun shots => ((List.ofFn shots).count a : ℝ) ≤ threshold) ≤
        Real.exp (t * threshold + n * (p.prob a * (Real.exp (-t) - 1))) := by
  rw [Real.exp_add]
  exact (count_lower_tail p a n threshold t ht).trans
    (mul_le_mul_of_nonneg_left (count_moment_le_exp p a n (-t)) (Real.exp_nonneg _))

/-- The chance of seeing at least one and a half times the expected count decays
exponentially in the expected count. -/
theorem count_three_halves_upper {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) :
    eventMass (independentSampleLaw fun _ : Fin n => p)
      (fun shots => (3 / 2 : ℝ) * n * p.prob a ≤ ((List.ofFn shots).count a : ℝ)) ≤
        Real.exp (-(n * p.prob a) / 10) := by
  refine (count_upper_exp p a n _ (1 / 3) (by norm_num)).trans (Real.exp_le_exp.mpr ?_)
  have hExp : Real.exp (1 / 3 : ℝ) ≤ 7 / 5 := by
    have h := Real.exp_le_two_add_div_two_sub
      (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  calc
    _ = (n * p.prob a) * (Real.exp (1 / 3 : ℝ) - 3 / 2) := by ring
    _ ≤ (n * p.prob a) * (-1 / 10) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg _) (p.nonneg a))
    _ = _ := by ring

/-- The chance of seeing at most half the expected count decays exponentially in
the expected count. -/
theorem count_half_lower {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) :
    eventMass (independentSampleLaw fun _ : Fin n => p)
      (fun shots => ((List.ofFn shots).count a : ℝ) ≤ n * p.prob a / 2) ≤
        Real.exp (-(3 / 20 : ℝ) * n * p.prob a) := by
  refine (count_lower_exp p a n _ (Real.log 2) (Real.log_nonneg (by norm_num))).trans
    (Real.exp_le_exp.mpr ?_)
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = (n * p.prob a) * (Real.log 2 / 2 - 1 / 2) := by ring
    _ ≤ (n * p.prob a) * (-(3 / 20)) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.log_two_lt_d9])
        (mul_nonneg (Nat.cast_nonneg _) (p.nonneg a))
    _ = _ := by ring

/-- If the reference frequency lies within the relative-error range, a positive
coordinate gives a large zero-flag probability and a negative coordinate gives a small one. -/
private theorem zero_flag_weight_bounds (value weight : ℝ) (hWeight : 0 ≤ weight)
    (hLower : value ^ 2 / 2 ≤ weight) (hUpper : weight ≤ 3 * value ^ 2 / 2) :
    (0 < value → (81 / 100 : ℝ) * weight ≤ ((value + Real.sqrt weight) / 2) ^ 2) ∧
      (value < 0 → ((value + Real.sqrt weight) / 2) ^ 2 ≤ weight / 16) := by
  let root := Real.sqrt weight
  have hRoot : 0 ≤ root := Real.sqrt_nonneg _
  have hSquare : root ^ 2 = weight := Real.sq_sqrt hWeight
  constructor
  · intro hPos
    have hCompare : (4 / 5 : ℝ) * root ≤ value := by
      apply (sq_le_sq₀ (mul_nonneg (by norm_num) hRoot) hPos.le).mp
      rw [mul_pow, hSquare]
      nlinarith
    have hAmp : (9 / 10 : ℝ) * root ≤ (value + root) / 2 := by linarith
    have h := (sq_le_sq₀ (show 0 ≤ (9 / 10 : ℝ) * root by positivity)
      ((show 0 ≤ (9 / 10 : ℝ) * root by positivity).trans hAmp)).mpr hAmp
    rw [mul_pow, hSquare] at h
    norm_num at h
    exact h
  · intro hNeg
    have hu : -value ≤ (3 / 2 : ℝ) * root := by
      apply (sq_le_sq₀ (neg_nonneg.mpr hNeg.le) (mul_nonneg (by norm_num) hRoot)).mp
      rw [neg_sq, mul_pow, hSquare]
      nlinarith
    have hl : (1 / 2 : ℝ) * root ≤ -value := by
      apply (sq_le_sq₀ (mul_nonneg (by norm_num) hRoot) (neg_nonneg.mpr hNeg.le)).mp
      rw [mul_pow, hSquare, neg_sq]
      nlinarith
    have hAbs : |(value + root) / 2| ≤ root / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h := (sq_le_sq₀ (abs_nonneg _) (div_nonneg hRoot (by norm_num))).mpr hAbs
    rw [sq_abs, div_pow root, hSquare] at h
    norm_num at h
    exact h

/-- Conditional on a basis record in the relative-error range, the ancilla-zero
threshold misclassifies a nonzero coordinate with probability at most
`exp (-shots * frequency / 8)`. -/
theorem conditional_sign_error_probability (state : Address depth → ℝ)
    (hState : ∑ i, state i ^ 2 = 1) (basis : List (Address depth)) (hBasis : basis ≠ [])
    (address : Address depth) (shots : ℕ)
    (hNonzero : state address ≠ 0)
    (hLower : state address ^ 2 / 2 ≤ frequency basis address)
    (hUpper : frequency basis address ≤ 3 * state address ^ 2 / 2) :
    let law := independentSampleLaw (fun _ : Fin shots => interferenceSampleLaw state hState basis hBasis)
    let threshold := (2 / 5 : ℝ) * shots * frequency basis address
    eventMass law (fun record =>
        if 0 < state address then ((List.ofFn record).count (false, address) : ℝ) ≤ threshold
        else threshold < ((List.ofFn record).count (false, address) : ℝ)) ≤
      Real.exp (-(shots : ℝ) * frequency basis address / 8) := by
  let p := interferenceSampleLaw state hState basis hBasis
  let weight := frequency basis address
  let threshold := (2 / 5 : ℝ) * shots * weight
  let label := (false, address)
  let rate := Real.exp (-(shots : ℝ) * weight / 8)
  have hWeight : 0 ≤ weight := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hThreshold : 0 ≤ threshold :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hWeight
  have hProb : p.prob label = ((state address + Real.sqrt weight) / 2) ^ 2 := by
    simp [p, label, interferenceSampleLaw, interferenceAmplitude, positiveAmplitude,
      reference_amplitude_eq_sqrt_frequency basis hBasis, weight]
  have hBounds := zero_flag_weight_bounds (state address) weight hWeight hLower hUpper
  have hLog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  change eventMass (independentSampleLaw (fun _ : Fin shots => p)) (fun record =>
    if 0 < state address then ((List.ofFn record).count label : ℝ) ≤ threshold
    else threshold < ((List.ofFn record).count label : ℝ)) ≤ rate
  by_cases hPos : 0 < state address
  · simp_rw [ite_eq_left hPos]
    refine (count_lower_exp p label shots threshold (Real.log 2) hLog).trans
      (Real.exp_le_exp.mpr ?_)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hExp : Real.log 2 * threshold ≤ (7 / 10 : ℝ) * threshold :=
      mul_le_mul_of_nonneg_right (by linarith [Real.log_two_lt_d9]) hThreshold
    have hMass := mul_le_mul_of_nonneg_left (hBounds.1 hPos) (Nat.cast_nonneg shots : (0 : ℝ) ≤ shots)
    rw [← hProb] at hMass
    change Real.log 2 * threshold + shots * (p.prob label * ((2 : ℝ)⁻¹ - 1)) ≤ -(shots : ℝ) * weight / 8
    dsimp only [threshold] at hExp ⊢
    nlinarith only [hExp, hMass]
  · have hNeg := lt_of_le_of_ne (le_of_not_gt hPos) hNonzero
    simp_rw [ite_eq_right hPos]
    refine (eventMass_mono _ _ (fun record => threshold ≤ ((List.ofFn record).count label : ℝ))
      (fun _ h => h.le)).trans ((count_upper_exp p label shots threshold (Real.log 2) hLog).trans
      (Real.exp_le_exp.mpr ?_))
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hExp : (2 / 3 : ℝ) * threshold ≤ Real.log 2 * threshold :=
      mul_le_mul_of_nonneg_right (by linarith [Real.log_two_gt_d9]) hThreshold
    have hMass := mul_le_mul_of_nonneg_left (hBounds.2 hNeg) (Nat.cast_nonneg shots : (0 : ℝ) ≤ shots)
    rw [← hProb] at hMass
    have hWeightShots : 0 ≤ (shots : ℝ) * weight := mul_nonneg (Nat.cast_nonneg _) hWeight
    change -(Real.log 2 * threshold) + shots * (p.prob label * (2 - 1)) ≤ -(shots : ℝ) * weight / 8
    dsimp only [threshold] at hExp ⊢
    nlinarith only [hExp, hMass, hWeightShots]

end Qatlib.Concepts.QRAM.SignedReadout
