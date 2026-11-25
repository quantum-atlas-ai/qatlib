/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Forward.MedianPreparation
public import Qatlib.Papers.QCNN20.Forward.MedianAccuracy
public import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
public import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalHHLNoiseConsumers
public import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoal

@[expose] public section

/-!
# Amplitude amplification of median activation readout

[KerenidisLandmanPrakash2020], Sections D.1.4–D.1.5, amplify the
zero sampling flag before reading the address and its estimated
activation. The preparation and its adjoint are those of the physical
median sampler. Conditioning after any successful number of iterations
leaves every readout event probability unchanged. When the unamplified
probability is known, Grover's round count gives a constant success
probability with the corresponding square-root bound on the rounds. A
mixed depth schedule uses a certified lower bound on the original good
amplitude and preserves the conditional law of the combined experiment.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Forward

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability (measureProb_mono measureProb_smul)
open Qatlib.Foundations.QueryWordCore.Circuit
  (Circuit GateCount IsUnitaryCircuit QueryCount RepeatCircuit Run run_gate run_nil)
open Qatlib.Concepts.LchsSimulation.StaticLchs
  (preparedAACircuit preparedAAState preparedAAWord preparedDataQueries preparedFixedGates preparedInputQueries
    preparedMark prepared_aa_actual_circuit prepared_aa_born_success prepared_aa_reflection_and_access
    prepared_aa_separate_access_word)
open Qatlib.Concepts.HhlAlgorithms.Postselection (depth)
open Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe (amplified_postMeasure_phase mixed_window_avg)
open Qatlib.Concepts.SearchStopping.KnownCount
  (groverIterations groverIterations_le groverIterations_success knownCountAngle knownCountAngle_spec)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid)
open scoped BigOperators Classical

variable {positions window : ℕ} {Filter : Type} [Fintype Filter]

/-- The marked basis states have zero sampling flag, with arbitrary estimation history. -/
def convolutionMedianGood (C : Type) [Fintype C] (window M r : ℕ) : Finset (MedianReadoutBasis C window M r) :=
  medianReadoutEvent (fun _ _ b => b = false)

/-- The marking reflection is the phase flip on the zero flag alone. -/
theorem convolution_median_mark_apply {C : Type} [Fintype C] [DecidableEq C] (window M r : ℕ)
    (ψ : QState (MedianReadoutBasis C window M r)) (p : MedianReadoutBasis C window M r) :
    ApplyGate (preparedMark (convolutionMedianGood C window M r)) ψ p =
      if p.1.2 = false then -ψ p else ψ p := by
  let good := convolutionMedianGood C window M r
  change ((1 - (2 : ℂ) • Projector good) *ᵥ ψ) p = _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  change ψ p - (2 : ℂ) * Collapse ψ good p = _
  have hmem : p ∈ good ↔ p.1.2 = false := by simp [good, convolutionMedianGood, medianReadoutEvent]
  rw [collapse_apply]
  by_cases h : p.1.2 = false
  · simp only [hmem, h, ite_true]
    ring
  · simp [hmem, h]

/-- Prepare the median sampler and apply the requested number of amplification rounds. -/
def convolutionMedianAmplificationCircuit [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (a : Address positions × Filter) (k : ℕ) : Circuit (MedianReadoutBasis (Address positions × Filter) window M r) :=
  preparedAACircuit (convolutionMedianPreparation memory filters cap M hM r addressPreparation)
    (convolutionMedianSeed a window M hM r) k

/-- Execute the amplification circuit with the actual zero-flag marking reflection. -/
def convolutionMedianAmplifiedOutput [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (a : Address positions × Filter) (k : ℕ) : QState (MedianReadoutBasis (Address positions × Filter) window M r) :=
  Run (preparedMark (convolutionMedianGood (Address positions × Filter) window M r))
    (convolutionMedianAmplificationCircuit memory filters cap M hM r addressPreparation a k)
    (Ket (convolutionMedianSeed a window M hM r))

/-- Without any amplification rounds the executed circuit is exactly the original sampler. -/
theorem convolution_median_amplified_zero [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (a : Address positions × Filter) :
    convolutionMedianAmplifiedOutput memory filters cap M hM r addressPreparation a 0 =
      convolutionMedianReadout memory filters cap M hM r (ApplyGate addressPreparation (Ket a)) := by
  simpa only [convolutionMedianAmplifiedOutput, convolutionMedianAmplificationCircuit, preparedAACircuit,
    RepeatCircuit, List.append_nil, run_gate, run_nil] using
    convolution_median_preparation_apply memory filters cap M hM r addressPreparation a

/-- The unamplified zero-flag mass is the total median activation weight divided by the cap. -/
theorem convolution_median_readout_success_probability
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (ψ : QState (Address positions × Filter)) :
    MeasureProb (convolutionMedianReadout memory filters cap M (by omega) r ψ)
      (convolutionMedianGood (Address positions × Filter) window M r) =
      convolutionMedianActivationMass memory filters cap M (by omega) r ψ (fun _ _ => True) / cap := by
  unfold convolutionMedianGood
  rw [convolution_median_readout_event memory filters hMemory hFilters cap M hM r ψ (fun _ _ b => b = false)]
  simpa only [and_true] using convolution_median_flag_probability memory filters cap hCap M (by omega) r ψ
    (fun _ _ => True)

set_option maxHeartbeats 1500000 in
/-- The circuit is unitary with a unitary mark. The separated word uses one mark,
two preparation accesses and one fixed reflection per round, after one initial preparation. -/
theorem convolution_median_amplification_access [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (hAddress : addressPreparation ∈ Matrix.unitaryGroup (Address positions × Filter) ℂ)
    (a : Address positions × Filter) (k : ℕ) :
    let circuit := convolutionMedianAmplificationCircuit memory filters cap M (by omega) r addressPreparation a k
    let word := preparedAAWord (convolutionMedianSeed a window M (by omega) r) k
    IsUnitaryCircuit circuit ∧ QueryCount circuit = k ∧ GateCount circuit = 3 * k + 1 ∧
      preparedDataQueries word = k ∧ preparedInputQueries word = 2 * k + 1 ∧ preparedFixedGates word = k ∧
      Normalized (convolutionMedianAmplifiedOutput memory filters cap M (by omega) r addressPreparation a k) := by
  intro circuit word
  let A := convolutionMedianPreparation memory filters cap M (by omega) r addressPreparation
  let seed := convolutionMedianSeed a window M (by omega) r
  let good := convolutionMedianGood (Address positions × Filter) window M r
  have hA := convolution_median_preparation_unitary memory filters hMemory hFilters cap hCap M hM r
    addressPreparation hAddress
  obtain ⟨hCircuit, hQueries, hGates, _⟩ := prepared_aa_actual_circuit A seed good k hA
  obtain ⟨_, hMark, hPrep, hFixed, _, _⟩ := prepared_aa_separate_access_word A seed good k hA
  have hOracle := (prepared_aa_reflection_and_access A seed good hA).1
  exact ⟨hCircuit, hQueries, hGates, hMark, hPrep, hFixed, hCircuit.normalized_run hOracle (normalized_ket seed)⟩

set_option maxHeartbeats 1500000 in
/-- At any successful amplification depth all conditional event probabilities equal those
of the original sampler. -/
theorem convolution_median_amplification_preserves_readout [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (hAddress : addressPreparation ∈ Matrix.unitaryGroup (Address positions × Filter) ℂ)
    (a : Address positions × Filter) (k : ℕ)
    (event : Finset (MedianReadoutBasis (Address positions × Filter) window M r)) :
    let out := convolutionMedianAmplifiedOutput memory filters cap M (by omega) r addressPreparation a k
    let good := convolutionMedianGood (Address positions × Filter) window M r
    0 < MeasureProb out good → MeasureProb (PostMeasure out good) event =
      MeasureProb (PostMeasure
        (convolutionMedianReadout memory filters cap M (by omega) r (ApplyGate addressPreparation (Ket a))) good) event := by
  intro out good hPositive
  let A := convolutionMedianPreparation memory filters cap M (by omega) r addressPreparation
  let seed := convolutionMedianSeed a window M (by omega) r
  have hA := convolution_median_preparation_unitary memory filters hMemory hFilters cap hCap M hM r
    addressPreparation hAddress
  obtain ⟨z, hNorm, hPhase⟩ := amplified_postMeasure_phase A seed good k hA hPositive
  have hPrepared : preparedAAState A seed =
      convolutionMedianReadout memory filters cap M (by omega) r (ApplyGate addressPreparation (Ket a)) :=
    convolution_median_preparation_apply memory filters cap M (by omega) r addressPreparation a
  change PostMeasure out good = z • PostMeasure (preparedAAState A seed) good at hPhase
  rw [hPhase, measureProb_smul, hNorm, one_pow, one_mul, hPrepared]

/-- Use no rounds when the original success is already at least a half, and the usual
known-probability Grover count otherwise. -/
def medianAmplificationRounds (p : ℝ) : ℕ :=
  if 1 / 2 ≤ p then 0 else groverIterations (knownCountAngle p)

/-- The known-probability count reaches success at least a half using at most
π divided by four times the original good amplitude. -/
private theorem median_amplification_rounds_bound {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (seed : I) (good : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (p : ℝ) (hp : 0 < p) (hMass : MeasureProb (preparedAAState A seed) good = p) :
    let k := medianAmplificationRounds p
    1 / 2 ≤ MeasureProb (Run (preparedMark good) (preparedAACircuit A seed k) (Ket seed)) good ∧
      (k : ℝ) ≤ Real.pi / (4 * Real.sqrt p) := by
  dsimp only
  by_cases hHalf : 1 / 2 ≤ p
  · rw [medianAmplificationRounds, ite_eq_left hHalf]
    refine ⟨?_, ?_⟩
    · change (1 / 2 : ℝ) ≤ MeasureProb (preparedAAState A seed) good
      rwa [hMass]
    · rw [Nat.cast_zero]
      exact div_nonneg Real.pi_pos.le (by positivity)
  · rw [medianAmplificationRounds, ite_eq_right hHalf]
    have hpOne : p < 1 := by linarith [lt_of_not_ge hHalf]
    obtain ⟨hAngle, hAngleTop, hSin, hSinSq, _⟩ := knownCountAngle_spec hp hpOne
    rw [prepared_aa_born_success A seed good (knownCountAngle p) _ hA hAngle hAngleTop (hMass.trans hSinSq.symm)]
    refine ⟨?_, ?_⟩
    · have hSuccess := groverIterations_success hAngle hAngleTop.le
      rw [hSinSq] at hSuccess
      exact (show 1 / 2 ≤ 1 - p by linarith [lt_of_not_ge hHalf]).trans hSuccess
    · rw [← hSin]
      exact groverIterations_le hAngle (by rw [hSin]; exact Real.sqrt_pos.mpr hp)

set_option maxHeartbeats 1500000 in
/-- Given positive total median activation and its exact value for choosing the round count,
the actual amplified circuit succeeds with probability at least a half and samples the
same address and median label law. -/
theorem convolution_median_known_amplification [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (hAddress : addressPreparation ∈ Matrix.unitaryGroup (Address positions × Filter) ℂ)
    (a : Address positions × Filter) (event : (Address positions × Filter) → Fin M → Prop)
    (hMass : 0 < convolutionMedianActivationMass memory filters cap M (by omega) r
      (ApplyGate addressPreparation (Ket a)) (fun _ _ => True)) :
    let ψ := ApplyGate addressPreparation (Ket a)
    let total := convolutionMedianActivationMass memory filters cap M (by omega) r ψ (fun _ _ => True)
    let p := total / cap
    let k := medianAmplificationRounds p
    let good := convolutionMedianGood (Address positions × Filter) window M r
    let out := convolutionMedianAmplifiedOutput memory filters cap M (by omega) r addressPreparation a k
    1 / 2 ≤ MeasureProb out good ∧ (k : ℝ) ≤ Real.pi / (4 * Real.sqrt p) ∧
      MeasureProb (PostMeasure out good) (Finset.univ.filter fun b => event b.1.1.1 b.1.1.2) =
        convolutionMedianActivationMass memory filters cap M (by omega) r ψ event / total := by
  intro ψ total p k good out
  let A := convolutionMedianPreparation memory filters cap M (by omega) r addressPreparation
  let seed := convolutionMedianSeed a window M (by omega) r
  have hA := convolution_median_preparation_unitary memory filters hMemory hFilters cap hCap M hM r
    addressPreparation hAddress
  have hPrepared : preparedAAState A seed = convolutionMedianReadout memory filters cap M (by omega) r ψ :=
    convolution_median_preparation_apply memory filters cap M (by omega) r addressPreparation a
  have hInitial : MeasureProb (preparedAAState A seed) good = p := by
    rw [hPrepared]
    exact convolution_median_readout_success_probability memory filters hMemory hFilters cap hCap M hM r ψ
  obtain ⟨hSuccess, hRounds⟩ := median_amplification_rounds_bound A seed good hA p (div_pos hMass hCap) hInitial
  have hPositive : 0 < MeasureProb out good := lt_of_lt_of_le (by norm_num) hSuccess
  refine ⟨hSuccess, hRounds, ?_⟩
  have hPreserved := convolution_median_amplification_preserves_readout memory filters hMemory hFilters cap hCap M hM r
    addressPreparation hAddress a k (Finset.univ.filter fun b => event b.1.1.1 b.1.1.2) hPositive
  exact hPreserved.trans (convolution_median_readout_postselect memory filters hMemory hFilters cap hCap M hM r
    ψ event hMass).2

/-- The ideal total minus its median error gives a certified probability lower bound for the
unamplified sampler when this difference is positive. -/
theorem convolution_median_success_lower
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (ψ : QState (Address positions × Filter)) (hψ : Normalized ψ)
    (hSignal : convolutionMedianMassError memory filters cap M r ψ <
      convolutionIdealActivationMass memory filters cap ψ (fun _ => True)) :
    let ideal := convolutionIdealActivationMass memory filters cap ψ (fun _ => True)
    let ε := convolutionMedianMassError memory filters cap M r ψ
    0 < (ideal - ε) / cap ∧ (ideal - ε) / cap ≤
      MeasureProb (convolutionMedianReadout memory filters cap M (by omega) r ψ)
        (convolutionMedianGood (Address positions × Filter) window M r) := by
  intro ideal ε
  let total := convolutionMedianActivationMass memory filters cap M (by omega) r ψ (fun _ _ => True)
  have hError : |total - ideal| ≤ ε :=
    convolution_median_mass_error memory filters hMemory hFilters cap hCap.le M hM r ψ hψ (fun _ => True)
  change ε < ideal at hSignal
  refine ⟨div_pos (sub_pos.mpr hSignal) hCap, ?_⟩
  rw [convolution_median_readout_success_probability memory filters hMemory hFilters cap hCap M hM r ψ]
  exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp hError).1]) hCap.le

/-- Mixing several runs with the same conditional law preserves that law. Runs of zero
success contribute zero to both masses. -/
private theorem conditioned_mixture_event {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]
    (state : K → QState I) (reference : QState I) (good event : Finset I)
    (hTotal : 0 < ∑ k, MeasureProb (state k) good)
    (hLaw : ∀ k, 0 < MeasureProb (state k) good →
      MeasureProb (PostMeasure (state k) good) event = MeasureProb (PostMeasure reference good) event) :
    (∑ k, MeasureProb (state k) (good ∩ event)) / (∑ k, MeasureProb (state k) good) =
      MeasureProb (PostMeasure reference good) event := by
  let q := MeasureProb (PostMeasure reference good) event
  have hFactor (k : K) : MeasureProb (state k) (good ∩ event) = q * MeasureProb (state k) good := by
    by_cases hk : 0 < MeasureProb (state k) good
    · have h := hLaw k hk
      rw [measureProb_postMeasure hk] at h
      exact (div_eq_iff hk.ne').mp h
    · have hZero : MeasureProb (state k) good = 0 :=
        le_antisymm (le_of_not_gt hk) (measureProb_nonneg _ _)
      rw [hZero, mul_zero]
      refine le_antisymm ?_ (measureProb_nonneg _ _)
      exact (measureProb_mono (state k) Finset.inter_subset_left).trans_eq hZero
  simp_rw [hFactor]
  rw [← Finset.mul_sum, mul_div_cancel_right₀ _ hTotal.ne']

set_option maxHeartbeats 1500000 in
/-- Uniformly sampling the mixed window gives at least one-eighth success without knowing
the exact probability. The conditional law of the successful mixture equals the original
sampler's law, and every selected depth is below the window size. -/
theorem convolution_median_mixed_amplification [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (hAddress : addressPreparation ∈ Matrix.unitaryGroup (Address positions × Filter) ℂ)
    (a : Address positions × Filter) (m : ℕ) (hm : 0 < m) (lowerAmplitude : ℝ) (hLowerPos : 0 < lowerAmplitude)
    (hWindow : 1 ≤ (m : ℝ) * lowerAmplitude)
    (event : Finset (MedianReadoutBasis (Address positions × Filter) window M r)) :
    let base := convolutionMedianReadout memory filters cap M (by omega) r (ApplyGate addressPreparation (Ket a))
    let good := convolutionMedianGood (Address positions × Filter) window M r
    let out := fun s : Fin (2 * m) =>
      convolutionMedianAmplifiedOutput memory filters cap M (by omega) r addressPreparation a (depth m s)
    lowerAmplitude ^ 2 ≤ MeasureProb base good →
      (1 / 8 : ℝ) ≤ (∑ s, MeasureProb (out s) good) / (2 * m : ℝ) ∧
      (∀ s : Fin (2 * m), depth m s < m) ∧
      (∑ s, MeasureProb (out s) (good ∩ event)) / (∑ s, MeasureProb (out s) good) =
        MeasureProb (PostMeasure base good) event := by
  intro base good out hLower
  let A := convolutionMedianPreparation memory filters cap M (by omega) r addressPreparation
  let seed := convolutionMedianSeed a window M (by omega) r
  have hA := convolution_median_preparation_unitary memory filters hMemory hFilters cap hCap M hM r
    addressPreparation hAddress
  have hPrepared : preparedAAState A seed = base :=
    convolution_median_preparation_apply memory filters cap M (by omega) r addressPreparation a
  have hSuccess : (1 / 8 : ℝ) ≤ (∑ s, MeasureProb (out s) good) / (2 * m : ℝ) :=
    mixed_window_avg A seed good m lowerAmplitude hA hm hLowerPos (by rw [hPrepared]; exact hLower) hWindow
  have hmReal : (0 : ℝ) < 2 * m := by positivity
  have hTotal : 0 < ∑ s, MeasureProb (out s) good :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 8) hmReal).trans_le ((le_div_iff₀ hmReal).mp hSuccess)
  refine ⟨hSuccess, ?_, conditioned_mixture_event out base good event hTotal ?_⟩
  · intro s
    unfold depth
    split_ifs <;> omega
  · intro s hs
    exact convolution_median_amplification_preserves_readout memory filters hMemory hFilters cap hCap M hM r
      addressPreparation hAddress a (depth m s) event hs

/-- The smallest integer window covering the reciprocal square root of the success bound. -/
def medianAmplificationWindow (lowerProbability : ℝ) : ℕ := ⌈1 / Real.sqrt lowerProbability⌉₊

/-- The chosen window supports the mixed schedule and costs at most one rounding step. -/
private theorem median_amplification_window_bounds (lowerProbability : ℝ) (h : 0 < lowerProbability) :
    let m := medianAmplificationWindow lowerProbability
    0 < m ∧ 1 ≤ (m : ℝ) * Real.sqrt lowerProbability ∧ (m : ℝ) < 1 / Real.sqrt lowerProbability + 1 := by
  intro m
  have hAmp := Real.sqrt_pos.mpr h
  have hInv : 0 < 1 / Real.sqrt lowerProbability := div_pos one_pos hAmp
  exact ⟨Nat.ceil_pos.mpr hInv, (div_le_iff₀ hAmp).mp (Nat.le_ceil _), Nat.ceil_lt_add_one hInv.le⟩

set_option maxHeartbeats 1800000 in
/-- Choose the mixed window from the certified activation signal. Every run has bounded
amplification depth, the average success is at least one eighth, and the sampled address law
retains the median sampler's error bound relative to the ideal activations. -/
theorem convolution_median_certified_mixed_amplification [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (addressPreparation : Matrix (Address positions × Filter) (Address positions × Filter) ℂ)
    (hAddress : addressPreparation ∈ Matrix.unitaryGroup (Address positions × Filter) ℂ)
    (a : Address positions × Filter) (event : (Address positions × Filter) → Prop)
    (hSignal : convolutionMedianMassError memory filters cap M r (ApplyGate addressPreparation (Ket a)) <
      convolutionIdealActivationMass memory filters cap (ApplyGate addressPreparation (Ket a)) (fun _ => True)) :
    let ψ := ApplyGate addressPreparation (Ket a)
    let ideal := convolutionIdealActivationMass memory filters cap ψ (fun _ => True)
    let ε := convolutionMedianMassError memory filters cap M r ψ
    let lower := (ideal - ε) / cap
    let m := medianAmplificationWindow lower
    let good := convolutionMedianGood (Address positions × Filter) window M r
    let kept : Finset (MedianReadoutBasis (Address positions × Filter) window M r) :=
      Finset.univ.filter fun p => event p.1.1.1
    let out := fun s : Fin (2 * m) =>
      convolutionMedianAmplifiedOutput memory filters cap M (by omega) r addressPreparation a (depth m s)
    (1 / 8 : ℝ) ≤ (∑ s, MeasureProb (out s) good) / (2 * m : ℝ) ∧
      (∀ s : Fin (2 * m), depth m s < m) ∧ (m : ℝ) < 1 / Real.sqrt lower + 1 ∧
      |(∑ s, MeasureProb (out s) (good ∩ kept)) / (∑ s, MeasureProb (out s) good) -
        convolutionIdealActivationMass memory filters cap ψ event / ideal| ≤ 2 * ε / ideal := by
  intro ψ ideal ε lower m good kept out
  have hψ : Normalized ψ := normalized_applyGate hAddress (normalized_ket a)
  obtain ⟨hLower, hBound⟩ := convolution_median_success_lower memory filters hMemory hFilters cap hCap M hM r ψ hψ hSignal
  obtain ⟨hm, hWindow, hRoundBound⟩ := median_amplification_window_bounds lower hLower
  have hSqrt : (Real.sqrt lower) ^ 2 ≤
      MeasureProb (convolutionMedianReadout memory filters cap M (by omega) r ψ) good := by
    rw [Real.sq_sqrt hLower.le]
    exact hBound
  obtain ⟨hSuccess, hDepth, hLaw⟩ := convolution_median_mixed_amplification memory filters hMemory hFilters
    cap hCap M hM r addressPreparation hAddress a m hm (Real.sqrt lower) (Real.sqrt_pos.mpr hLower) hWindow kept hSqrt
  refine ⟨hSuccess, hDepth, hRoundBound, ?_⟩
  rw [hLaw]
  exact (convolution_median_readout_accuracy memory filters hMemory hFilters cap hCap M hM r ψ hψ event hSignal).2

end Qatlib.Papers.QCNN20.Forward
