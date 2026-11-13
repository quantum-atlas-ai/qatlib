/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenCascade
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StructuralEstimateCompilationAux

/-!
# Probability and amplification bounds for record-driven cascades

This module proves legality and probability normalization for the record-driven construction,
together with a good-record mass bound of `9 / 10`. It also supplies relative estimation bounds,
bounded first-crossing arguments, and output-state properties used to establish the
variable-time algorithm associated with [Ambainis2012].

## Main statements

* `recordDrivenLaw_probability`: normalization and nonnegativity of the record law.
* `recordDriven_sharp_good_mass`: the good-record mass lower bound.
* `recordDriven_prefix_crossing`: bounded minimal threshold crossing.
* `recordDriven_good_ray`: preservation of the final good-state direction.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix
open scoped Classical BigOperators
variable {C : Type} [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in

/-- Cascade words agree when their schedules agree on all indices below the prefix length. -/
theorem cascadeWord_congr (s t : ℕ → ℕ) (i : ℕ)
    (h : ∀ j, j < i → s j = t j) : cascadeWord s i = cascadeWord t i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [cascadeWord, cascadeWord, ih (fun j hj => h j (by omega)), h i (by omega)]

omit [Fintype C] [DecidableEq C] in

/-- The input word at record position `i` depends only on record entries at positions strictly
below `i`. -/
theorem recordDrivenInputWord_prefix (m : ℕ) (i : Fin (m+1))
    (ω ω' : RecordDrivenRecord m) (h : ∀ j, j.val < i.val → ω j = ω' j) :
    recordDrivenInputWord m ω i = recordDrivenInputWord m ω' i := by
  have hc (k : ℕ) (hk : k ≤ i.val) :
      cascadeWord (recordDrivenSchedule m ω) k = cascadeWord (recordDrivenSchedule m ω') k := by
    apply cascadeWord_congr
    intro j hj
    have hm : j < m := by omega
    simp only [recordDrivenSchedule, dif_pos hm]
    rw [h ⟨j, by omega⟩ (by change j < i.val; omega)]
  unfold recordDrivenInputWord
  split_ifs
  · rw [hc i.val le_rfl]
  · rw [hc m (by omega)]

omit [DecidableEq C] in

/-- Good amplification preserves legality of a data word. -/
theorem goodAAWord_legal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (word : List DataVtStep) (hw : DataVtWordLegal stages word) (k : ℕ) :
    DataVtWordLegal stages (goodAAWord word k) := by
  have hr : DataVtWordLegal stages (goodAARound word) := by
    intro s hs
    simp only [goodAARound, List.mem_append, List.mem_singleton] at hs
    rcases hs with ((rfl | hi) | rfl) | hf
    · trivial
    · exact dataVtWordInverse_legal stages word hw s hi
    · trivial
    · exact hw s hf
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact hw s hs
  · obtain ⟨w, hw', hs⟩ := List.mem_flatten.mp hs
    have he : w = goodAARound word := (List.mem_replicate.mp hw').2
    exact hr s (he ▸ hs)

omit [DecidableEq C] in

/-- All record-driven estimation input words and the output word are legal data words. -/
theorem recordDriven_words_legal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (ω : RecordDrivenRecord stages.length) :
    (∀ i, DataVtWordLegal stages (recordDrivenInputWord stages.length ω i)) ∧
      DataVtWordLegal stages (recordDrivenOutputWord stages.length ω) := by
  constructor
  · intro i
    unfold recordDrivenInputWord
    split_ifs with hi
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact cascadeWord_legal stages _ i.val (by omega) s hs
      · obtain rfl := List.mem_singleton.mp hs
        exact hi
    · exact cascadeWord_legal stages _ stages.length le_rfl
  · apply goodAAWord_legal
    exact cascadeWord_legal stages _ stages.length le_rfl

/-- For a legal growing pipeline, the record-driven law sums to one and is nonnegative at every
record. -/
theorem recordDrivenLaw_probability
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history) :
    (∑ ω, recordDrivenLaw stages history j₀ ω = 1) ∧
      (∀ ω, 0 ≤ recordDrivenLaw stages history j₀ ω) := by
  constructor
  · apply dataRecordLaw_sum_one _ _ _ _ stages history j₀ hl
    · intro ω i; exact (recordDriven_words_legal stages ω).1 i
    · exact recordDrivenInputWord_prefix stages.length
  · intro ω
    exact dataRecordLaw_nonneg _ _ _ _ stages history j₀ _ ω

/-- For `m ≥ 1`, the union-bound loss `(m + 1) * (8 / 9) ^ recordDrivenRepetitions m` is at most
`1 / 10`. -/
theorem recordDriven_union_loss (m : ℕ) (hm : 1 ≤ m) :
    ((m+1 : ℕ) : ℝ)*(8/9 : ℝ)^(recordDrivenRepetitions m) ≤ 1/10 := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1/8 by norm_num) (1000*m)
  norm_num at hb
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (9/8 : ℝ)^(1000*m) := pow_pos (by norm_num) _
  have hinv : (8/9 : ℝ)^(1000*m)*(9/8 : ℝ)^(1000*m) = 1 := by
    rw [← mul_pow]; norm_num
  unfold recordDrivenRepetitions
  apply (mul_le_mul_iff_right₀ hp).mp
  have he : (9/8 : ℝ)^(1000*m)*(((m+1 : ℕ) : ℝ)*(8/9 : ℝ)^(1000*m)) = ((m+1 : ℕ) : ℝ) := by
    calc
      _ = ((m+1 : ℕ) : ℝ)*((8/9 : ℝ)^(1000*m)*(9/8 : ℝ)^(1000*m)) := by ring
      _ = _ := by rw [hinv, mul_one]
  rw [he]
  push_cast at hb ⊢
  nlinarith

/-- For a nonempty legal growing pipeline, records satisfying all prescribed estimation error
bounds have total law mass at least `9 / 10`. -/
theorem recordDriven_sharp_good_mass
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history) (hm : 1 ≤ stages.length) :
    9/10 ≤ ∑ ω ∈ dataRecordGood (recordDrivenResolution stages.length)
      (recordDrivenRepetitions stages.length) (stages.length+1) stages history j₀
      (recordDrivenInputWord stages.length), recordDrivenLaw stages history j₀ ω := by
  have hb := dataRecordGood_mass (recordDrivenResolution stages.length)
    (by unfold recordDrivenResolution; omega) (recordDrivenRepetitions stages.length)
    (stages.length+1) stages history j₀ hl (recordDrivenInputWord stages.length)
    (fun ω i => (recordDriven_words_legal stages ω).1 i) (recordDrivenInputWord_prefix stages.length)
  have hsmall := recordDriven_union_loss stages.length hm
  change 1-((stages.length+1 : ℕ) : ℝ)*(8/9 : ℝ)^(recordDrivenRepetitions stages.length) ≤ _ at hb
  change 9/10 ≤ ∑ ω ∈ dataRecordGood (recordDrivenResolution stages.length)
    (recordDrivenRepetitions stages.length) (stages.length+1) stages history j₀
    (recordDrivenInputWord stages.length),
    dataRecordLaw (recordDrivenResolution stages.length) _ (recordDrivenRepetitions stages.length)
      (stages.length+1) stages history j₀ (recordDrivenInputWord stages.length) ω
  linarith

omit [Fintype C] [DecidableEq C] in

/-- If `a ≥ 0`, `M > 0`, and `M * sqrt a ≥ 1000`, the data estimation radius is at most `a /
100`. -/
theorem dataEstimateRadius_relative (a : ℝ) (ha : 0 ≤ a)
    (M : ℕ) (hM : 0 < M) (hres : 1000 ≤ (M : ℝ)*Real.sqrt a) :
    dataEstimateRadius a M ≤ a/100 := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hs := Real.sqrt_nonneg a
  have hsq := Real.sq_sqrt ha
  have hsmall : Real.sqrt (a*(1-a)) ≤ Real.sqrt a :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hmul : 1000*Real.sqrt a ≤ (M : ℝ)*a := by
    have h := mul_le_mul_of_nonneg_right hres hs
    nlinarith [hsq]
  have hsqres : 1000000 ≤ (M : ℝ)^2*a := by
    have h :=
        sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1000) (by positivity : (0 : ℝ) ≤ (M : ℝ)*Real.sqrt a)
    have h' := h.mpr hres
    nlinarith [hsq]
  have hfirst : Real.sqrt (a*(1-a))/(M : ℝ) ≤ a/1000 := by
    apply (div_le_div_iff₀ hm (by norm_num)).mpr
    simpa only [mul_comm] using!
        (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 1000)).trans hmul
  have hsecond : 1/(M : ℝ)^2 ≤ a/1000000 := by
    exact (div_le_div_iff₀ (pow_pos hm 2) (by norm_num)).mpr (by nlinarith)
  have hπ : 2*Real.pi/1000+Real.pi^2/1000000 ≤ 1/100 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  unfold dataEstimateRadius
  calc
    2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2 =
      (2*Real.pi)*(Real.sqrt (a*(1-a))/(M : ℝ))+Real.pi^2*(1/(M : ℝ)^2) := by ring
    _ ≤ (2*Real.pi)*(a/1000)+Real.pi^2*(a/1000000) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by positivity))
        (mul_le_mul_of_nonneg_left hsecond (sq_nonneg _))
    _ = (2*Real.pi/1000+Real.pi^2/1000000)*a := by ring
    _ ≤ a/100 := by simpa only [one_div_mul_eq_div] using! mul_le_mul_of_nonneg_right hπ ha

/-- The matrix of one good-amplification round equals the prepared amplification iterate for the
input-word matrix. -/
theorem goodAARound_matrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep) :
    dataVtWordMatrix stages history j₀ (goodAARound word) =
      preparedAAIterate (dataVtWordMatrix stages history j₀ word) j₀ (goodSet C) := by
  simp only [goodAARound, dataVtWordMatrix_append, dataVtWordMatrix_singleton,
    dataVtWordMatrix_inverse, dataVtStepMatrix, preparedAAIterate]
  noncomm_ring

/-- The matrix of a good-amplified word is the `k`th power of its prepared amplification iterate
times the input-word matrix. -/
theorem goodAAWord_matrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep) (k : ℕ) :
    dataVtWordMatrix stages history j₀ (goodAAWord word k) =
      (preparedAAIterate (dataVtWordMatrix stages history j₀ word) j₀ (goodSet C))^k *
        dataVtWordMatrix stages history j₀ word := by
  have hr (n : ℕ) : dataVtWordMatrix stages history j₀ (List.replicate n (goodAARound word)).flatten =
      (preparedAAIterate (dataVtWordMatrix stages history j₀ word) j₀ (goodSet C))^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, dataVtWordMatrix_append, ih, goodAARound_matrix,
        pow_succ]
  exact (dataVtWordMatrix_append stages history j₀ _ _).trans (congrArg
    (fun A => A*dataVtWordMatrix stages history j₀ word) (hr k))

/-- Good amplification multiplies the input word's charged time by `2 * k + 1`. -/
theorem goodAAWord_time (word : List DataVtStep) (k : ℕ) :
    dataVtWordTime (goodAAWord word k) = (2*k+1)*dataVtWordTime word := by
  have hr : dataVtWordTime (goodAARound word) = 2*dataVtWordTime word := by
    simp only [goodAARound, dataVtWordTime_append, dataVtWordTime_inverse]
    simp only [dataVtWordTime, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      dataVtStepTime]
    omega
  have hf (n : ℕ) : dataVtWordTime (List.replicate n (goodAARound word)).flatten =
      n*dataVtWordTime (goodAARound word) := by
    induction n with
    | zero => simp [dataVtWordTime]
    | succ n ih => simp [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm]
  rw [goodAAWord, dataVtWordTime_append, hf, hr]
  ring

/-- For a legal supported pipeline starting in the running sector, every record-driven output
has good-sector collapse proportional to the original pipeline's final good-sector collapse. -/
theorem recordDriven_good_ray
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history) (hj : j₀.1 = vtRunningFlag)
    (hs : GrowingVtSupported stages history j₀) (ω : RecordDrivenRecord stages.length) :
    ∃ c : ℂ, Collapse (dataVtWordState stages history j₀ (recordDrivenOutputWord stages.length ω))
      (goodSet C) = c • Collapse (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := by
  let word := cascadeWord (recordDrivenSchedule stages.length ω) stages.length
  let A := dataVtWordMatrix stages history j₀ word
  let k := recordDrivenFinalRounds stages.length (ω (Fin.last stages.length))
  have hA : A ∈ Matrix.unitaryGroup (VtSpace C) ℂ :=
    dataVtWordMatrix_unitary stages history j₀ hl word (cascadeWord_legal stages _ _ le_rfl)
  obtain ⟨a, ha⟩ := (cascadePrefixTransport_answer C stages history hl j₀ hj hs
    (recordDrivenSchedule stages.length ω)).2.2
  obtain ⟨c, d, hout⟩ := prepared_aa_orbit_span A j₀ hA (goodSet C) k
  refine ⟨c*a, ?_⟩
  have he : dataVtWordState stages history j₀ (recordDrivenOutputWord stages.length ω) =
      ApplyGate ((preparedAAIterate A j₀ (goodSet C))^k) (preparedAAState A j₀) := by
    simp only [recordDrivenOutputWord, dataVtWordState, goodAAWord_matrix, applyGate_mul]
    rfl
  rw [he, hout]
  have hc : Collapse
      (c • Collapse (preparedAAState A j₀) (goodSet C)+
        d • (preparedAAState A j₀-Collapse (preparedAAState A j₀) (goodSet C))) (goodSet C) =
      c • Collapse (preparedAAState A j₀) (goodSet C) := by
    funext p
    by_cases hp : p ∈ goodSet C <;> simp [collapse_apply, hp]
  rw [hc]
  change c • Collapse (dataVtWordState stages history j₀ word) (goodSet C) = _
  rw [ha, smul_smul]

omit [Fintype C] [DecidableEq C] in

/-- For `m ≥ 1` and `a ≥ 1 / (10^12 * m³)`, the prescribed resolution satisfies `M * sqrt a ≥
1000`. -/
theorem recordDriven_floor_resolution (m : ℕ) (hm : 1 ≤ m) (a : ℝ)
    (ha : 1/(10^12*(m : ℝ)^3) ≤ a) :
    1000 ≤ (recordDrivenResolution m : ℝ)*Real.sqrt a := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hden : (0 : ℝ) < 10^12*(m : ℝ)^3 := by positivity
  have ha0 : 0 ≤ a := (le_of_lt (div_pos (by norm_num) hden)).trans ha
  have haf := (div_le_iff₀ hden).mp ha
  have hM : 1000000000*(m : ℝ)^2 ≤ (recordDrivenResolution m : ℝ) := by
    simp [recordDrivenResolution, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  have hlower : 1000000 ≤ (recordDrivenResolution m : ℝ)^2*a := by
    calc
      (1000000 : ℝ) ≤ 1000000*(m : ℝ) := by nlinarith
      _ ≤ (1000000*(m : ℝ))*(a*(10^12*(m : ℝ)^3)) :=
        le_mul_of_one_le_right (by positivity) haf
      _ = (1000000000*(m : ℝ)^2)^2*a := by ring
      _ ≤ (recordDrivenResolution m : ℝ)^2*a :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hM 2) ha0
  have he : ((recordDrivenResolution m : ℝ)*Real.sqrt a)^2 =
      (recordDrivenResolution m : ℝ)^2*a := by rw [mul_pow, Real.sq_sqrt ha0]
  have hnonneg : 0 ≤ (recordDrivenResolution m : ℝ)*Real.sqrt a := by positivity
  nlinarith

omit [Fintype C] [DecidableEq C] in

/-- For `m ≥ 1` and `a ≥ 1 / (10^12 * m³)`, the prescribed-resolution data estimation radius is
at most `a / 100`. -/
theorem recordDriven_floor_radius (m : ℕ) (hm : 1 ≤ m) (a : ℝ)
    (ha : 1/(10^12*(m : ℝ)^3) ≤ a) :
    dataEstimateRadius a (recordDrivenResolution m) ≤ a/100 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have ha0 : 0 ≤ a := (le_of_lt (by positivity : (0 : ℝ) < 1/(10^12*(m : ℝ)^3))).trans ha
  exact dataEstimateRadius_relative a ha0 (recordDrivenResolution m)
    (by unfold recordDrivenResolution; omega) (recordDriven_floor_resolution m hm a ha)

omit [Fintype C] [DecidableEq C] in

/-- For nonnegative `θ` and `n` with `n * θ ≤ 1`, `sin (n * θ)` is at least `n * (1 - (n * θ)² /
4) * sin θ`. -/
theorem sine_small_window_gain (θ n : ℝ) (hθ : 0 ≤ θ) (hn : 0 ≤ n)
    (hwin : n*θ ≤ 1) :
    n*(1-(n*θ)^2/4)*Real.sin θ ≤ Real.sin (n*θ) := by
  have hx : 0 ≤ n*θ := mul_nonneg hn hθ
  have hcoef : 0 ≤ 1-(n*θ)^2/4 := by nlinarith
  have hlower : n*θ-(n*θ)^3/4 ≤ Real.sin (n*θ) := by
    by_cases hz : n*θ = 0
    · simp [hz]
    · have hpos : 0 < n * θ := lt_of_le_of_ne hx (Ne.symm hz)
      linarith [Real.sin_gt_sub_cube hpos, pow_nonneg hpos.le 3]
  calc
    _ ≤ n*(1-(n*θ)^2/4)*θ :=
      mul_le_mul_of_nonneg_left (Real.sin_le hθ) (mul_nonneg hn hcoef)
    _ = n*θ-(n*θ)^3/4 := by ring
    _ ≤ _ := hlower

omit [Fintype C] [DecidableEq C] in

/-- For `0 ≤ θ ≤ π`, nonnegative `n`, and `n * θ ≤ 1`, the squared small-window sine gain
satisfies the stated lower bound. -/
theorem sine_small_window_gain_sq (θ n : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ Real.pi)
    (hn : 0 ≤ n) (hwin : n*θ ≤ 1) :
    n^2*(1-(n*θ)^2/4)^2*(Real.sin θ)^2 ≤ (Real.sin (n*θ))^2 := by
  have hc : 0 ≤ 1-(n*θ)^2/4 := by nlinarith [mul_nonneg hn hθ]
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ hθ1
  have h := pow_le_pow_left₀ (mul_nonneg (mul_nonneg hn hc) hs)
    (sine_small_window_gain θ n hθ hn hwin) 2
  convert! h using 1; ring

omit [Fintype C] [DecidableEq C] in

/-- If a decidable predicate holds at some index at most `N`, searching `List.range (N + 1)`
returns its least satisfying index, which is at most `N`. -/
theorem bounded_first_crossing (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hex : ∃ k, k ≤ N ∧ P k) :
    ∃ k, (List.range (N+1)).find? (fun k => decide (P k)) = some k ∧
      k ≤ N ∧ P k ∧ ∀ j, j < k → ¬P j := by
  cases he : (List.range (N+1)).find? (fun k => decide (P k)) with
  | none =>
    obtain ⟨k, hk, hp⟩ := hex
    have hn := List.find?_eq_none.mp he k (by simp; omega)
    exact False.elim (hn (by simpa using! hp))
  | some k =>
    have hmem := List.mem_of_find?_eq_some he
    have ⟨hP, i, hi, hik, hprev⟩ := List.find?_eq_some_iff_getElem.mp he
    have heq : i = k := by simpa using! hik
    refine ⟨k, rfl, by simpa using! hmem, by simpa using! hP, ?_⟩
    intro j hj
    have h := hprev j (by omega)
    simpa using! h

omit [Fintype C] [DecidableEq C] in

/-- For `m > 16`, a probability above the stated floor and a relative-error estimate yield a
selected prefix count within the cap that is the first to reach estimated gain `1 / (6 *
m)`. -/
theorem recordDriven_prefix_crossing (m : ℕ) (hm : 16 < m) (a : ℝ)
    (labels : RecordDrivenLabels m)
    (ha : 1/(10^12*(m : ℝ)^3) ≤ a)
    (hest : |recordDrivenEstimate m labels-a| ≤ a/100) :
    recordDrivenPrefixRounds m labels ≤ recordDrivenRoundCap m ∧
      1/(6*(m : ℝ)) ≤
        ((2*recordDrivenPrefixRounds m labels+1 : ℕ) : ℝ)^2*recordDrivenEstimate m labels ∧
      ∀ k, k < recordDrivenPrefixRounds m labels →
        ((2*k+1 : ℕ) : ℝ)^2*recordDrivenEstimate m labels < 1/(6*(m : ℝ)) := by
  have hm1 : 1 ≤ m := by omega
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0 : ℝ) < m := by linarith
  have ha0 : 0 ≤ a := (le_of_lt (by positivity : (0 : ℝ) < 1/(10^12*(m : ℝ)^3))).trans ha
  have hr := recordDriven_floor_resolution m hm1 a ha
  have hM : (recordDrivenResolution m : ℝ) ≤ ((2*recordDrivenRoundCap m+1 : ℕ) : ℝ) := by
    exact_mod_cast (show recordDrivenResolution m ≤ 2*recordDrivenRoundCap m+1 by
      have hp : 1 ≤ m^2 := by nlinarith
      unfold recordDrivenResolution recordDrivenRoundCap
      omega)
  have hs := Real.sq_sqrt ha0
  have hres : 1000000 ≤ (recordDrivenResolution m : ℝ)^2*a := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1000) hr 2
    rw [mul_pow, hs] at h
    norm_num at h ⊢
    exact h
  have hcap : 1000000 ≤ ((2*recordDrivenRoundCap m+1 : ℕ) : ℝ)^2*a :=
    hres.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hM 2) ha0)
  have hcal : (99/100 : ℝ)*a ≤ recordDrivenEstimate m labels := by
    have h := (abs_le.mp hest).1
    linarith
  have hval : (990000 : ℝ) ≤ ((2*recordDrivenRoundCap m+1 : ℕ) : ℝ)^2*recordDrivenEstimate m labels := by
    have h := mul_le_mul_of_nonneg_left hcal (sq_nonneg (((2*recordDrivenRoundCap m+1 : ℕ) : ℝ)))
    nlinarith [hcap]
  have hthreshold : 1/(6*(m : ℝ)) ≤ 990000 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  obtain ⟨k, hfind, hk, hp, hmin⟩ := bounded_first_crossing (recordDrivenRoundCap m)
    (fun k => 1/(6*(m : ℝ)) ≤ ((2*k+1 : ℕ) : ℝ)^2*recordDrivenEstimate m labels)
    ⟨recordDrivenRoundCap m, le_rfl, hthreshold.trans hval⟩
  have he : recordDrivenPrefixRounds m labels = k := by
    simp only [recordDrivenPrefixRounds, if_neg (by omega : ¬m ≤ 16), hfind, Option.getD_some]
  rw [he]
  exact ⟨hk, hp, fun j hj => lt_of_not_ge (hmin j hj)⟩

/-- For a legal growing pipeline, every record-driven output state is normalized. -/
theorem recordDriven_output_normalized
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (ω : RecordDrivenRecord stages.length) :
    Normalized (dataVtWordState stages history j₀ (recordDrivenOutputWord stages.length ω)) :=
  normalized_applyGate
    (dataVtWordMatrix_unitary stages history j₀ hl _ (recordDriven_words_legal stages ω).2)
    (normalized_ket j₀)

/-- For a legal growing pipeline, the sum of the output's good and running masses is at most
one. -/
theorem recordDriven_output_flag_mass_le_one
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (ω : RecordDrivenRecord stages.length) :
    MeasureProb (dataVtWordState stages history j₀ (recordDrivenOutputWord stages.length ω))
      (goodSet C) +
    MeasureProb (dataVtWordState stages history j₀ (recordDrivenOutputWord stages.length ω))
      (runningSet C) ≤ 1 := by
  have hdis : Disjoint (goodSet C) (runningSet C) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [goodSet, runningSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have he := hp.symm.trans hq
    exact (by decide : vtGoodFlag ≠ vtRunningFlag) he
  rw [← measureProb_union _ hdis]
  exact measureProb_le_one (recordDriven_output_normalized stages history j₀ hl ω) _

/-- For a legal growing pipeline, an output good mass of at least `2 / 5` implies running mass
at most `3 / 5`. -/
theorem recordDriven_output_running_of_good
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (ω : RecordDrivenRecord stages.length)
    (hgood : 2/5 ≤ MeasureProb
      (dataVtWordState stages history j₀ (recordDrivenOutputWord stages.length ω)) (goodSet C)) :
    MeasureProb (dataVtWordState stages history j₀ (recordDrivenOutputWord stages.length ω))
      (runningSet C) ≤ 3/5 := by
  have hmass := recordDriven_output_flag_mass_le_one stages history j₀ hl ω
  linarith

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
