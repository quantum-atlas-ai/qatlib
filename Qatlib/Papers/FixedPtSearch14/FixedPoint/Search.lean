/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.SearchDefs

/-!
# Search and amplitude-estimation resource bounds

This module proves circuit expansions, interruption accounting, and relative
amplitude-estimation bounds used alongside the fixed-point-search development
[YoderLowChuang2014]. It also records exact endpoint behavior, truncation estimates for finite
distributions, and compatibility of oracle-access models.

The final lemmas establish strict-order properties of `BitRowLt` and the resource ledger for
`linearScanMinimum`.

## Main statements

* `ae_receipt_transport`: Prefix execution, residual code, and conserved query counts.
* `relative_ae_same_record_native`: Relative error for finite-precision decoding of the same
  measured record.
* `variance_truncation_tail`: A probability bound for truncation error.
* `linear_scan_ledger`: Exact loads, comparisons, and bit cost of the scan ledger.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix
open scoped BigOperators Classical

variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] in

/-- Expanding one phase-threshold block yields `aeRoundSteps M k`. -/
theorem expand_phaseThresholdBlock (M k : ℕ) :
    (phaseThresholdBlock (I := I) M k).flatMap expandAEAccess = aeRoundSteps M k := by
  simp [phaseThresholdBlock, expandAEAccess, aeRoundSteps]

omit [Fintype I] in

/-- Expanding an `n`-round phase-threshold loop yields the concatenation of its indexed round
steps. -/
theorem phaseThresholdLoop_rounds (M n : ℕ) :
    (phaseThresholdLoop (I := I) M n).flatMap expandAEAccess
      = (List.range n).flatMap (aeRoundSteps M) := by
  induction n with
  | zero => simp [phaseThresholdLoop, List.range_zero]
  | succ n ih =>
    rw [phaseThresholdLoop, List.flatMap_append, ih, List.range_succ,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      expand_phaseThresholdBlock]
    simp

omit [Fintype I] in

/-- The amplitude-estimation access word consists of initialization, a Fourier gate, `M - 1`
rounds, and the inverse Fourier gate. -/
theorem aeAccessWord_rounds (M : ℕ) :
    aeAccessWord (I := I) M =
      .initialize ::
        ([.fixed (TensorGate (QFTMatrix M) (1 : Matrix (Bool × I) (Bool × I) ℂ))] ++
          (List.range (M - 1)).flatMap (aeRoundSteps M) ++
          [.fixed (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))]) := by
  rw [aeAccessWord_split, aeFlagAccessWord, phaseThresholdLoop_rounds]

/-- Mapping over a concatenated list equals concatenating the mapped component lists. -/
theorem map_flatMap_comm {α β γ : Type} (f : β → γ) (g : α → List β) (l : List α) :
    (l.flatMap g).map f = l.flatMap (fun x => (g x).map f) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih, List.map_append]

omit [Fintype I] in

/-- The counted amplitude-estimation circuit expands into initialization, Fourier gates, and the
indexed compiled rounds. -/
theorem countedAECircuit_rounds (M : ℕ) (A : Matrix I I ℂ) (j : I) :
    countedAECircuit M A j =
      (aeAccessInstruction M A j) .initialize ::
        ((aeAccessInstruction M A j)
          (.fixed (TensorGate (QFTMatrix M) (1 : Matrix (Bool × I) (Bool × I) ℂ))) ::
          (((List.range (M - 1)).flatMap (fun k => compiledRound M A j k)) ++
            [(aeAccessInstruction M A j)
              (.fixed (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ)))])) := by
  rw [countedAECircuit, aeAccessWord_rounds]
  simp only [List.map_cons, List.map_append]
  rw [map_flatMap_comm]
  simp [compiledRound]

omit [Fintype I] in

/-- A compiled round consists of two threshold flips surrounding one query and the controlled
backward preparation, source reflection, and forward preparation. -/
theorem compiledRound_eq (M : ℕ) (A : Matrix I I ℂ) (j : I) (k : ℕ) :
    compiledRound M A j k =
      [.gate (permMatrix (phaseThresholdFlip M k)), .query,
        .gate (aeControlledGate M Aᴴ),
        .gate (aeControlledGate M (ReflectionAbout (outerProduct (Ket j)))),
        .gate (aeControlledGate M A),
        .gate (permMatrix (phaseThresholdFlip M k))] := by
  rfl

omit [Fintype I] in

/-- Each compiled round contains exactly one query and has length `aeRoundLength`. -/
theorem compiledRound_single_query (M : ℕ) (A : Matrix I I ℂ) (j : I) (k : ℕ) :
    QueryCount (compiledRound M A j k) = 1 ∧
    (compiledRound M A j k).length = aeRoundLength := by
  rw [compiledRound_eq]
  simp [aeRoundLength]

omit [Fintype I] [DecidableEq I] in

/-- The query counts of a circuit prefix and its complementary suffix add to the total query
count. -/
theorem queryCount_take_add_drop (C : Circuit I) (k : ℕ) :
    QueryCount (C.take k) + QueryCount (C.drop k) = QueryCount C := by
  induction C generalizing k with
  | nil => simp
  | cons s C ih =>
    cases s with
    | gate U =>
      cases k with
      | zero => simp
      | succ k =>
        simp only [List.take_succ_cons, List.drop_succ_cons, queryCount_gate]
        rw [ih k]
    | query =>
      cases k with
      | zero => simp
      | succ k =>
        simp only [List.take_succ_cons, List.drop_succ_cons, queryCount_query]
        have h := ih k
        omega

/-- After `k` microsteps of the counted circuit, the residual word is its dropped suffix, memory
is the executed-prefix state, and the two query counts sum to `M - 1`. -/
theorem ae_receipt_transport (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (O : Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ)
    (cfg : InterruptConfig (Fin M × (Bool × I)) ℕ)
    (hcfg : cfg.word = countedAECircuit M A j) (k : ℕ) :
    (microAfter O k cfg).word = (countedAECircuit M A j).drop k ∧
    (microAfter O k cfg).mem = Run O ((countedAECircuit M A j).take k) cfg.mem ∧
    QueryCount ((countedAECircuit M A j).take k) +
        QueryCount ((countedAECircuit M A j).drop k) = M - 1 := by
  have hm := microAfter_spec O k cfg
  have hledger := (prepared_ae_access_ledger M (by omega) A j).1
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, hcfg]
  · rw [hm, hcfg]
  · rw [queryCount_take_add_drop, hledger]

/-- Subtracting the executed-prefix query count from `M - 1` gives the query count of the
remaining suffix. -/
theorem ae_receipt_remaining_calls (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (C : Circuit (Fin M × (Bool × I))) (k : ℕ) (hC : C = countedAECircuit M A j) :
    (M - 1) - QueryCount (C.take k) = QueryCount (C.drop k) := by
  have hledger := (prepared_ae_access_ledger M (by omega) A j).1
  have hpart : QueryCount (C.take k) + QueryCount (C.drop k) = M - 1 := by
    rw [hC, queryCount_take_add_drop, hledger]
  omega

/-- No fixed finite circuit can have event probability at least `2/3` at zero rotation and at
most `1/3` at every rotation in `(0, 1]`. -/
theorem unknown_amplitude_zero_decision_impossible
    (C : Circuit (Fin 2)) (ψ : QState (Fin 2)) (S : Finset (Fin 2))
    (hzero : 2/3 ≤ MeasureProb (Run (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation 0) C ψ) S)
    (hpositive : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      MeasureProb (Run (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation θ) C ψ) S ≤ 1/3) : False :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.fixed_budget_zero_test_impossible C ψ S hzero hpositive

/-- For any fixed positive grid parameter, the relative sampling-error expression exceeds any
positive bound at some promise in `(0, 1]`. -/
theorem relative_ae_budget_diverges (M : ℝ) (hM : 0 < M) (R : ℝ) (hR : 0 < R) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ ≤ 1 ∧ R < relativeAESamplingError M a₀ := by
  have hden : 0 < 2 * R * M ^ 2 := by positivity
  have hsq : 0 < M ^ 2 := sq_pos_of_pos hM
  refine ⟨min 1 (Real.pi ^ 2 / (2 * R * M ^ 2)), lt_min (by positivity) (by positivity),
    min_le_left _ _, ?_⟩
  have hmin : min 1 (Real.pi ^ 2 / (2 * R * M ^ 2)) ≤ Real.pi ^ 2 / (2 * R * M ^ 2) :=
    min_le_right _ _
  have hmul : min 1 (Real.pi ^ 2 / (2 * R * M ^ 2)) * (2 * R * M ^ 2) ≤ Real.pi ^ 2 := by
    rw [le_div_iff₀ hden] at hmin
    linarith
  have hkey : 2 * R ≤ Real.pi ^ 2 / (min 1 (Real.pi ^ 2 / (2 * R * M ^ 2)) * M ^ 2) := by
    have hden2 : 0 < min 1 (Real.pi ^ 2 / (2 * R * M ^ 2)) * M ^ 2 := by
      positivity
    rw [le_div_iff₀ hden2]
    nlinarith [hmul]
  have ha₀ : 0 < min 1 (Real.pi ^ 2 / (2 * R * M ^ 2)) := lt_min (by positivity) (by positivity)
  have hfrac : 0 ≤ (1 - min 1 (Real.pi ^ 2 / (2 * R * M ^ 2))) / min 1 (Real.pi ^ 2 / (2 * R * M ^ 2)) :=
    div_nonneg (sub_nonneg.mpr (min_le_left _ _)) (le_of_lt ha₀)
  have hterm : 0 ≤ 2 * Real.pi * Real.sqrt ((1 - min 1 (Real.pi ^ 2 / (2 * R * M ^ 2))) /
      min 1 (Real.pi ^ 2 / (2 * R * M ^ 2))) / M := by
    have hsqrt := Real.sqrt_nonneg
      ((1 - min 1 (Real.pi ^ 2 / (2 * R * M ^ 2))) /
        min 1 (Real.pi ^ 2 / (2 * R * M ^ 2)))
    positivity
  unfold relativeAESamplingError
  linarith

/-- Under a positive lower bound `a₀ ≤ a` and positive grid parameter, the BHMT absolute-error
window is bounded by `a` times the relative sampling-error expression. -/
theorem bhmt_window_le_relative (a a₀ M : ℝ) (ha0 : 0 < a₀)
    (ha : a₀ ≤ a) (hM : 0 < M) :
    2 * Real.pi * Real.sqrt (a * (1 - a)) / M + Real.pi ^ 2 / M ^ 2
      ≤ a * relativeAESamplingError M a₀ := by
  have ha_pos : 0 < a := lt_of_lt_of_le ha0 ha
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have h1 : a₀ * (1 - a) ≤ a * (1 - a₀) := by linarith
  have hmul : a * (a₀ * (1 - a)) ≤ a * (a * (1 - a₀)) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt ha_pos)
  have hsq : a * (1 - a) ≤ a ^ 2 * ((1 - a₀) / a₀) := by
    rw [← mul_div_assoc, le_div_iff₀ ha0]
    nlinarith [hmul]
  have hsqrt : Real.sqrt (a * (1 - a)) ≤ a * Real.sqrt ((1 - a₀) / a₀) := by
    have hroot := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_nonneg ha_nonneg] at hroot
    exact hroot
  have hA : 2 * Real.pi * Real.sqrt (a * (1 - a))
      ≤ 2 * Real.pi * (a * Real.sqrt ((1 - a₀) / a₀)) :=
    mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hB : (2 * Real.pi * Real.sqrt (a * (1 - a))) / M
      ≤ (2 * Real.pi * (a * Real.sqrt ((1 - a₀) / a₀))) / M :=
    div_le_div_of_nonneg_right hA (le_of_lt hM)
  have hC : (2 * Real.pi * Real.sqrt (a * (1 - a))) / M
      ≤ a * (2 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / M) := by
    have hB' : (2 * Real.pi * (a * Real.sqrt ((1 - a₀) / a₀))) / M
        = a * (2 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / M) := by ring
    rw [← hB']
    exact hB
  have hpos2 : 0 < a₀ * M ^ 2 := by positivity
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hD : Real.pi ^ 2 / M ^ 2 ≤ a * (Real.pi ^ 2 / (a₀ * M ^ 2)) := by
    rw [← mul_div_assoc, le_div_iff₀ hpos2]
    have hneM : M ^ 2 ≠ 0 := by positivity
    field_simp
    have hthat : a₀ * Real.pi ^ 2 ≤ a * Real.pi ^ 2 :=
      mul_le_mul_of_nonneg_right ha (le_of_lt hpi)
    nlinarith [hthat]
  unfold relativeAESamplingError
  linarith [hC, hD]

/-- The relative sampling-error expression is nonnegative for a positive grid parameter and a
promise in `(0, 1]`. -/
theorem relativeAESamplingError_nonneg (M a₀ : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hM : 0 < M) : 0 ≤ relativeAESamplingError M a₀ := by
  have hfrac : 0 ≤ (1 - a₀) / a₀ := div_nonneg (sub_nonneg.mpr ha₀1) (le_of_lt ha₀)
  have hsqrt0 : 0 ≤ Real.sqrt ((1 - a₀) / a₀) := Real.sqrt_nonneg _
  have h1 : 0 ≤ 2 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / M := by positivity
  have h2 : 0 ≤ Real.pi ^ 2 / (a₀ * M ^ 2) := by positivity
  unfold relativeAESamplingError
  linarith

/-- The relative error including finite decoding precision is nonnegative for a positive grid
parameter and a promise in `(0, 1]`. -/
theorem relativeAEError_nonneg (M : ℝ) (k : ℕ) (a₀ : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hM : 0 < M) : 0 ≤ relativeAEError M k a₀ := by
  have hs := relativeAESamplingError_nonneg M a₀ ha₀ ha₀1 hM
  have h3 : 0 ≤ ((2 : ℝ)⁻¹) ^ k / a₀ := by positivity
  unfold relativeAEError
  linarith

/-- If the marked mass is at least `a₀ > 0`, the ideal estimate has relative error at most
`relativeAESamplingError M a₀` with probability at least `8 / π²`; this error bound is
nonnegative. -/
theorem relative_ae_relative_error (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) (a₀ : ℝ) (ha₀ : 0 < a₀)
    (ha₀1 : a₀ ≤ 1) :
    let a := unknownAmplitude A j S
    a₀ ≤ a →
    (0 ≤ relativeAESamplingError (M : ℝ) a₀ ∧
      (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |aeEstimate M z - a| ≤ a * relativeAESamplingError (M : ℝ) a₀),
      (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2) := by
  (try dsimp only)
  let a := unknownAmplitude A j S
  have hgeom := prepared_aa_good_bad_geometry A j S hA
  have ha0 : 0 ≤ a := hgeom.2.2.2.2.1
  have ha1 : a ≤ 1 := hgeom.2.2.2.2.2
  intro ha
  have hkey : 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2
      ≤ a * relativeAESamplingError (M : ℝ) a₀ :=
    bhmt_window_le_relative a a₀ (M : ℝ) ha₀ ha
      (by exact_mod_cast (show (0 : ℕ) < M by omega))
  have hsub : (Finset.univ.filter (fun z : Fin M =>
        |aeEstimate M z - a| ≤
          2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2))
      ⊆ (Finset.univ.filter (fun z : Fin M =>
        |aeEstimate M z - a| ≤ a * relativeAESamplingError (M : ℝ) a₀)) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact le_trans (Finset.mem_filter.mp hz).2 hkey
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => (aeLaw M A j S hA hM).nonneg z)
  refine ⟨relativeAESamplingError_nonneg (M : ℝ) a₀ ha₀ ha₀1
    (by exact_mod_cast (show (0 : ℕ) < M by omega)), ?_⟩
  exact (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).1.trans hmass

/-- If the marked mass is at least `a₀ > 0`, native decoding has relative error at most
`relativeAEError M k a₀` with probability at least `8 / π²`; this error bound is
nonnegative. -/
theorem relative_ae_same_record_native (M k : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) (a₀ : ℝ) (ha₀ : 0 < a₀)
    (ha₀1 : a₀ ≤ 1) :
    let a := unknownAmplitude A j S
    a₀ ≤ a →
    (0 ≤ relativeAEError (M : ℝ) k a₀ ∧
      (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |(nativeAEDecode M k z : ℝ) - a| ≤ a * relativeAEError (M : ℝ) k a₀),
      (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2) := by
  (try dsimp only)
  let a := unknownAmplitude A j S
  have hgeom := prepared_aa_good_bad_geometry A j S hA
  have ha1 : a ≤ 1 := hgeom.2.2.2.2.2
  intro ha
  have hkey : 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2
        + ((2 : ℝ)⁻¹) ^ k
      ≤ a * relativeAEError (M : ℝ) k a₀ := by
    have hs := bhmt_window_le_relative a a₀ (M : ℝ) ha₀ ha
      (by exact_mod_cast (show (0 : ℕ) < M by omega))
    have hnum : ((2 : ℝ)⁻¹) ^ k ≤ a * (((2 : ℝ)⁻¹) ^ k / a₀) := by
      have ha0pos : 0 < a₀ := ha₀
      have h1 : 1 ≤ a / a₀ := (le_div_iff₀ ha0pos).2 (by linarith)
      have h2 : (1 : ℝ) * ((2 : ℝ)⁻¹) ^ k ≤ (a / a₀) * ((2 : ℝ)⁻¹) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : (1 : ℝ) * ((2 : ℝ)⁻¹) ^ k = ((2 : ℝ)⁻¹) ^ k := by ring
      have h4 : (a / a₀) * ((2 : ℝ)⁻¹) ^ k = a * (((2 : ℝ)⁻¹) ^ k / a₀) := by
        rw [div_mul_eq_mul_div, ← mul_div_assoc]
      linarith
    have hsplit : a * relativeAESamplingError (M : ℝ) a₀ + a * (((2 : ℝ)⁻¹) ^ k / a₀)
        = a * relativeAEError (M : ℝ) k a₀ := by
      unfold relativeAEError
      ring
    linarith [hs, hnum, hsplit]
  have hsub : (Finset.univ.filter (fun z : Fin M =>
        |(nativeAEDecode M k z : ℝ) - a| ≤
          2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2
            + ((2 : ℝ)⁻¹) ^ k))
      ⊆ (Finset.univ.filter (fun z : Fin M =>
        |(nativeAEDecode M k z : ℝ) - a| ≤ a * relativeAEError (M : ℝ) k a₀)) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact le_trans (Finset.mem_filter.mp hz).2 hkey
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => (aeLaw M A j S hA hM).nonneg z)
  refine ⟨relativeAEError_nonneg (M : ℝ) k a₀ ha₀ ha₀1
    (by exact_mod_cast (show (0 : ℕ) < M by omega)), ?_⟩
  exact (native_ae_same_record_bhmt_success I M k hM A j S hA).trans hmass

/-- At zero marked mass, the zero record has probability one and decodes ideally to zero. -/
theorem relative_ae_zero_endpoint (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : unknownAmplitude A j S = 0) :
    (aeLaw M A j S hA hM).prob ⟨0, by omega⟩ = 1 ∧
    aeEstimate M ⟨0, by omega⟩ = 0 := by
  have h := (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).2.1 ha
  refine ⟨h, ?_⟩
  simp [aeEstimate]

/-- At unit marked mass and even grid size, the total probability of records whose ideal
estimate is one equals one. -/
theorem relative_ae_unit_endpoint (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : unknownAmplitude A j S = 1) (hdiv : 2 ∣ M) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M => aeEstimate M z = 1),
      (aeLaw M A j S hA hM).prob z = 1 :=
  (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).2.2 ha hdiv

/-- Every ideal amplitude estimate lies in the unit interval. -/
theorem relative_ae_finite_budget_output (M : ℕ) (z : Fin M) :
    0 ≤ aeEstimate M z ∧ aeEstimate M z ≤ 1 := by
  rw [aeEstimate]
  have hsq : 0 ≤ (Real.sin (Real.pi * (z.val : ℝ) / (M : ℝ))) ^ 2 := sq_nonneg _
  have habs : |Real.sin (Real.pi * (z.val : ℝ) / (M : ℝ))| ≤ 1 := Real.abs_sin_le_one _
  have hle := abs_le.mp habs
  have hprod : 0 ≤ (1 - Real.sin (Real.pi * (z.val : ℝ) / (M : ℝ))) *
      (1 + Real.sin (Real.pi * (z.val : ℝ) / (M : ℝ))) :=
    mul_nonneg (sub_nonneg.mpr hle.2) (by linarith)
  constructor
  · exact hsq
  · nlinarith [hprod]

/-- For `M ≥ 2`, the counted amplitude-estimation circuit uses exactly `M - 1` queries. -/
theorem relative_ae_query_cost (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) :
    QueryCount (countedAECircuit M A j) = M - 1 :=
  (prepared_ae_access_ledger M (by omega) A j).1

omit [Fintype I] [DecidableEq I] in

/-- The phase-mark and bit-kickback access models do not match. -/
theorem relative_ae_lower_bound_model :
    matchedModel AccessModel.phaseMark AccessModel.bitKickback = False := by
  rfl

/-- A bound `V` on the second moment about `c` bounds the absolute truncation bias by `(V +
(p.expect f - c)^2) / (4 * τ)` for `τ > 0`. -/
theorem variance_truncation_bias (p : FinDist I) (f : I → ℝ) (c τ : ℝ)
    (hτ : 0 < τ) (V : ℝ) (hV : (∑ i, p.prob i * (f i - c)^2) ≤ V) :
    |p.expect f - p.expect (fun i => c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))|
      ≤ (V + (p.expect f - c)^2) / (4 * τ) := by
  have hpoint (i : I) : |f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))|
      ≤ (f i - c)^2 / (4 * τ) := by
    have h := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip_error τ (f i - c) hτ
    have hrw : f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))
        = (f i - c) - Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c) := by ring
    rw [hrw]
    exact h
  have hsum : |∑ i, p.prob i * (f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c)))|
      ≤ ∑ i, p.prob i * |f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))| := by
    calc |∑ i, p.prob i * (f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c)))|
        = |∑ i, (p.prob i * (f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))))| := rfl
      _ ≤ ∑ i, |(p.prob i * (f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, p.prob i * |f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_of_nonneg (p.nonneg i)]
  calc
    |p.expect f - p.expect (fun i => c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))|
        = |∑ i, p.prob i * (f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c)))| := by
          rw [FinDist.expect, FinDist.expect]
          congr 1
          have hlin := @Finset.sum_sub_distrib I ℝ (Finset.univ : Finset I) _
            (fun i => p.prob i * f i) (fun i => p.prob i * (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c)))
          have hlin' : (∑ i, p.prob i * f i) - (∑ i, p.prob i * (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c)))
              = ∑ i, p.prob i * (f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))) := by
            have h1 := hlin
            rw [← h1]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [hlin']
      _ ≤ ∑ i, p.prob i * |f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))| := hsum
      _ ≤ ∑ i, p.prob i * ((f i - c)^2 / (4 * τ)) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hpoint i) (p.nonneg i)
      _ = (∑ i, p.prob i * (f i - c)^2) / (4 * τ) := by
          symm
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_div_assoc]
      _ ≤ (V + (p.expect f - c)^2) / (4 * τ) := by
          have hshift := SignedMean.shifted_second_moment p f c
          have hnum : (∑ i, p.prob i * (f i - c)^2) ≤ V + (p.expect f - c)^2 := by
            linarith [hV, hshift, sq_nonneg (p.expect f - c)]
          exact div_le_div_of_nonneg_right hnum (by positivity)

/-- For positive `τ`, the payoff clipped about `c` lies between `c - τ` and `c + τ`. -/
theorem truncated_payoff_bounded (f : I → ℝ) (c τ : ℝ) (hτ : 0 < τ) (i : I) :
    c - τ ≤ c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c) ∧
    c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c) ≤ c + τ := by
  have hb :=
      (abs_le.mp (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip_bound τ (f i - c) hτ.le))
  constructor
  · linarith
  · linarith

/-- For a nonnegative function on a finite distribution and `t > 0`, the mass where the function
exceeds `t` is at most its expectation divided by `t`. -/
theorem finDist_markov (p : FinDist I) (g : I → ℝ) (hg : ∀ i, 0 ≤ g i)
    (t : ℝ) (ht : 0 < t) :
    (∑ i with t < g i, p.prob i) ≤ (∑ i, p.prob i * g i) / t := by
  have hpoint : ∀ i ∈ Finset.filter (fun i : I => t < g i) Finset.univ,
      p.prob i * t ≤ p.prob i * g i := by
    intro i hi
    have hgt : t < g i := (Finset.mem_filter.mp hi).2
    have hmul : p.prob i * (g i - t) ≥ 0 :=
      mul_nonneg (p.nonneg i) (by linarith)
    have hpt : p.prob i * t ≤ p.prob i * g i := by nlinarith
    nlinarith
  have hsum : (∑ i with t < g i, p.prob i) * t ≤ ∑ i, p.prob i * g i := by
    calc (∑ i with t < g i, p.prob i) * t = ∑ i with t < g i, (p.prob i * t) := by
            rw [Finset.sum_mul]
          _ ≤ ∑ i with t < g i, (p.prob i * g i) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hpoint i hi
          _ ≤ ∑ i, p.prob i * g i := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun i hi => (Finset.mem_filter.mp hi).1)
              (fun i _ _ => mul_nonneg (p.nonneg i) (hg i))
  rw [le_div_iff₀ ht]
  linarith

/-- A second-moment bound `V` about `c` bounds the mass of truncation errors exceeding `ε > 0`
by `V / (4 * τ * ε)`. -/
theorem variance_truncation_tail (p : FinDist I) (f : I → ℝ) (c τ ε : ℝ)
    (hτ : 0 < τ) (hε : 0 < ε) (V : ℝ) (hV : (∑ i, p.prob i * (f i - c)^2) ≤ V) :
    (∑ i with ε < |f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))|, p.prob i)
      ≤ V / (4 * τ * ε) := by
  have hpoint (i : I) : |f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))|
      ≤ (f i - c)^2 / (4 * τ) := by
    have h := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip_error τ (f i - c) hτ
    have hrw : f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))
        = (f i - c) - Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c) := by ring
    rw [hrw]
    exact h
  have hsub : (Finset.filter (fun i : I => ε < |f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))|)
        Finset.univ)
      ⊆ (Finset.filter (fun i : I => 4 * τ * ε < (f i - c)^2) Finset.univ) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hle := hpoint i
    have hlt : ε < |f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))| :=
      (Finset.mem_filter.mp hi).2
    have hpos : 0 < 4 * τ := by positivity
    have : ε < (f i - c)^2 / (4 * τ) := lt_of_lt_of_le hlt hle
    have : ε * (4 * τ) < (f i - c)^2 := (lt_div_iff₀ hpos).mp this
    linarith
  have hcheb : (∑ i with 4 * τ * ε < (f i - c)^2, p.prob i)
      ≤ (∑ i, p.prob i * (f i - c)^2) / (4 * τ * ε) :=
    finDist_markov p (fun i => (f i - c)^2) (fun i => sq_nonneg _) (4 * τ * ε) (by positivity)
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => p.nonneg i)
  calc
    (∑ i with ε < |f i - (c + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - c))|, p.prob i)
        ≤ (∑ i with 4 * τ * ε < (f i - c)^2, p.prob i) := hmass
    _ ≤ (∑ i, p.prob i * (f i - c)^2) / (4 * τ * ε) := hcheb
    _ ≤ V / (4 * τ * ε) := by
          exact div_le_div_of_nonneg_right hV (by positivity)

/-- The signed-mean joint probability function factors into its source probability and the
positive and negative layer probabilities conditioned on that source. -/
theorem variance_only_layer_records (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (σ : ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (signedMeanLaw k A j f σ hA).prob
      = (signedMeanSource A j hA).prob ∘ Prod.fst *
        (fun ω => (layerLaw k A j (centerPositive f σ ω.1) hA
          (fun _ => le_max_right _ _)).prob ω.2.1) *
        (fun ω => (layerLaw k A j (centerNegative f σ ω.1) hA
          (fun _ => le_max_right _ _)).prob ω.2.2) := by
  funext ω
  rfl

/-- A payoff identically equal to `-1` is everywhere negative while its squared deviation from
zero is one. -/
theorem variance_only_separates_nonnegativity (f : I → ℝ) (hf : ∀ i, f i = -1) :
    (∀ i, ¬ (0 ≤ f i)) ∧ (∀ i, (f i - 0)^2 = 1) := by
  refine ⟨?_, ?_⟩
  · intro i
    simp [hf]
  · intro i
    simp [hf]

/-- For the two-point payoff with positive scale `t`, the mean is `t`, the variance is `t²`, and
the relative-variance contract with parameter one holds. -/
theorem relative_variance_gives_no_absolute_bound (B t : ℝ) (hB : 1 ≤ B)
    (ht : 0 < t) :
    let p : FinDist (Fin 2) := twoPointSource
    let f : Fin 2 → ℝ := twoPointPayoff t
    p.expect f = t ∧ p.variance f = t ^ 2 ∧
      RelativeVarianceContract p f 1 ∧ (∀ V : ℝ, t ^ 2 ≤ V → V ≥ t ^ 2) := by
  have hmean : (twoPointSource : FinDist (Fin 2)).expect (twoPointPayoff t) = t := by
    simp [twoPointSource, twoPointPayoff, FinDist.expect, Fin.sum_univ_two]
  have hvar : (twoPointSource : FinDist (Fin 2)).variance (twoPointPayoff t) = t ^ 2 := by
    rw [FinDist.variance, hmean]
    simp [twoPointSource, twoPointPayoff, FinDist.expect, Fin.sum_univ_two]
    ring
  refine ⟨hmean, hvar, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      simp [twoPointPayoff]
      split <;> linarith
    · rw [hmean]
      exact ht
    · rw [hvar, hmean]
      have h1 : (1 : ℝ) ≤ B := hB
      have hmul : (1 : ℝ) * t ^ 2 ≤ B * t ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
      simpa using! hmul
  · intro V hV
    exact hV

/-- For `M ≥ 2`, the counted circuit has `M - 1` queries and `5 * (M - 1) + 3` gates, and its
amplitude-estimation law has total mass one. -/
theorem ae_program_oblivious (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    QueryCount (countedAECircuit M A j) = M - 1 ∧
    GateCount (countedAECircuit M A j) = 5 * (M - 1) + 3 ∧
    (∑ x, (aeLaw M A j S hA hM).prob x) = 1 := by
  have hledger := prepared_ae_access_ledger M (by omega) A j
  exact ⟨hledger.1, hledger.2.1, (aeLaw M A j S hA hM).sum_one⟩

/-- For positive `M`, the access word has `M` forward preparation accesses and `M - 1` backward
accesses. -/
theorem ae_direction_ledger (M : ℕ) (hM : 0 < M) :
    aeForwardAccesses (aeAccessWord (I := I) M) = M ∧
    aeBackwardAccesses (aeAccessWord (I := I) M) = M - 1 := by
  have hsep := prepared_ae_separate_access_counts (I := I) M hM
  exact ⟨hsep.1, hsep.2.1⟩

/-- For positive `M`, the access word contains `M - 1` source reflections. -/
theorem ae_source_reflection_ledger (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (j : I) :
    aeSourceReflections (aeAccessWord (I := I) M) = M - 1 :=
  (prepared_ae_access_ledger M hM A j).2.2.2

/-- The phase-mark model matches itself and does not match the bit-kickback model. -/
theorem ae_access_model_is_phase :
    matchedModel AccessModel.phaseMark AccessModel.phaseMark ∧
    matchedModel AccessModel.phaseMark AccessModel.bitKickback = False := by
  refine ⟨?_, rfl⟩
  trivial

/-- The amplitude-estimation workspace has dimension `M * (2 * Fintype.card I)`. -/
theorem ae_workspace_dimension (M : ℕ) :
    Fintype.card (Fin M × (Bool × I)) = M * (2 * Fintype.card I) := by
  simp [Fintype.card_prod]

/-- The unified relative error is the sampling error plus the decoding term `2⁻ᵏ / a₀`. -/
theorem ae_unified_error_budget (M : ℝ) (k : ℕ) (a₀ : ℝ) :
    relativeAEError M k a₀ = relativeAESamplingError M a₀ + ((2 : ℝ)⁻¹) ^ k / a₀ := by
  rfl

/-- The list of readouts from `L` layers has length `L`. -/
theorem multi_layer_readout_length (M k L : ℕ) (ω : Fin L → Fin M) :
    (multiLayerReadout M k L ω).length = L := by
  simp [multiLayerReadout]

/-- The `L`-layer readout has length `L` and an assigned total of `L * (M - 1)` oracle calls. -/
theorem multi_layer_readout_cost (M k L : ℕ) (ω : Fin L → Fin M) :
    multiLayerOracleCalls L M = L * (M - 1) ∧
    (multiLayerReadout M k L ω).length = L := by
  exact ⟨rfl, multi_layer_readout_length M k L ω⟩

/-- Each access model matches itself, while phase marking, bit kickback, and adaptive feedback
are pairwise incompatible. -/
theorem access_model_matching_facts :
    matchedModel AccessModel.phaseMark AccessModel.phaseMark ∧
    matchedModel AccessModel.bitKickback AccessModel.bitKickback ∧
    matchedModel AccessModel.adaptiveFeedback AccessModel.adaptiveFeedback ∧
    matchedModel AccessModel.phaseMark AccessModel.bitKickback = False ∧
    matchedModel AccessModel.phaseMark AccessModel.adaptiveFeedback = False ∧
    matchedModel AccessModel.bitKickback AccessModel.adaptiveFeedback = False := by
  refine ⟨trivial, trivial, trivial, rfl, rfl, rfl⟩

/-- For at least two data bits, the workspace Grover circuit uses at most `π * √N / 4` queries,
where `N` is the data-register cardinality, within the bit-kickback model. -/
theorem frozen_search_bounds_are_in_the_bit_model
    {W : Type} [Fintype W] [DecidableEq W] (n : ℕ) (w : W) (x : Reg n) (hn : 2 ≤ n) :
    (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ)
        ≤ Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 ∧
    matchedModel AccessModel.bitKickback AccessModel.bitKickback := by
  have h := (workspace_singleton_search_actual_upper (W := W) n w x hn).2.1
  exact ⟨h, trivial⟩

/-- The strict lexicographic relation `BitRowLt` is irreflexive. -/
theorem BitRowLt_irrefl (a : List Bool) : ¬ BitRowLt a a := by
  induction a with
  | nil => simp [BitRowLt]
  | cons x xs ih =>
    cases x <;> simp [BitRowLt, ih]

/-- If `BitRowLt a b`, then `BitRowLt b a` does not hold. -/
theorem BitRowLt_asymm (a b : List Bool) (h : BitRowLt a b) : ¬ BitRowLt b a := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp_all [BitRowLt]
    | cons y ys => simp [BitRowLt]
  | cons x xs ih =>
    cases b with
    | nil => simp_all [BitRowLt]
    | cons y ys =>
      match x, y with
      | true, true => exact ih ys h
      | false, false => exact ih ys h
      | true, false => simp_all [BitRowLt]
      | false, true => simp [BitRowLt]

/-- The strict lexicographic relation `BitRowLt` is transitive. -/
theorem BitRowLt_trans (a b c : List Bool) (h₁ : BitRowLt a b) (h₂ : BitRowLt b c) :
    BitRowLt a c := by
  induction a generalizing b c with
  | nil =>
    cases c with
    | nil => cases b <;> simp_all [BitRowLt]
    | cons y ys => simp [BitRowLt]
  | cons x xs ih =>
    cases b with
    | nil => simp_all [BitRowLt]
    | cons y ys =>
      cases c with
      | nil => simp_all [BitRowLt]
      | cons z zs =>
        match x, y, z with
        | true, true, true => exact ih ys zs h₁ h₂
        | false, false, false => exact ih ys zs h₁ h₂
        | false, true, true => exact trivial
        | false, false, true => exact trivial
        | true, true, false => simp_all [BitRowLt]
        | true, false, true => simp_all [BitRowLt]
        | true, false, false => simp_all [BitRowLt]
        | false, true, false => simp_all [BitRowLt]

/-- The scan ledger records one load per row, `rows - 1` comparisons, and bit cost `(2 * rows -
1) * width`. -/
theorem linear_scan_ledger (t : DatabaseTable) :
    (linearScanMinimum t).2.loads = t.rows ∧
    (linearScanMinimum t).2.comparisons = t.rows - 1 ∧
    (linearScanMinimum t).2.bitCost t.width = (2 * t.rows - 1) * t.width := by
  by_cases hr : 0 < t.rows
  · have hlen : (tableRows t).length = t.rows := by
      simp [tableRows, List.length_map, List.length_finRange]
    have hdrop : (List.drop 1 (tableRows t)).length = t.rows - 1 := by
      simp only [List.length_drop, hlen]
    have hcomps : (scanMinRow (List.drop 1 (tableRows t)) (t.entry ⟨0, hr⟩) 0).2 = t.rows - 1 := by
      rw [scanMinRow_comps]
      simp only [Nat.zero_add]
      rw [hdrop]
    simp only [linearScanMinimum, dif_pos hr]
    rw [hcomps]
    simp only [ComparisonLedger.bitCost]
    have hkey : t.rows + (t.rows - 1) = 2 * t.rows - 1 := by omega
    rw [hkey]
    simp
  · have hrows : t.rows = 0 := by omega
    simp only [linearScanMinimum, dif_neg hr]
    simp [hrows, ComparisonLedger.bitCost]

end Qatlib.Papers.FixedPtSearch14.FixedPoint
