/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchStoppingDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CountingOracleTransport
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.AQuantumAlgorithmForFindingTheMinimum1999
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.QueryLowerBound
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib
open Qatlib.Concepts.SearchStopping.RestartLaw
open scoped ENNReal BigOperators Classical Topology

private theorem ae_mark_append {R : Type} (l₁ l₂ : List (AEAccessStep R)) :
    aeMarkAccesses (l₁ ++ l₂) = aeMarkAccesses l₁ + aeMarkAccesses l₂ := by
  induction l₁ with
  | nil => simp [aeMarkAccesses]
  | cons a l₁ ih =>
    cases a with
    | mark => simp only [aeMarkAccesses, List.cons_append, ih]; all_goals omega
    | _ => simp only [aeMarkAccesses, List.cons_append, ih]

private theorem ae_source_append {R : Type} (l₁ l₂ : List (AEAccessStep R)) :
    aeSourceOracleAccesses (l₁ ++ l₂) =
      aeSourceOracleAccesses l₁ + aeSourceOracleAccesses l₂ := by
  induction l₁ with
  | nil => simp [aeSourceOracleAccesses]
  | cons a l₁ ih =>
    cases a with
    | mark => simp only [aeSourceOracleAccesses, List.cons_append, ih]; all_goals omega
    | _ => simp only [aeSourceOracleAccesses, List.cons_append, ih]; all_goals omega

private theorem ae_expanded_mark_count {R : Type} (C : Circuit R) :
    aeMarkAccesses (C.flatMap expandAEAccess) = QueryCount C := by
  induction C with
  | nil => simp [aeMarkAccesses, QueryCount]
  | cons s C ih =>
    cases s with
    | gate U =>
      have hflat : (Step.gate U :: C).flatMap expandAEAccess =
          [.fixed U] ++ C.flatMap expandAEAccess := by simp [expandAEAccess]
      rw [hflat, ae_mark_append]
      simp only [aeMarkAccesses, QueryCount]
      omega
    | query =>
      have hflat : (Step.query :: C).flatMap expandAEAccess =
          [.mark, .prepareBackward, .sourceReflection, .prepareForward] ++
            C.flatMap expandAEAccess := by simp [expandAEAccess]
      rw [hflat, ae_mark_append]
      simp only [aeMarkAccesses, QueryCount]
      omega

private theorem ae_expanded_source_count {R : Type} (C : Circuit R) :
    aeSourceOracleAccesses (C.flatMap expandAEAccess) = QueryCount C := by
  induction C with
  | nil => simp [aeSourceOracleAccesses, QueryCount]
  | cons s C ih =>
    cases s with
    | gate U =>
      have hflat : (Step.gate U :: C).flatMap expandAEAccess =
          [.fixed U] ++ C.flatMap expandAEAccess := by simp [expandAEAccess]
      rw [hflat, ae_source_append]
      simp only [aeSourceOracleAccesses, QueryCount]
      omega
    | query =>
      have hflat : (Step.query :: C).flatMap expandAEAccess =
          [.mark, .prepareBackward, .sourceReflection, .prepareForward] ++
            C.flatMap expandAEAccess := by simp [expandAEAccess]
      rw [hflat, ae_source_append]
      simp only [aeSourceOracleAccesses, QueryCount]
      omega

private theorem ae_mark_equals_query_count {I : Type} [Fintype I] [DecidableEq I] (M : ℕ)
    (A : Matrix I I ℂ) (j : I) (w : List (AEAccessStep (Fin M × (Bool × I)))) :
    aeMarkAccesses w = QueryCount (w.map (aeAccessInstruction M A j)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | mark => simp [aeMarkAccesses, aeAccessInstruction, ih]
    | _ => simp [aeMarkAccesses, aeAccessInstruction, ih]

theorem ae_mark_access_count {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) :
    aeMarkAccesses (aeAccessWord (I := I) M) = M - 1 := by
  have hq : QueryCount (countedAECircuit (I := I) M A j) = M - 1 :=
    (prepared_ae_access_ledger (I := I) M hM A j).1
  have h2 : aeMarkAccesses (aeAccessWord (I := I) M)
      = QueryCount ((aeAccessWord (I := I) M).map (aeAccessInstruction M A j)) :=
    ae_mark_equals_query_count M A j _
  have h3 : (aeAccessWord (I := I) M).map (aeAccessInstruction M A j)
      = countedAECircuit (I := I) M A j := rfl
  rw [h2, h3, hq]

private theorem ae_phase_query_count {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) :
    QueryCount (countedPhaseCircuit (I := I) M) = M - 1 := by
  have h := ae_mark_access_count M hM A j
  have hsplit : aeAccessWord (I := I) M =
      .initialize :: (countedPhaseCircuit (I := I) M).flatMap expandAEAccess := rfl
  rw [hsplit] at h
  simp only [aeMarkAccesses] at h
  rw [ae_expanded_mark_count] at h
  exact h

theorem ae_source_evaluation_count {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) :
    aeSourceOracleAccesses (aeAccessWord (I := I) M) = M := by
  have hq := ae_phase_query_count M hM A j
  have hsplit : aeAccessWord (I := I) M =
      .initialize :: (countedPhaseCircuit (I := I) M).flatMap expandAEAccess := rfl
  rw [hsplit]
  simp only [aeSourceOracleAccesses]
  rw [ae_expanded_source_count]
  omega

theorem ae_source_evaluation_transport {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) :
    aeSourceOracleAccesses (aeAccessWord (I := I) M)
      = 1 + QueryCount (countedAECircuit (I := I) M A j) := by
  have hq : QueryCount (countedAECircuit (I := I) M A j) = M - 1 :=
    (prepared_ae_access_ledger (I := I) M hM A j).1
  rw [ae_source_evaluation_count M hM A j]
  omega

theorem clause7_source_cost_convention {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) :
    aeSourceOracleAccesses (aeAccessWord (I := I) M) = M ∧
      aeSourceOracleAccesses (aeAccessWord (I := I) M) =
        1 + QueryCount (countedAECircuit (I := I) M A j) ∧
      aeMarkAccesses (aeAccessWord (I := I) M) = M - 1 := by
  refine ⟨ae_source_evaluation_count M hM A j, ?_, ae_mark_access_count M hM A j⟩
  have hq : QueryCount (countedAECircuit (I := I) M A j) = M - 1 :=
    (prepared_ae_access_ledger (I := I) M hM A j).1
  rw [ae_source_evaluation_count M hM A j]
  omega

private theorem aeWindow_one_at_one {M : ℕ} (z : Fin M) :
    aeWindow M 1 1 z ↔ |aeEstimate M z - 1| ≤ Real.pi ^ 2 / (M : ℝ) ^ 2 := by
  simp [aeWindow]

private theorem odd_mod_two {M : ℕ} (hodd : ¬ 2 ∣ M) : M % 2 = 1 := by
  have hne : M % 2 ≠ 0 := by
    intro hz
    exact hodd (Nat.dvd_iff_mod_eq_zero.mpr hz)
  rcases Nat.mod_two_eq_zero_or_one M with h | h
  · exact absurd h hne
  · exact h

private theorem odd_neighbour_arith {M : ℕ} (hodd : ¬ 2 ∣ M) :
    ((M - 1) / 2 : ℕ) * 2 = M - 1 ∧ ((M + 1) / 2 : ℕ) * 2 = M + 1 ∧
      ((M - 1) / 2 : ℕ) + ((M + 1) / 2 : ℕ) = M := by
  have hmod : M % 2 = 1 := odd_mod_two hodd
  have h1 : 2 * ((M - 1) / 2) + (M - 1) % 2 = M - 1 := Nat.div_add_mod (M - 1) 2
  have h2 : 2 * ((M + 1) / 2) + (M + 1) % 2 = M + 1 := Nat.div_add_mod (M + 1) 2
  have h3 : (M - 1) % 2 = 0 := by omega
  have h4 : (M + 1) % 2 = 0 := by omega
  omega

private theorem odd_neighbour_casts {M : ℕ} (hodd : ¬ 2 ∣ M) :
    ((((M - 1) / 2 : ℕ) : ℝ) * 2 = (M : ℝ) - 1) ∧
    ((((M + 1) / 2 : ℕ) : ℝ) * 2 = (M : ℝ) + 1) := by
  have h := odd_neighbour_arith hodd
  have h1 : ((M - 1) / 2 : ℕ) * 2 = M - 1 := h.1
  have h2 : ((M + 1) / 2 : ℕ) * 2 = M + 1 := h.2.1
  have hc1 : (((M - 1) / 2 : ℕ) : ℝ) * 2 = ((M - 1 : ℕ) : ℝ) := by norm_cast
  have hc2 : (((M + 1) / 2 : ℕ) : ℝ) * 2 = ((M + 1 : ℕ) : ℝ) := by norm_cast
  have hsub : (M - 1 : ℕ) + 1 = M := by omega
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) hsub
    simp only [Nat.cast_add, Nat.cast_one] at hh
    linarith
  constructor
  · rw [hc1, hcast]
  · rw [hc2]
    push_cast
    ring

private theorem odd_neighbour_angle {M : ℕ} (hM : 1 < M) (hodd : ¬ 2 ∣ M) :
    Real.pi * (((M - 1) / 2 : ℕ) : ℝ) / (M : ℝ)
      = Real.pi / 2 - Real.pi / (2 * (M : ℝ)) := by
  have hc := (odd_neighbour_casts hodd).1
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (show 0 < M by omega))
  have hdiv : (((M - 1) / 2 : ℕ) : ℝ) = ((M : ℝ) - 1) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
    linarith [hc]
  rw [hdiv]
  field_simp

private theorem odd_neighbour_angle2 {M : ℕ} (hM : 1 < M) (hodd : ¬ 2 ∣ M) :
    Real.pi * (((M + 1) / 2 : ℕ) : ℝ) / (M : ℝ)
      = Real.pi / 2 + Real.pi / (2 * (M : ℝ)) := by
  have hc := (odd_neighbour_casts hodd).2
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (show 0 < M by omega))
  have hdiv : (((M + 1) / 2 : ℕ) : ℝ) = ((M : ℝ) + 1) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
    linarith [hc]
  rw [hdiv]
  field_simp

theorem odd_neighbour_estimate_value {M : ℕ} (hM : 1 < M) (hodd : ¬ 2 ∣ M) :
    aeEstimate M ⟨(M - 1) / 2, by omega⟩ = Real.cos (Real.pi / (2 * (M : ℝ))) ^ 2 := by
  rw [aeEstimate, odd_neighbour_angle hM hodd, Real.sin_pi_div_two_sub]

theorem odd_neighbour_estimate_value2 {M : ℕ} (hM : 1 < M) (hodd : ¬ 2 ∣ M) :
    aeEstimate M ⟨(M + 1) / 2, by omega⟩ = Real.cos (Real.pi / (2 * (M : ℝ))) ^ 2 := by
  rw [aeEstimate, odd_neighbour_angle2 hM hodd]
  rw [show Real.pi / 2 + Real.pi / (2 * (M : ℝ))
      = Real.pi - (Real.pi / 2 - Real.pi / (2 * (M : ℝ))) by ring,
    Real.sin_pi_sub, Real.sin_pi_div_two_sub]

theorem odd_neighbour_estimates {M : ℕ} (hM : 1 < M) (hodd : ¬ 2 ∣ M) :
    aeEstimate M ⟨(M - 1) / 2, by omega⟩ = aeEstimate M ⟨(M + 1) / 2, by omega⟩ := by
  rw [odd_neighbour_estimate_value hM hodd, odd_neighbour_estimate_value2 hM hodd]

theorem odd_neighbour_window {M : ℕ} (hM : 1 < M) (hodd : ¬ 2 ∣ M) :
    aeWindow M 1 1 ⟨(M - 1) / 2, by omega⟩ ∧
    aeWindow M 1 1 ⟨(M + 1) / 2, by omega⟩ := by
  rw [aeWindow_one_at_one, aeWindow_one_at_one]
  have hx : Real.sin (Real.pi / (2 * (M : ℝ))) ^ 2 ≤ (Real.pi / (2 * (M : ℝ))) ^ 2 := by
    have h1 : |Real.sin (Real.pi / (2 * (M : ℝ)))| ≤ |Real.pi / (2 * (M : ℝ))| := by
      exact Real.abs_sin_le_abs
    have h2 := mul_self_le_mul_self (abs_nonneg _) h1
    nlinarith [sq_abs (Real.sin (Real.pi / (2 * (M : ℝ)))),
      sq_abs (Real.pi / (2 * (M : ℝ)))]
  have hx2 : (Real.pi / (2 * (M : ℝ))) ^ 2 ≤ (Real.pi / (M : ℝ)) ^ 2 := by
    have hid : (Real.pi / (M : ℝ)) ^ 2 = 4 * (Real.pi / (2 * (M : ℝ))) ^ 2 := by
      have hM0' : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (show 0 < M by omega))
      have hq : Real.pi / (2 * (M : ℝ)) = (Real.pi / (M : ℝ)) / 2 := by field_simp
      rw [hq]
      ring
    nlinarith [hid, sq_nonneg (Real.pi / (2 * (M : ℝ)))]
  have hp : Real.sin (Real.pi / (2 * (M : ℝ))) ^ 2 + Real.cos (Real.pi / (2 * (M : ℝ))) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hnonpos : Real.cos (Real.pi / (2 * (M : ℝ))) ^ 2 - 1 ≤ 0 := by nlinarith [hp]
  have hid2 : Real.pi ^ 2 / (M : ℝ) ^ 2 = (Real.pi / (M : ℝ)) ^ 2 := by ring
  constructor
  · rw [odd_neighbour_estimate_value hM hodd, abs_of_nonpos hnonpos]
    nlinarith [hx, hx2, hp, hid2]
  · rw [odd_neighbour_estimate_value2 hM hodd, abs_of_nonpos hnonpos]
    nlinarith [hx, hx2, hp, hid2]

theorem clause7_endpoint {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ)
    (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (∀ k : ℕ, 2 ≤ k →
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        aeWindow M k (MeasureProb (preparedAAState A j) S) z),
        (aeLaw M A j S hA hM).prob z ≥ 1 - 1 / (2 * ((k : ℝ) - 1))) ∧
    (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        aeWindow M 1 (MeasureProb (preparedAAState A j) S) z),
        (aeLaw M A j S hA hM).prob z ≥ 8 / Real.pi ^ 2) ∧
    (MeasureProb (preparedAAState A j) S = 0 →
        (aeLaw M A j S hA hM).prob ⟨0, by omega⟩ = 1) ∧
    (MeasureProb (preparedAAState A j) S = 1 → 2 ∣ M →
      ∑ z ∈ Finset.univ.filter (fun z : Fin M => aeEstimate M z = 1),
        (aeLaw M A j S hA hM).prob z = 1) ∧
    (MeasureProb (preparedAAState A j) S = 1 → ¬ 2 ∣ M →
      aeEstimate M ⟨(M - 1) / 2, by omega⟩ = aeEstimate M ⟨(M + 1) / 2, by omega⟩ ∧
      aeWindow M 1 1 ⟨(M - 1) / 2, by omega⟩ ∧
      aeWindow M 1 1 ⟨(M + 1) / 2, by omega⟩) := by
  classical
  have hM0 : 0 < M := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have h := bhmt_amplitude_estimation_k2_window I M A j S hM hA k hk
    simpa only [aeWindow] using! h
  · have h := (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).1
    have hfilter : Finset.univ.filter (fun z : Fin M =>
          aeWindow M 1 (MeasureProb (preparedAAState A j) S) z)
        = Finset.univ.filter (fun z : Fin M =>
          |aeEstimate M z - MeasureProb (preparedAAState A j) S| ≤
            2 * Real.pi * Real.sqrt (MeasureProb (preparedAAState A j) S *
              (1 - MeasureProb (preparedAAState A j) S)) / (M : ℝ) +
            Real.pi ^ 2 / (M : ℝ) ^ 2) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hz
        simpa [aeWindow] using! hz
      · intro hz
        simpa [aeWindow] using! hz
    rw [hfilter]
    exact h
  · intro ha
    exact (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).2.1 ha
  · intro ha hdiv
    exact (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).2.2 ha hdiv
  · intro ha hodd
    exact ⟨odd_neighbour_estimates (by omega) hodd, (odd_neighbour_window (by omega) hodd).1,
      (odd_neighbour_window (by omega) hodd).2⟩

theorem countGridSize_two_le (N : ℕ) (hN : 2 ≤ N) : 2 ≤ countGridSize N := by
  have hsqrt : (1 : ℝ) < Real.sqrt N := by
    have h1 : Real.sqrt 1 < Real.sqrt N := Real.sqrt_lt_sqrt (by norm_num) (by
      have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      linarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 1)])
    simpa using! h1
  have h2 : 1 < countGridSize N := by
    rw [countGridSize, Nat.lt_ceil]
    simpa using! hsqrt
  omega

theorem countGridSize_one_le (N : ℕ) (hN : 0 < N) : 1 ≤ countGridSize N := by
  have h1 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have h2 : 0 < countGridSize N := by
    rw [countGridSize, Nat.lt_ceil]
    simpa using! h1
  omega

theorem countGridSize_sqrt_le (N : ℕ) (hN : 0 < N) :
    Real.sqrt N ≤ (countGridSize N : ℝ) := by
  have _ := hN
  rw [countGridSize]
  exact Nat.le_ceil _

theorem countGridSize_lt_succ (N : ℕ) (hN : 0 < N) :
    (countGridSize N : ℝ) - 1 < Real.sqrt N := by
  have h1 : countGridSize N - 1 < countGridSize N := by
    have hM1 : 1 ≤ countGridSize N := countGridSize_one_le N hN
    omega
  have h3 : countGridSize N - 1 < Nat.ceil (Real.sqrt N) := by
    rw [countGridSize]
    exact h1
  have h2 : ((countGridSize N - 1 : ℕ) : ℝ) < Real.sqrt N :=
    (Nat.lt_ceil (a := Real.sqrt N) (n := countGridSize N - 1)).mp h3
  have hsub : (countGridSize N - 1 : ℕ) + 1 = countGridSize N := by omega
  have hh := congrArg (fun n : ℕ => (n : ℝ)) hsub
  simp only [Nat.cast_add, Nat.cast_one] at hh
  linarith

theorem countGridSize_sq (N : ℕ) (hN : 0 < N) : (N : ℝ) ≤ (countGridSize N : ℝ) ^ 2 := by
  have h1 : Real.sqrt N ≤ (countGridSize N : ℝ) := countGridSize_sqrt_le N hN
  have h2 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have h3 := mul_self_le_mul_self h2 h1
  nlinarith [h3, Real.sq_sqrt (x := (N : ℝ)) (by positivity)]

theorem countRounded_abs (x : ℝ) (hx : 0 ≤ x) : |countRounded x - x| ≤ 1 / 2 := by
  have h1 : (countRounded x : ℝ) ≤ x + 1 / 2 := by
    simpa [countRounded] using!
      (Nat.floor_le (by linarith [show (0 : ℝ) < 1 / 2 by norm_num] : 0 ≤ x + 1 / 2))
  have h2 : x + 1 / 2 < (countRounded x : ℝ) + 1 := by
    simpa [countRounded] using! (Nat.lt_floor_add_one (x + 1 / 2))
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem pi_sq_add_half_lt_eleven : Real.pi ^ 2 + 1 / 2 < 11 := by
  have h1 : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  nlinarith

theorem count_window_at_scale {N : ℕ} (hN : 0 < N) {M : ℕ}
    (hgrid : Real.sqrt N ≤ (M : ℝ)) (hM2 : (N : ℝ) ≤ (M : ℝ) ^ 2)
    (t : ℕ) (ht0 : 0 ≤ t) (htN : t ≤ N) (z : Fin M) (hz : countWindow N M 1 t z) :
    |(N : ℝ) * aeEstimate M z - (t : ℝ)| ≤
      2 * Real.pi * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ)) / (N : ℝ)) + Real.pi ^ 2 := by
  have hMpos : (0 : ℝ) < M := by
    have : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    linarith
  have hsqrtpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hxt : (0 : ℝ) ≤ Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) :=
    Real.sqrt_nonneg _
  have hdivle : Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (M : ℝ)
      ≤ Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / Real.sqrt N := by
    rw [div_le_div_iff₀ hMpos hsqrtpos]
    nlinarith [hgrid, hxt]
  have hsqrtdiv : Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / Real.sqrt N
      = Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ)) / (N : ℝ)) := by
    have hrad : (0 : ℝ) ≤ (t : ℝ) * ((N : ℝ) - (t : ℝ)) := by
      have h1 : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
      have h2 : (0 : ℝ) ≤ (N : ℝ) - (t : ℝ) := by
        have htR : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast htN
        linarith
      exact mul_nonneg h1 h2
    rw [Real.sqrt_div hrad (N : ℝ)]
  have hpi : Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    have hNle : (N : ℝ) / (M : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (show (0 : ℝ) < (M : ℝ) ^ 2 from pow_pos hMpos 2)]
      exact hM2
    have hh := mul_le_mul_of_nonneg_left hNle (sq_nonneg (Real.pi))
    have hform : Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2
        = Real.pi ^ 2 * ((N : ℝ) / (M : ℝ) ^ 2) := by ring
    rw [hform]
    simpa using! hh
  have hsd : Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (M : ℝ)
      ≤ Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ)) / (N : ℝ)) :=
    le_trans hdivle (le_of_eq hsqrtdiv)
  have hmain : 2 * Real.pi * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (M : ℝ)
      ≤ 2 * Real.pi * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ)) / (N : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hsd (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
    have hform : 2 * Real.pi * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (M : ℝ)
        = 2 * Real.pi * (Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (M : ℝ)) := by ring
    rw [hform]
    exact hh
  have hz' : |(N : ℝ) * aeEstimate M z - (t : ℝ)| ≤
      2 * Real.pi * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (M : ℝ) +
        Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 := by
    simpa [countWindow] using! hz
  calc
    |(N : ℝ) * aeEstimate M z - (t : ℝ)| ≤
        2 * Real.pi * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ))) / (M : ℝ) +
          Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 := hz'
    _ ≤ 2 * Real.pi * Real.sqrt ((t : ℝ) * ((N : ℝ) - (t : ℝ)) / (N : ℝ)) + Real.pi ^ 2 :=
      add_le_add hmain hpi

theorem count_output_window_at_grid {N : ℕ} (hN : 0 < N) {M : ℕ}
    (hgrid : Real.sqrt N ≤ (M : ℝ)) (hM2 : (N : ℝ) ≤ (M : ℝ) ^ 2)
    (t : ℕ) (ht0 : 0 ≤ t) (htN : t ≤ N) (z : Fin M) (hz : countWindow N M 1 t z) :
    countOutputWindow N t M z := by
  have hscale := count_window_at_scale hN hgrid hM2 t ht0 htN z hz
  have hae : (0 : ℝ) ≤ (N : ℝ) * aeEstimate M z := by
    unfold aeEstimate
    positivity
  have hround : |(countOutput N M z : ℝ) - (N : ℝ) * aeEstimate M z| ≤ 1 / 2 := by
    simpa [countOutput] using! countRounded_abs ((N : ℝ) * aeEstimate M z) hae
  have htri : |(countOutput N M z : ℝ) - (t : ℝ)| ≤
      |(countOutput N M z : ℝ) - (N : ℝ) * aeEstimate M z| +
        |(N : ℝ) * aeEstimate M z - (t : ℝ)| :=
    abs_sub_le _ _ _
  rw [countOutputWindow]
  nlinarith [htri, hround, hscale, pi_sq_add_half_lt_eleven]

noncomputable def countingLaw (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N)
    (S : Finset (Fin N)) : FinDist (Fin (countGridSize N)) :=
  aeLaw (countGridSize N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN)
    (countGridSize_two_le N hN2)

theorem clause8_counting_k2_window (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N)
    (S : Finset (Fin N)) (k : ℕ) (hk : 2 ≤ k) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countWindow N (countGridSize N) k S.card z),
      (countingLaw N hN hN2 S).prob z ≥ 1 - 1 / (2 * ((k : ℝ) - 1)) := by
  have h := bhmt_counting_k2_window N (countGridSize N) S hN (countGridSize_two_le N hN2) k hk
  simpa [countWindow, countingLaw] using! h

theorem clause8_counting_k1_window (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N) (S : Finset (Fin N)) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countWindow N (countGridSize N) 1 S.card z),
      (countingLaw N hN hN2 S).prob z ≥ 8 / Real.pi ^ 2 := by
  have h := amplitude_counting_actual_consumer N (countGridSize N) hN
    (countGridSize_two_le N hN2) S
  simpa [countWindow, countingLaw] using! h

theorem clause8_counting_rounded_output (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N)
    (S : Finset (Fin N)) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countOutputWindow N S.card (countGridSize N) z),
      (countingLaw N hN hN2 S).prob z ≥ 8 / Real.pi ^ 2 := by
  classical
  have hgrid := countGridSize_sqrt_le N hN
  have hM2 := countGridSize_sq N hN
  have hsubset : Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countWindow N (countGridSize N) 1 S.card z)
      ⊆ Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countOutputWindow N S.card (countGridSize N) z) := by
    intro z hz
    have hz' : countWindow N (countGridSize N) 1 S.card z := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using! hz
    have hw := count_output_window_at_grid hN hgrid hM2 S.card
      (Nat.zero_le _) (by simpa using! (Finset.card_le_univ S)) z hz'
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using! hw
  have hnonneg : ∀ z ∈ (Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countOutputWindow N S.card (countGridSize N) z)),
      z ∉ (Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countWindow N (countGridSize N) 1 S.card z)) →
      0 ≤ (countingLaw N hN hN2 S).prob z := by
    intro z _ _
    exact (countingLaw N hN hN2 S).nonneg z
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have h2 : (∑ z ∈ Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countOutputWindow N S.card (countGridSize N) z),
      (countingLaw N hN hN2 S).prob z)
      ≥ (∑ z ∈ Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countWindow N (countGridSize N) 1 S.card z),
        (countingLaw N hN hN2 S).prob z) := by
    simpa [countWindow] using! hsum
  have h3 : (∑ z ∈ Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countWindow N (countGridSize N) 1 S.card z),
      (countingLaw N hN hN2 S).prob z) ≥ 8 / Real.pi ^ 2 := by
    simpa [countWindow] using! clause8_counting_k1_window N hN hN2 S
  linarith

theorem clause8_counting_endpoint (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N) (S : Finset (Fin N)) :
    (∀ k : ℕ, 2 ≤ k →
      ∑ z ∈ Finset.univ.filter (fun z : Fin (countGridSize N) =>
          countWindow N (countGridSize N) k S.card z),
        (countingLaw N hN hN2 S).prob z ≥ 1 - 1 / (2 * ((k : ℝ) - 1))) ∧
    (∑ z ∈ Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countWindow N (countGridSize N) 1 S.card z),
      (countingLaw N hN hN2 S).prob z ≥ 8 / Real.pi ^ 2) ∧
    (∑ z ∈ Finset.univ.filter (fun z : Fin (countGridSize N) =>
        countOutputWindow N S.card (countGridSize N) z),
      (countingLaw N hN hN2 S).prob z ≥ 8 / Real.pi ^ 2) := by
  refine ⟨clause8_counting_k2_window N hN hN2 S, clause8_counting_k1_window N hN hN2 S,
    clause8_counting_rounded_output N hN hN2 S⟩

private theorem tan_sq_add_one (x : ℝ) (hc : Real.cos x ≠ 0) :
    (1 : ℝ) + Real.tan x ^ 2 = 1 / Real.cos x ^ 2 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc]
  have := Real.sin_sq_add_cos_sq x
  nlinarith

private theorem stationarity_cos_mul (x : ℝ) (hc : Real.cos x ≠ 0) :
    Real.sin x - 2 * x * Real.cos x = Real.cos x * restartStationarityResidual x := by
  rw [restartStationarityResidual, Real.tan_eq_sin_div_cos]
  field_simp [hc]

private theorem hasDerivAt_stationarity (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt restartStationarityResidual (1 / Real.cos x ^ 2 - 2) x := by
  have ht := Real.hasDerivAt_tan hc
  have hmul : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa only [id_eq, mul_one] using! (hasDerivAt_id x).const_mul 2
  have h := ht.sub hmul
  convert! h using 1

private theorem deriv_stationarity (x : ℝ) (hc : Real.cos x ≠ 0) :
    deriv restartStationarityResidual x = Real.tan x ^ 2 - 1 := by
  rw [(hasDerivAt_stationarity x hc).deriv, ← tan_sq_add_one x hc]
  ring

private theorem stationarity_neg_strictMonoOn_lo :
    StrictMonoOn (fun x : ℝ => 2 * x - Real.tan x) (Set.Icc 0 (Real.pi / 4)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · intro x hx
    have htan : ContinuousOn Real.tan (Set.Icc 0 (Real.pi / 4)) := by
      refine Real.continuousOn_tan.mono ?_
      intro y hy
      have hy1 : 0 ≤ y := hy.1
      have hy2 : y ≤ Real.pi / 4 := hy.2
      have hy' : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      exact (Real.cos_pos_of_mem_Ioo hy').ne'
    have htwo : ContinuousOn (fun x : ℝ => 2 * x) (Set.Icc 0 (Real.pi / 4)) :=
      continuousOn_const.mul continuousOn_id
    have hsub : ContinuousOn (fun x : ℝ => 2 * x - Real.tan x) (Set.Icc 0 (Real.pi / 4)) :=
      htwo.sub htan
    have hcw : ContinuousWithinAt (fun x : ℝ => 2 * x - Real.tan x)
        (Set.Icc 0 (Real.pi / 4)) x := hsub.continuousWithinAt hx
    simpa [restartStationarityResidual] using! hcw
  · intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 4) := by
      simpa only [interior_Icc] using! hx
    have hx1 : 0 < x := hx'.1
    have hx2 : x < Real.pi / 4 := hx'.2
    have hxI : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hcos : Real.cos x ≠ 0 := by
      exact (Real.cos_pos_of_mem_Ioo hxI).ne'
    have hmul : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
      simpa only [id_eq, mul_one] using! (hasDerivAt_id x).const_mul 2
    have htan := Real.hasDerivAt_tan hcos
    have hder : deriv (fun t : ℝ => 2 * t - Real.tan t) x = 2 - 1 / Real.cos x ^ 2 := by
      have h := (hmul.sub htan).deriv
      simpa using! h
    have htan_lt : Real.tan x < 1 := by
      have hx4 : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      have h4' : Real.tan (Real.pi / 4) = 1 := Real.tan_pi_div_four
      have hlt := Real.strictMonoOn_tan hxI hx4 (by linarith [Real.pi_pos])
      simpa [h4'] using! hlt
    have htan_pos : 0 < Real.tan x := by
      have h0 : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      have hlt := Real.strictMonoOn_tan h0 hxI (by linarith)
      simpa using! hlt
    rw [hder, ← tan_sq_add_one x hcos]
    nlinarith [sq_nonneg (Real.tan x)]

private theorem stationarity_strictMonoOn_hi :
    StrictMonoOn (fun x : ℝ => Real.tan x - 2 * x) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
  · intro x hx
    have htan : ContinuousOn Real.tan (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      refine Real.continuousOn_tan.mono ?_
      intro y hy
      have hy1 : Real.pi / 4 < y := hy.1
      have hy2 : y < Real.pi / 2 := hy.2
      have hy' : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      exact (Real.cos_pos_of_mem_Ioo hy').ne'
    have htwo : ContinuousOn (fun x : ℝ => 2 * x) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      continuousOn_const.mul continuousOn_id
    have hsub : ContinuousOn (fun x : ℝ => Real.tan x - 2 * x)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := htan.sub htwo
    have hcw : ContinuousWithinAt (fun x : ℝ => Real.tan x - 2 * x)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) x := hsub.continuousWithinAt hx
    simpa [restartStationarityResidual] using! hcw
  · intro x hx
    have hx' : x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
      simpa only [interior_Ioo] using! hx
    have hx1 : Real.pi / 4 < x := hx'.1
    have hx2 : x < Real.pi / 2 := hx'.2
    have hxI : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hcos : Real.cos x ≠ 0 := by
      exact (Real.cos_pos_of_mem_Ioo hxI).ne'
    have htan := Real.hasDerivAt_tan hcos
    have hder : deriv (fun t : ℝ => Real.tan t - 2 * t) x = 1 / Real.cos x ^ 2 - 2 := by
      have h := (htan.sub ((hasDerivAt_id x).mul_const 2)).deriv
      simpa [mul_comm] using! h
    have htan_gt : 1 < Real.tan x := by
      have hx4 : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      have h4' : Real.tan (Real.pi / 4) = 1 := Real.tan_pi_div_four
      have hlt := Real.strictMonoOn_tan hx4 hxI (by linarith [Real.pi_pos])
      simpa [h4'] using! hlt
    rw [hder, ← tan_sq_add_one x hcos]
    nlinarith [sq_nonneg (Real.tan x)]

theorem restartOptimalAngle_bounds :
    Real.pi / 2 < restartOptimalAngle ∧ restartOptimalAngle < Real.pi := by
  obtain ⟨htan, hlo, hhi⟩ := restartOptimalAngle_spec
  refine ⟨?_, ?_⟩
  · have hpi : Real.pi / 2 < 233112 / 100000 := by
      have := Real.pi_lt_d4
      linarith
    linarith
  · have hpi : 233113 / 100000 < Real.pi := by
      have := Real.pi_gt_d4
      linarith
    linarith

theorem restartOptimalAngle_half_mem :
    restartOptimalAngle / 2 ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
  obtain ⟨hlo, hhi⟩ := restartOptimalAngle_bounds
  constructor
  · have hz : (2 : ℝ) * (Real.pi / 4) < restartOptimalAngle := by linarith
    linarith
  · have hz : restartOptimalAngle < (2 : ℝ) * (Real.pi / 2) := by linarith
    linarith

theorem restartScaledOptimum_mem :
    restartScaledOptimum ∈ Set.Ioo 0 (Real.pi / 4) := by
  constructor
  · have hz : 0 < restartOptimalAngle := by
      obtain ⟨_, hlo, _⟩ := restartOptimalAngle_spec
      linarith
    rw [restartScaledOptimum]
    linarith
  · have hz : restartOptimalAngle < Real.pi := restartOptimalAngle_bounds.2
    rw [restartScaledOptimum]
    linarith

theorem stationarity_neg_of_lt_half (x : ℝ) (hx : 0 < x)
    (hx2 : x < restartOptimalAngle / 2) :
    restartStationarityResidual x < 0 := by
  by_cases hcase : x ≤ Real.pi / 4
  · have hstrict : 2 * x - Real.tan x > 2 * 0 - Real.tan 0 := by
      have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 4) := ⟨by linarith, by linarith [Real.pi_pos]⟩
      have hx' : x ∈ Set.Icc 0 (Real.pi / 4) := ⟨by linarith, hcase⟩
      have hlt := stationarity_neg_strictMonoOn_lo h0 hx' (by linarith)
      simpa using! hlt
    have h0 : Real.tan 0 = 0 := by simp
    have hneg : Real.tan x - 2 * x < 0 := by linarith
    rw [restartStationarityResidual]
    exact hneg
  · have hx' : x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
      constructor
      · linarith
      · have := restartOptimalAngle_half_mem
        linarith [this.2]
    have hz := restartOptimalAngle_half_mem
    have hztan : Real.tan (restartOptimalAngle / 2) = restartOptimalAngle := by
      obtain ⟨htan, _, _⟩ := restartOptimalAngle_spec
      exact htan
    have hstrict : Real.tan x - 2 * x
        < Real.tan (restartOptimalAngle / 2) - 2 * (restartOptimalAngle / 2) := by
      have hlt := stationarity_strictMonoOn_hi hx' hz (by linarith)
      simpa using! hlt
    rw [restartStationarityResidual]
    linarith [hztan]

theorem stationarity_pos_of_gt_half (x : ℝ) (hx : restartOptimalAngle / 2 < x)
    (hx2 : x < Real.pi / 2) :
    restartStationarityResidual x > 0 := by
  have hx' : x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
    constructor
    · have := restartOptimalAngle_half_mem
      linarith [this.1]
    · exact hx2
  have hz := restartOptimalAngle_half_mem
  have hztan : Real.tan (restartOptimalAngle / 2) = restartOptimalAngle := by
    obtain ⟨htan, _, _⟩ := restartOptimalAngle_spec
    exact htan
  have hstrict : Real.tan x - 2 * x
      > Real.tan (restartOptimalAngle / 2) - 2 * (restartOptimalAngle / 2) := by
    have hlt := stationarity_strictMonoOn_hi hz hx' (by linarith)
    simpa using! hlt
  rw [restartStationarityResidual]
  linarith [hztan]

private theorem hasDerivAt_scaledProfile (u : ℝ) (hs : Real.sin (2 * u) ≠ 0) :
    HasDerivAt (fun t : ℝ => t / Real.sin (2 * t) ^ 2)
      ((Real.sin (2 * u) ^ 2 - u * (4 * Real.sin (2 * u) * Real.cos (2 * u))) /
        Real.sin (2 * u) ^ 4) u := by
  have hmul : HasDerivAt (fun t : ℝ => 2 * t) 2 u := by
    simpa only [id_eq, mul_one] using! (hasDerivAt_id u).const_mul 2
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * u)) u := by
    have h := (Real.hasDerivAt_sin (2 * u)).comp u hmul
    have h' : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * u) * 2) u := by
      simpa only [Function.comp_apply] using! h
    have heq : Real.cos (2 * u) * 2 = 2 * Real.cos (2 * u) := by ring
    rw [heq] at h'
    exact h'
  have hsq : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (4 * Real.sin (2 * u) * Real.cos (2 * u)) u := by
    have h := hsin.pow 2
    have h' : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
        (2 * Real.sin (2 * u) * (2 * Real.cos (2 * u))) u := by
      have h'' := h
      convert! h'' using 1
      · ring
    have heq : 2 * Real.sin (2 * u) * (2 * Real.cos (2 * u))
        = 4 * Real.sin (2 * u) * Real.cos (2 * u) := by ring
    rw [heq] at h'
    exact h'
  have hden : (Real.sin (2 * u) ^ 2) ≠ 0 := by
    intro hz
    have h1 : Real.sin (2 * u) = 0 := (sq_eq_zero_iff).mp hz
    exact hs h1
  have hdiv := (hasDerivAt_id u).div hsq hden
  have hfun : (_root_.id / fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      = fun t => t / Real.sin (2 * t) ^ 2 := by
    funext t
    simp
  rw [hfun] at hdiv
  convert! hdiv using 1
  · simp only [id_eq, one_mul]
    have hpow : (Real.sin (2 * u) ^ 2) ^ 2 = Real.sin (2 * u) ^ 4 := by ring
    rw [hpow]

private theorem deriv_scaledProfile (u : ℝ) (hs : Real.sin (2 * u) ≠ 0) :
    deriv (fun t : ℝ => t / Real.sin (2 * t) ^ 2) u =
      (Real.sin (2 * u) ^ 2 - u * (4 * Real.sin (2 * u) * Real.cos (2 * u))) /
        Real.sin (2 * u) ^ 4 :=
  (hasDerivAt_scaledProfile u hs).deriv

private theorem scaledProfile_deriv_neg (u : ℝ) (hu : 0 < u)
    (hu2 : u < restartScaledOptimum) :
    deriv (fun t : ℝ => t / Real.sin (2 * t) ^ 2) u < 0 := by
  have hmem := restartScaledOptimum_mem
  have hu2' : u < restartOptimalAngle / 4 := by
    rw [restartScaledOptimum] at hu2
    exact hu2
  have hsin : Real.sin (2 * u) ≠ 0 := by
    have hpos : 0 < 2 * u := by linarith
    have hbig : 0 < 2 * u ∧ 2 * u < Real.pi := ⟨hpos, by linarith [hmem.2, hu2]⟩
    exact (Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2).ne'
  have hcos : Real.cos (2 * u) ≠ 0 := by
    have hpos : 0 < 2 * u := by linarith
    have hlt : 2 * u < Real.pi / 2 := by linarith [hmem.2, hu2]
    have : 2 * u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    exact (Real.cos_pos_of_mem_Ioo this).ne'
  rw [deriv_scaledProfile u hsin]
  have hres : Real.sin (2 * u) - 4 * u * Real.cos (2 * u) < 0 := by
    have hr := stationarity_neg_of_lt_half (2 * u) (by linarith) (by
      have hz := restartOptimalAngle_half_mem
      linarith [hz.2])
    have hmul := stationarity_cos_mul (2 * u) hcos
    have hcospos : 0 < Real.cos (2 * u) := by
      have hpos : 0 < 2 * u := by linarith
      have hlt : 2 * u < Real.pi / 2 := by linarith [hmem.2, hu2]
      have : 2 * u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      exact Real.cos_pos_of_mem_Ioo this
    have hmul' : Real.cos (2 * u) * restartStationarityResidual (2 * u)
        = Real.sin (2 * u) - 2 * (2 * u) * Real.cos (2 * u) := hmul.symm
    have hlt := mul_lt_mul_of_pos_right hr hcospos
    nlinarith [hlt, hmul']
  have hsinpos : 0 < Real.sin (2 * u) := by
    have hpos : 0 < 2 * u := by linarith
    have hbig : 0 < 2 * u ∧ 2 * u < Real.pi := ⟨hpos, by linarith [hmem.2, hu2]⟩
    exact Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2
  have hfactor : Real.sin (2 * u) ^ 2 - u * (4 * Real.sin (2 * u) * Real.cos (2 * u))
      = Real.sin (2 * u) * (Real.sin (2 * u) - 4 * u * Real.cos (2 * u)) := by ring
  rw [hfactor]
  have hnum : Real.sin (2 * u) * (Real.sin (2 * u) - 4 * u * Real.cos (2 * u)) < 0 :=
    mul_neg_of_pos_of_neg hsinpos hres
  exact div_neg_of_neg_of_pos hnum (pow_pos hsinpos 4)

private theorem scaledProfile_deriv_pos (u : ℝ) (hu : restartScaledOptimum < u)
    (hu2 : u < Real.pi / 4) :
    deriv (fun t : ℝ => t / Real.sin (2 * t) ^ 2) u > 0 := by
  have hmem := restartScaledOptimum_mem
  have hu' : restartOptimalAngle / 4 < u := by
    rw [restartScaledOptimum] at hu
    exact hu
  have hsin : Real.sin (2 * u) ≠ 0 := by
    have hpos : 0 < 2 * u := by linarith [hmem.1, hu]
    have hbig : 0 < 2 * u ∧ 2 * u < Real.pi := ⟨hpos, by linarith [Real.pi_pos]⟩
    exact (Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2).ne'
  have hcos : Real.cos (2 * u) ≠ 0 := by
    have hpos : 0 < 2 * u := by linarith [hmem.1, hu]
    have hlt : 2 * u < Real.pi / 2 := by linarith [Real.pi_pos]
    have : 2 * u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    exact (Real.cos_pos_of_mem_Ioo this).ne'
  rw [deriv_scaledProfile u hsin]
  have hres : 0 < Real.sin (2 * u) - 4 * u * Real.cos (2 * u) := by
    have hr := stationarity_pos_of_gt_half (2 * u) (by
      have hz := restartOptimalAngle_half_mem
      linarith [hz.1, hu']) (by linarith [Real.pi_pos])
    have hmul := stationarity_cos_mul (2 * u) hcos
    have hcospos : 0 < Real.cos (2 * u) := by
      have hpos : 0 < 2 * u := by linarith [hmem.1, hu]
      have hlt : 2 * u < Real.pi / 2 := by linarith [Real.pi_pos]
      have : 2 * u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      exact Real.cos_pos_of_mem_Ioo this
    have hmul' : Real.cos (2 * u) * restartStationarityResidual (2 * u)
        = Real.sin (2 * u) - 2 * (2 * u) * Real.cos (2 * u) := hmul.symm
    have hpos' := mul_pos hcospos hr
    nlinarith [hpos', hmul']
  have hsinpos : 0 < Real.sin (2 * u) := by
    have hpos : 0 < 2 * u := by linarith [hmem.1, hu]
    have hbig : 0 < 2 * u ∧ 2 * u < Real.pi := ⟨hpos, by linarith [Real.pi_pos]⟩
    exact Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2
  have hfactor : Real.sin (2 * u) ^ 2 - u * (4 * Real.sin (2 * u) * Real.cos (2 * u))
      = Real.sin (2 * u) * (Real.sin (2 * u) - 4 * u * Real.cos (2 * u)) := by ring
  rw [hfactor]
  have hnum : 0 < Real.sin (2 * u) * (Real.sin (2 * u) - 4 * u * Real.cos (2 * u)) :=
    mul_pos hsinpos hres
  exact div_pos hnum (pow_pos hsinpos 4)

private theorem scaledProfile_continuousOn {D : Set ℝ}
    (hD : ∀ u ∈ D, 0 < u ∧ u ≤ Real.pi / 4) :
    ContinuousOn (fun u : ℝ => restartScaledProfile u) D := by
  have hsin : Continuous (fun t : ℝ => Real.sin (2 * t)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hsq : ContinuousOn (fun t : ℝ => (Real.sin (2 * t)) ^ 2) D := by
    exact (hsin.continuousOn.pow 2).mono (Set.subset_univ _)
  refine continuousOn_id.div hsq ?_
  intro u hu
  have h := hD u hu
  have hpos : 0 < 2 * u := by linarith
  have hbig : 0 < 2 * u ∧ 2 * u < Real.pi := ⟨hpos, by linarith [Real.pi_pos]⟩
  have hsinpos : 0 < Real.sin (2 * u) := Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2
  intro hz
  exact absurd ((sq_eq_zero_iff).mp hz) (ne_of_gt hsinpos)

private theorem scaledProfile_strictMonoOn_dec :
    StrictMonoOn (fun u : ℝ => -restartScaledProfile u)
      (Set.Icc (1 / 16) restartScaledOptimum) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · intro u hu
    have hD : ∀ v ∈ Set.Icc (1 / 16) restartScaledOptimum, 0 < v ∧ v ≤ Real.pi / 4 := by
      intro v hv
      have hv1 : 1 / 16 ≤ v := hv.1
      have hv2 : v ≤ restartScaledOptimum := hv.2
      exact ⟨by linarith, by linarith [restartScaledOptimum_mem.2, hv2]⟩
    have hcont := scaledProfile_continuousOn hD
    have hcw : ContinuousWithinAt (fun u : ℝ => -restartScaledProfile u)
        (Set.Icc (1 / 16) restartScaledOptimum) u := by
      have := hcont.neg.continuousWithinAt hu
      simpa [restartScaledProfile] using! this
    exact hcw
  · intro u hu
    have hu' : u ∈ Set.Ioo (1 / 16) restartScaledOptimum := by
      simpa only [interior_Icc] using! hu
    have hder := scaledProfile_deriv_neg u (by linarith [hu'.1]) hu'.2
    have hnegderiv : deriv (fun t : ℝ => -restartScaledProfile t) u
        = -deriv (fun t : ℝ => t / Real.sin (2 * t) ^ 2) u := by
      have hD := (hasDerivAt_scaledProfile u (by
        have hpos : 0 < 2 * u := by linarith [hu'.1]
        have hlt : 2 * u < Real.pi := by
          have hu'' : u < Real.pi / 4 := by linarith [restartScaledOptimum_mem.2, hu'.2]
          linarith [Real.pi_pos]
        have hbig : 0 < 2 * u ∧ 2 * u < Real.pi := ⟨hpos, hlt⟩
        exact (Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2).ne')).neg
      have h := hD.deriv
      simpa [restartScaledProfile] using! h
    rw [hnegderiv]
    linarith

private theorem scaledProfile_strictMonoOn_inc :
    StrictMonoOn (fun u : ℝ => restartScaledProfile u)
      (Set.Icc restartScaledOptimum (Real.pi / 4)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · intro u hu
    have hD : ∀ v ∈ Set.Icc restartScaledOptimum (Real.pi / 4), 0 < v ∧ v ≤ Real.pi / 4 := by
      intro v hv
      have hv1 : restartScaledOptimum ≤ v := hv.1
      have hv2 : v ≤ Real.pi / 4 := hv.2
      exact ⟨by linarith [restartScaledOptimum_mem.1, hv1], hv2⟩
    have hcont := scaledProfile_continuousOn hD
    have hcw : ContinuousWithinAt (fun u : ℝ => restartScaledProfile u)
        (Set.Icc restartScaledOptimum (Real.pi / 4)) u := hcont.continuousWithinAt hu
    simpa [restartScaledProfile] using! hcw
  · intro u hu
    have hu' : u ∈ Set.Ioo restartScaledOptimum (Real.pi / 4) := by
      simpa only [interior_Icc] using! hu
    have hder := scaledProfile_deriv_pos u hu'.1 hu'.2
    have hder' : deriv (fun t : ℝ => restartScaledProfile t) u > 0 := by
      simpa only [restartScaledProfile] using! hder
    exact hder'

private theorem scaledProfile_ge_four_of_small (u : ℝ) (hu : 0 < u) (hu2 : u ≤ 1 / 16) :
    restartScaledProfile u ≥ 4 := by
  have h1 : |Real.sin (2 * u)| ≤ |2 * u| := Real.abs_sin_le_abs
  have h2 : Real.sin (2 * u) ^ 2 ≤ (2 * u) ^ 2 := by
    have hsq := mul_self_le_mul_self (abs_nonneg _) h1
    have habs1 : |Real.sin (2 * u)| * |Real.sin (2 * u)| = Real.sin (2 * u) ^ 2 := by
      rw [← pow_two, sq_abs]
    have habs2 : |2 * u| * |2 * u| = (2 * u) ^ 2 := by
      rw [← pow_two, sq_abs]
    rw [habs1, habs2] at hsq
    exact hsq
  have hpos : 0 < Real.sin (2 * u) ^ 2 := by
    have hpos' : 0 < 2 * u := by linarith
    have hbig : 0 < 2 * u ∧ 2 * u < Real.pi := ⟨hpos', by linarith [Real.pi_gt_d4, hu2]⟩
    have hsin := Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2
    positivity
  rw [restartScaledProfile]
  have hden : 0 < Real.sin (2 * u) ^ 2 := hpos
  have heq : 4 ≤ u / Real.sin (2 * u) ^ 2 ↔ 4 * Real.sin (2 * u) ^ 2 ≤ u :=
    le_div_iff₀ hden
  rw [ge_iff_le, heq]
  have h3 : 4 * Real.sin (2 * u) ^ 2 ≤ 4 * (2 * u) ^ 2 := by nlinarith [h2]
  nlinarith [hu, hu2]

theorem scaledProfile_optimum_value :
    restartScaledProfile restartScaledOptimum = restartScaledExpectation := by
  rw [restartScaledProfile, restartScaledOptimum, restartScaledExpectation]
  have hz : restartOptimalAngle ≠ 0 := by
    obtain ⟨_, hlo, _⟩ := restartOptimalAngle_spec
    linarith
  have hcos : Real.cos (restartOptimalAngle / 2) ≠ 0 := by
    have hu' := restartOptimalAngle_half_mem
    have hu1 : Real.pi / 4 < restartOptimalAngle / 2 := hu'.1
    have hu2 : restartOptimalAngle / 2 < Real.pi / 2 := hu'.2
    have hu'' : restartOptimalAngle / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    exact (Real.cos_pos_of_mem_Ioo hu'').ne'
  field_simp
  ring

theorem clause36_source_constants :
    58278 / 100000 < restartScaledOptimum ∧ restartScaledOptimum < 58279 / 100000 ∧
      69002 / 100000 < restartScaledExpectation ∧ restartScaledExpectation < 69003 / 100000 := by
  obtain ⟨htan, hlo, hhi⟩ := restartOptimalAngle_spec
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ :=
    section3OptimalConstantsSubgoal restartOptimalAngle htan hlo hhi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [restartScaledOptimum]
    exact h3
  · rw [restartScaledOptimum]
    exact h4
  · rw [restartScaledExpectation]
    exact h5
  · rw [restartScaledExpectation]
    exact h6

theorem scaledProfile_min_unique (u : ℝ) (hu : 0 < u) (hu2 : u < Real.pi / 4) :
    restartScaledProfile u ≥ restartScaledProfile restartScaledOptimum ∧
      (u ≠ restartScaledOptimum → restartScaledProfile u > restartScaledProfile restartScaledOptimum) := by
  have hopt := restartScaledOptimum_mem
  have hopt1 : 0 < restartScaledOptimum := hopt.1
  have hopt2 : restartScaledOptimum < Real.pi / 4 := hopt.2
  have hoptsmall : restartScaledProfile restartScaledOptimum < 1 := by
    rw [scaledProfile_optimum_value]
    have h := clause36_source_constants
    linarith
  by_cases hsmall : u < 1 / 16
  · have hbig := scaledProfile_ge_four_of_small u hu (le_of_lt hsmall)
    constructor
    · linarith
    · intro _
      linarith
  · by_cases hcase : u < restartScaledOptimum
    · have hlo : 1 / 16 ≤ u := not_lt.mp hsmall
      have hhi : u ≤ restartScaledOptimum := le_of_lt hcase
      have hoptlo : 1 / 16 ≤ restartScaledOptimum := by linarith
      have hmono := scaledProfile_strictMonoOn_dec
        (Set.mem_Icc.mpr ⟨hlo, hhi⟩)
        (Set.mem_Icc.mpr ⟨hoptlo, le_rfl⟩) hcase
      have hneg : -restartScaledProfile u
          < -restartScaledProfile restartScaledOptimum := by simpa using! hmono
      constructor
      · linarith
      · intro _
        linarith
    · by_cases hfinal : u = restartScaledOptimum
      · have h1 : restartScaledProfile u = restartScaledProfile restartScaledOptimum := by
          rw [hfinal]
        exact ⟨h1.symm.le, fun h => absurd hfinal h⟩
      · have hge : restartScaledOptimum ≤ u := not_lt.mp hcase
        have hlt : restartScaledOptimum < u := lt_of_le_of_ne hge (Ne.symm hfinal)
        have hmono := scaledProfile_strictMonoOn_inc
          (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hopt2⟩)
          (Set.mem_Icc.mpr ⟨hge, le_of_lt hu2⟩) hlt
        have hpos : restartScaledProfile restartScaledOptimum
            < restartScaledProfile u := by simpa using! hmono
        exact ⟨by linarith, fun _ => hpos⟩

theorem restartRoundedDepth_nearest (θ : ℝ) (hθ : 0 < θ) :
    |(restartRoundedDepth θ restartOptimalAngle : ℝ) - restartOptimalAngle / (4 * θ)| ≤ 1 / 2 := by
  have hx : 0 ≤ restartOptimalAngle / (4 * θ) := by
    have : 0 < restartOptimalAngle := by
      obtain ⟨_, hlo, _⟩ := restartOptimalAngle_spec
      linarith
    positivity
  have h := countRounded_abs (restartOptimalAngle / (4 * θ)) hx
  simpa [restartRoundedDepth, countRounded] using! h

theorem restartWindowDepth_spec (θ : ℝ) (hθ : 0 < θ) (hθ2 : θ ≤ Real.pi / 4) :
    1 ≤ restartWindowDepth θ ∧
      (restartWindowDepth θ : ℝ) * θ ≤ Real.pi / 4 ∧
      Real.pi / 4 - θ < (restartWindowDepth θ : ℝ) * θ := by
  rw [restartWindowDepth]
  have hpos : 0 < 4 * θ := by linarith
  have h1 : 1 ≤ Real.pi / (4 * θ) := by
    rw [le_div_iff₀ hpos]
    have h4 : 4 * θ ≤ Real.pi := by linarith [Real.pi_pos]
    linarith
  have hfloor_le : (Nat.floor (Real.pi / (4 * θ)) : ℝ) ≤ Real.pi / (4 * θ) :=
    Nat.floor_le (by positivity)
  have hfloor_lt : Real.pi / (4 * θ) < (Nat.floor (Real.pi / (4 * θ)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloor : 1 ≤ Nat.floor (Real.pi / (4 * θ)) := by
    have hpos' : (0 : ℝ) < (Nat.floor (Real.pi / (4 * θ)) : ℝ) := by linarith
    exact_mod_cast hpos'
  have hid : (Real.pi / (4 * θ)) * θ = Real.pi / 4 := by
    field_simp [ne_of_gt hpos]
  have hmul : (Nat.floor (Real.pi / (4 * θ)) : ℝ) * θ ≤ Real.pi / 4 := by
    have hle : (Nat.floor (Real.pi / (4 * θ)) : ℝ) ≤ Real.pi / (4 * θ) := hfloor_le
    have hpos : 0 < θ := hθ
    have hmul' := mul_le_mul_of_nonneg_right hle hpos.le
    linarith
  have hmul2 : Real.pi / 4 - θ < (Nat.floor (Real.pi / (4 * θ)) : ℝ) * θ := by
    have hpos : 0 < θ := hθ
    have hlt : Real.pi / (4 * θ) < (Nat.floor (Real.pi / (4 * θ)) : ℝ) + 1 := hfloor_lt
    have hmul' := mul_lt_mul_of_pos_right hlt hpos
    linarith
  exact ⟨hfloor, hmul, hmul2⟩

theorem restartIntegerOptimum_spec (θ : ℝ) (M : ℕ) (hM : 0 < M) :
    1 ≤ restartIntegerOptimum θ M ∧ restartIntegerOptimum θ M ≤ M ∧
      restartProfile θ (restartIntegerOptimum θ M) = restartOptimalValue θ M := by
  have hfind : restartIntegerOptimum θ M
      = Nat.find (restartIntegerOptimum_exists θ M hM) := by
    simp [restartIntegerOptimum, dif_pos hM]
  rw [hfind]
  obtain ⟨h1, h2, h3⟩ := Nat.find_spec (restartIntegerOptimum_exists θ M hM)
  exact ⟨h1, h2, h3⟩

theorem restartProfile_ge_min (θ : ℝ) (M : ℕ) (hM : 0 < M) (j : ℕ) (hj : 1 ≤ j)
    (hjM : j ≤ M) :
    restartProfile θ (j : ℝ) ≥ restartOptimalValue θ M := by
  have hne : (restartWindowProfile θ M).Nonempty :=
    Finset.image_nonempty.mpr ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hmem : restartProfile θ (j : ℝ) ∈ restartWindowProfile θ M := by
    rw [restartWindowProfile, Finset.mem_image]
    exact ⟨j, Finset.mem_Icc.mpr ⟨hj, hjM⟩, rfl⟩
  have hle : (restartWindowProfile θ M).min' ⟨restartProfile θ (j : ℝ), hmem⟩
      ≤ restartProfile θ (j : ℝ) :=
    Finset.min'_le (restartWindowProfile θ M) (restartProfile θ (j : ℝ)) hmem
  have hcongr : (restartWindowProfile θ M).min' ⟨restartProfile θ (j : ℝ), hmem⟩
      = restartOptimalValue θ M := by
    rw [restartOptimalValue, dif_pos hM]
  rw [hcongr] at hle
  exact hle

theorem scaledProfileθ_eq_profile (j : ℕ) (θ : ℝ) :
    restartScaledProfileθ ((j : ℝ) * θ) θ = θ * restartProfile θ (j : ℝ) := by
  rw [restartScaledProfileθ, restartProfile, restartExpectedIterations, mul_div_assoc]
  have h : 2 * ((j : ℝ) * θ) + θ = (2 * (j : ℝ) + 1) * θ := by ring
  rw [h]
  ring

private theorem sin_sq_sub_sin_sq (a b : ℝ) :
    Real.sin a ^ 2 - Real.sin b ^ 2 = Real.sin (a + b) * Real.sin (a - b) := by
  rw [Real.sin_add, Real.sin_sub]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

theorem scaledProfile_close_wide (θ u : ℝ) (hθ : 0 < θ) (hθ2 : θ ≤ Real.pi / 4)
    (hu : restartScaledFloor ≤ u) (hu2 : u ≤ Real.pi / 4) :
    |restartScaledProfileθ u θ - restartScaledProfile u| ≤ restartScaledSlack * θ := by
  have hu0 : 0 < u := by
    rw [restartScaledFloor] at hu
    linarith
  have hsin2u : Real.sin (2 * u) ≥ Real.sin (1 / 8) := by
    have h1 : 1 / 8 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_gt_d4]
    have h2 : 2 * u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_gt_d4]
    have hmono : MonotoneOn Real.sin (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
      Real.strictMonoOn_sin.monotoneOn
    exact hmono h1 h2 (by
      rw [restartScaledFloor] at hu
      linarith)
  have hsin2uθ : Real.sin (2 * u + θ) ≥ Real.sin (1 / 8) := by
    have hmono : MonotoneOn Real.sin (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
      Real.strictMonoOn_sin.monotoneOn
    by_cases hle : 2 * u + θ ≤ Real.pi / 2
    · have h1 : 1 / 8 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_gt_d4]
      have h2 : 2 * u + θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_gt_d4]
      exact hmono h1 h2 (by
        rw [restartScaledFloor] at hu
        linarith)
    · have hgt : Real.pi / 2 < 2 * u + θ := by linarith
      have hhi : 2 * u + θ ≤ 3 * Real.pi / 4 := by
        have h2u : 2 * u ≤ Real.pi / 2 := by linarith
        linarith
      have h1 : Real.pi / 4 ≤ Real.pi - (2 * u + θ) := by linarith
      have h2 : Real.pi - (2 * u + θ) ≤ Real.pi / 2 := by linarith
      have h3 : Real.sin (Real.pi - (2 * u + θ)) ≥ Real.sin (Real.pi / 4) := by
        have h4 : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> linarith [Real.pi_pos]
        have h5 : Real.pi - (2 * u + θ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> linarith [Real.pi_pos]
        exact hmono h4 h5 (by linarith)
      have hq : Real.sin (1 / 8) < Real.sin (Real.pi / 4) := by
        have h1 : (1 / 8 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> linarith [Real.pi_gt_d4]
        have h2 : (Real.pi / 4 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> linarith [Real.pi_pos]
        exact (Real.strictMonoOn_sin.lt_iff_lt h1 h2).2 (by linarith [Real.pi_gt_d4])
      rw [Real.sin_pi_sub] at h3
      linarith
  have hdiff : |Real.sin (2 * u) ^ 2 - Real.sin (2 * u + θ) ^ 2| ≤ θ := by
    rw [sin_sq_sub_sin_sq]
    have h1 : |Real.sin (2 * u + (2 * u + θ)) * Real.sin (2 * u - (2 * u + θ))|
        = |Real.sin (2 * u + (2 * u + θ))| * |Real.sin (2 * u - (2 * u + θ))| := abs_mul _ _
    have h2 : |Real.sin (2 * u + (2 * u + θ))| ≤ 1 := Real.abs_sin_le_one _
    have h3 : |Real.sin (2 * u - (2 * u + θ))| ≤ θ := by
      have hkey : 2 * u - (2 * u + θ) = -θ := by ring
      have h : |Real.sin (2 * u - (2 * u + θ))| ≤ |2 * u - (2 * u + θ)| := by
        exact Real.abs_sin_le_abs
      rw [hkey, abs_neg] at h
      simpa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ)] using! h
    have h4 : |Real.sin (2 * u + (2 * u + θ))| * |Real.sin (2 * u - (2 * u + θ))| ≤ 1 * θ :=
      mul_le_mul h2 h3 (abs_nonneg _) (by norm_num)
    nlinarith
  have hden : 0 < Real.sin (2 * u) ^ 2 := by
    have hpos : 0 < 2 * u := by linarith
    have hbig : 0 < 2 * u ∧ 2 * u < Real.pi := ⟨hpos, by linarith [Real.pi_pos]⟩
    have h := Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2
    positivity
  have hden2 : 0 < Real.sin (2 * u + θ) ^ 2 := by
    have hpos : 0 < 2 * u + θ := by linarith
    have h2u : 2 * u ≤ Real.pi / 2 := by linarith
    have hbig : 0 < 2 * u + θ ∧ 2 * u + θ < Real.pi := ⟨hpos, by linarith⟩
    have h := Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2
    positivity
  have hA : Real.sin (2 * u) ^ 2 ≥ Real.sin (1 / 8) ^ 2 := by
    have h := mul_self_le_mul_self
      (Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_gt_d4])) hsin2u
    simpa only [pow_two] using! h
  have hB : Real.sin (2 * u + θ) ^ 2 ≥ Real.sin (1 / 8) ^ 2 := by
    have h := mul_self_le_mul_self
      (Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_gt_d4])) hsin2uθ
    simpa only [pow_two] using! h
  have hAB : Real.sin (1 / 8) ^ 4 ≤ Real.sin (2 * u) ^ 2 * Real.sin (2 * u + θ) ^ 2 := by
    have hmul : Real.sin (1 / 8) ^ 2 * Real.sin (1 / 8) ^ 2
        ≤ Real.sin (2 * u) ^ 2 * Real.sin (2 * u + θ) ^ 2 :=
      mul_le_mul hA hB (sq_nonneg _) (sq_nonneg _)
    nlinarith [hmul]
  have hmain : |restartScaledProfileθ u θ - restartScaledProfile u|
      ≤ u * θ / Real.sin (1 / 8) ^ 4 := by
    rw [restartScaledProfileθ, restartScaledProfile]
    have hA : Real.sin (2 * u) ^ 2 ≠ 0 := ne_of_gt hden
    have hB : Real.sin (2 * u + θ) ^ 2 ≠ 0 := ne_of_gt hden2
    have hden' : Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2 ≠ 0 := by
      positivity
    have hkey' : (u * (Real.sin (2 * u) ^ 2 - Real.sin (2 * u + θ) ^ 2))
          / (Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2)
        = u / Real.sin (2 * u + θ) ^ 2 - u / Real.sin (2 * u) ^ 2 := by
      have hb : u / Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u + θ) ^ 2 = u := by
        rw [mul_comm]
        exact mul_div_cancel₀ _ hB
      have h1 : u / Real.sin (2 * u + θ) ^ 2
            * (Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2)
          = u * Real.sin (2 * u) ^ 2 := by
        calc
          u / Real.sin (2 * u + θ) ^ 2
                * (Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2)
              = (u / Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u + θ) ^ 2)
                * Real.sin (2 * u) ^ 2 := by ring
          _ = u * Real.sin (2 * u) ^ 2 := by rw [hb]
      have ha : u / Real.sin (2 * u) ^ 2 * Real.sin (2 * u) ^ 2 = u := by
        rw [mul_comm]
        exact mul_div_cancel₀ _ hA
      have h2 : u / Real.sin (2 * u) ^ 2
            * (Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2)
          = u * Real.sin (2 * u + θ) ^ 2 := by
        calc
          u / Real.sin (2 * u) ^ 2
                * (Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2)
              = (u / Real.sin (2 * u) ^ 2 * Real.sin (2 * u) ^ 2)
                * Real.sin (2 * u + θ) ^ 2 := by ring
          _ = u * Real.sin (2 * u + θ) ^ 2 := by rw [ha]
      apply (div_eq_iff hden').mpr
      have h3 : (u / Real.sin (2 * u + θ) ^ 2 - u / Real.sin (2 * u) ^ 2)
            * (Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2)
          = u * Real.sin (2 * u) ^ 2 - u * Real.sin (2 * u + θ) ^ 2 := by
        rw [sub_mul, h1, h2]
      rw [h3]
      ring
    have hkey : u / Real.sin (2 * u + θ) ^ 2 - u / Real.sin (2 * u) ^ 2
        = u * (Real.sin (2 * u) ^ 2 - Real.sin (2 * u + θ) ^ 2)
          / (Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2) := hkey'.symm
    rw [hkey, abs_div, abs_mul, abs_of_pos (by linarith : 0 < u),
      abs_of_pos (by positivity : 0 < Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2)]
    calc
      u * |Real.sin (2 * u) ^ 2 - Real.sin (2 * u + θ) ^ 2|
            / (Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2)
          ≤ u * θ / (Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2) := by
            have hnum : u * |Real.sin (2 * u) ^ 2 - Real.sin (2 * u + θ) ^ 2| ≤ u * θ := by
              nlinarith [hdiff]
            have hD : 0 < Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2 := by positivity
            apply (div_le_div_iff₀ hD hD).mpr
            have hmul := mul_le_mul_of_nonneg_left hnum hD.le
            simpa [mul_comm] using! hmul
      _ ≤ u * θ / Real.sin (1 / 8) ^ 4 := by
        have hD : 0 < Real.sin (2 * u + θ) ^ 2 * Real.sin (2 * u) ^ 2 := by positivity
        have hs4 : 0 < Real.sin (1 / 8) ^ 4 := by
          have hlow : 0 < Real.sin (1 / 8) := by
            have hpos' : (0 : ℝ) < 1 / 8 := by norm_num
            have hbig : (0 : ℝ) < 1 / 8 ∧ 1 / 8 < Real.pi := ⟨hpos', by linarith [Real.pi_gt_d4]⟩
            exact Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2
          positivity
        have hpos : 0 ≤ u * θ := by positivity
        apply (div_le_div_iff₀ hD hs4).mpr
        have hmul := mul_le_mul_of_nonneg_left hAB hpos
        simpa [mul_comm] using! hmul
  have hfinal : u * θ / Real.sin (1 / 8) ^ 4
      ≤ restartScaledSlack * θ := by
    have h1 : u * θ ≤ (Real.pi / 4) * θ := by
      have := mul_le_mul_of_nonneg_right (by linarith : u ≤ Real.pi / 4) (by linarith : 0 ≤ θ)
      linarith
    have hpos : 0 < Real.sin (1 / 8) ^ 4 := by
      have hlow : 0 < Real.sin (1 / 8) := by
        have hpos' : (0 : ℝ) < 1 / 8 := by norm_num
        have hbig : (0 : ℝ) < 1 / 8 ∧ 1 / 8 < Real.pi := ⟨hpos', by linarith [Real.pi_gt_d4]⟩
        exact Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2
      positivity
    have h' : u * θ / Real.sin (1 / 8) ^ 4
        ≤ (Real.pi / 4) * θ / Real.sin (1 / 8) ^ 4 := div_le_div_of_nonneg_right h1 hpos.le
    calc
      u * θ / Real.sin (1 / 8) ^ 4
          ≤ (Real.pi / 4) * θ / Real.sin (1 / 8) ^ 4 := h'
      _ = restartScaledSlack * θ := by rw [restartScaledSlack]; ring
  exact hmain.trans hfinal

theorem scaledProfile_close (θ u : ℝ) (hθ : 0 < θ) (hθ2 : θ ≤ Real.pi / 4)
    (hu : restartScaledFloor ≤ u) (hu2 : u ≤ Real.pi / 4)
    (hphase : 2 * u + θ ≤ Real.pi / 2) :
    |restartScaledProfileθ u θ - restartScaledProfile u| ≤ restartScaledSlack * θ :=
  scaledProfile_close_wide θ u hθ hθ2 hu hu2

theorem scaledProfile_continuousAt (u : ℝ) (hu : 0 < u) (hu2 : u < Real.pi / 4) :
    ContinuousAt (fun t : ℝ => restartScaledProfile t) u := by
  have hsin : Real.sin (2 * u) ≠ 0 := by
    have hpos : 0 < 2 * u := by linarith
    have hbig : 0 < 2 * u ∧ 2 * u < Real.pi := ⟨hpos, by linarith [Real.pi_pos]⟩
    exact (Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2).ne'
  have h1 : ContinuousAt (fun t : ℝ => t) u := continuousAt_id
  have h2 : ContinuousAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2) u :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.pow 2
  have hsin2 : Real.sin (2 * u) ^ 2 ≠ 0 := by
    intro hz
    exact hsin ((sq_eq_zero_iff).mp hz)
  simpa [restartScaledProfile] using! h1.div h2 hsin2

private theorem abs_sub_lt_of_continuousAt {f : ℝ → ℝ} {x : ℝ} (hf : ContinuousAt f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : ℝ, |y - x| < δ → |f y - f x| < ε := by
  have hset : {z : ℝ | dist z (f x) < ε} ∈ nhds (f x) := by
    rw [Metric.mem_nhds_iff]
    refine ⟨ε, hε, ?_⟩
    intro y hy
    have hy' : dist y (f x) < ε := by
      simpa [Metric.mem_ball, dist_comm] using! hy
    exact hy'
  have hpre : {z : ℝ | dist z (f x) < ε} ∈ Filter.map f (nhds x) := hf hset
  obtain ⟨s, hs, hsub⟩ := Filter.mem_map_iff_exists_image.mp hpre
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨r, hr, hball⟩ := hs
  refine ⟨r, hr, fun y hy => ?_⟩
  have hmem : y ∈ s := hball (by
    rw [Metric.mem_ball]
    simpa [Real.dist_eq] using! hy)
  have hdist := hsub ⟨y, hmem, rfl⟩
  simpa [Real.dist_eq] using! hdist

theorem clause36_numeric_windows :
    (233113 : ℝ) / 100000 < Real.pi ∧ Real.pi < 31416 / 10000 ∧
      Real.pi / 4 > 58279 / 100000 ∧
      58278 / 100000 < restartScaledOptimum ∧
      restartScaledOptimum < 58279 / 100000 ∧
      69002 / 100000 < restartScaledExpectation ∧
      restartScaledExpectation < 69003 / 100000 := by
  have hc := clause36_source_constants
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  refine ⟨?_, ?_, ?_, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  · linarith
  · linarith
  · linarith

private theorem clause36_z_le_pi_of_three (θ : ℝ) (hθ : θ ≤ (Real.pi - restartOptimalAngle) / 4) :
    θ ≤ restartOptimalAngle / 2 := by
  have hz := restartOptimalAngle_spec
  have hpi : Real.pi ≤ 3 * restartOptimalAngle := by
    have hp := Real.pi_lt_d4
    linarith
  have hzpos : 0 < Real.pi - restartOptimalAngle := by
    have hp := Real.pi_gt_d4
    linarith
  linarith

private theorem restartRoundedDepth_window (θ : ℝ) (hθ : 0 < θ)
    (hθ2 : θ ≤ (Real.pi - restartOptimalAngle) / 4) :
    1 ≤ restartRoundedDepth θ restartOptimalAngle ∧
      restartRoundedDepth θ restartOptimalAngle ≤ restartWindowDepth θ := by
  have hz := restartOptimalAngle_spec
  have hzpos : 0 < restartOptimalAngle := by linarith [hz.2.1]
  have hzpi : 0 < Real.pi - restartOptimalAngle := by
    have hp := Real.pi_gt_d4
    linarith
  have hpos4 : 0 < 4 * θ := by positivity
  set q : ℝ := restartOptimalAngle / (4 * θ) + 1 / 2 with hq

  have hq1 : 1 ≤ q := by
    have hθz : θ ≤ restartOptimalAngle / 2 := clause36_z_le_pi_of_three θ hθ2
    have h3 : (2 : ℝ) * θ ≤ restartOptimalAngle := by linarith
    have h4 : restartOptimalAngle / (4 * θ) ≥ (2 * θ) / (4 * θ) :=
      (div_le_div_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 4 * θ))
    have h5 : (2 * θ) / (4 * θ) = 1 / 2 := by
      field_simp [ne_of_gt hpos4]
      ring
    rw [hq]
    linarith

  have hq2 : q ≤ Real.pi / (4 * θ) := by
    have h3 : (2 : ℝ) * θ ≤ Real.pi - restartOptimalAngle := by
      have := hθ2
      linarith
    have h4 : restartOptimalAngle + 2 * θ ≤ Real.pi := by linarith
    have h5 : (restartOptimalAngle + 2 * θ) / (4 * θ) ≤ Real.pi / (4 * θ) :=
      (div_le_div_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ 4 * θ))
    have h6 : (restartOptimalAngle + 2 * θ) / (4 * θ)
        = restartOptimalAngle / (4 * θ) + 1 / 2 := by
      field_simp [ne_of_gt hpos4]
      ring
    rw [hq]
    linarith
  have hone : restartRoundedDepth θ restartOptimalAngle = Nat.floor q := by
    rw [restartRoundedDepth, hq]
  refine ⟨?_, ?_⟩
  · rw [hone]
    exact (Nat.floor_pos).2 hq1
  · rw [hone]
    have h1 : (Nat.floor q : ℝ) ≤ q := Nat.floor_le (by linarith [hq1])
    have h3 : (Real.pi / (4 * θ) : ℝ) < (Nat.floor (Real.pi / (4 * θ)) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h4 : (Nat.floor q : ℝ) < (Nat.floor (Real.pi / (4 * θ)) : ℝ) + 1 := by linarith
    rw [restartWindowDepth]
    have h5 : Nat.floor q < Nat.floor (Real.pi / (4 * θ)) + 1 := by exact_mod_cast h4
    omega

private theorem clause36_phase_sine_lower :
    (restartOptimalAngle + Real.pi) / 8 < Real.sin (restartOptimalAngle / 2) ^ 2 := by
  obtain ⟨hpi1, hpi2, hpi4, hz4a, hz4b, hEa, hEb⟩ := clause36_numeric_windows
  have hz := restartOptimalAngle_spec
  have hE : restartScaledExpectation =
      restartOptimalAngle / (4 * Real.sin (restartOptimalAngle / 2) ^ 2) := rfl
  have hsinpos : 0 < Real.sin (restartOptimalAngle / 2) := by
    have hu' := restartOptimalAngle_half_mem
    have hpos : 0 < restartOptimalAngle / 2 := by linarith [hz.2.1]
    have hlt : restartOptimalAngle / 2 < Real.pi := by linarith [hu'.2, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hpos hlt
  have hden : 0 < 4 * Real.sin (restartOptimalAngle / 2) ^ 2 := by positivity
  have hEpos : 0 < restartScaledExpectation := by linarith [hEa]

  have hnum : 5 * ((233112 : ℝ) / 100000) > 14 * (69003 / 100000) := by norm_num
  have hbound2 : 5 * restartOptimalAngle > 14 * restartScaledExpectation := by
    have h1 := mul_lt_mul_of_pos_right hz.2.1 (by norm_num : (0 : ℝ) < 5)
    have h2 := mul_lt_mul_of_pos_left hEb (by norm_num : (0 : ℝ) < 14)
    nlinarith [h1, h2, hnum]

  have hE2 : restartScaledExpectation * (4 * Real.sin (restartOptimalAngle / 2) ^ 2)
      = restartOptimalAngle := by
    rw [hE]
    calc
      (restartOptimalAngle / (4 * Real.sin (restartOptimalAngle / 2) ^ 2))
            * (4 * Real.sin (restartOptimalAngle / 2) ^ 2)
          = (4 * Real.sin (restartOptimalAngle / 2) ^ 2)
              * (restartOptimalAngle / (4 * Real.sin (restartOptimalAngle / 2) ^ 2)) := by ring
      _ = restartOptimalAngle := mul_div_cancel₀ _ (ne_of_gt hden)
  have hkey : restartOptimalAngle =
      4 * restartScaledExpectation * Real.sin (restartOptimalAngle / 2) ^ 2 := by
    nlinarith [hE2]
  have hlt : (14 : ℝ) < 20 * Real.sin (restartOptimalAngle / 2) ^ 2 := by
    have h3 : 14 * restartScaledExpectation
        < (20 * Real.sin (restartOptimalAngle / 2) ^ 2) * restartScaledExpectation := by
      rw [hkey] at hbound2
      nlinarith [hbound2]
    exact lt_of_mul_lt_mul_right h3 hEpos.le
  have hsq : 7 / 10 < Real.sin (restartOptimalAngle / 2) ^ 2 := by linarith
  have hzpi : restartOptimalAngle + Real.pi < 233113 / 100000 + 31416 / 10000 := by
    linarith [hz.2.2, hpi1, hpi2]
  have hnum2 : ((233113 : ℝ) / 100000 + 31416 / 10000) / 8 < 7 / 10 := by norm_num
  linarith

private theorem restartProfile_rounded_le (θ : ℝ) (hθ : 0 < θ)
    (hθ2 : θ ≤ (Real.pi - restartOptimalAngle) / 4) :
    restartProfile θ (restartRoundedDepth θ restartOptimalAngle : ℝ) ≤ 1 / θ := by
  have hnear := restartRoundedDepth_nearest θ hθ
  have hz := restartOptimalAngle_spec
  have hhalf := restartOptimalAngle_half_mem
  have hsinlo := clause36_phase_sine_lower
  have hpos4 : 0 < 4 * θ := by positivity
  set jj : ℝ := (restartRoundedDepth θ restartOptimalAngle : ℝ) with hjj

  have hA : |jj * (4 * θ) - restartOptimalAngle| ≤ 2 * θ := by
    have habs : |jj - restartOptimalAngle / (4 * θ)| * (4 * θ)
        = |(jj - restartOptimalAngle / (4 * θ)) * (4 * θ)| := by
      rw [abs_mul, abs_of_pos hpos4]
    have hkey : (jj - restartOptimalAngle / (4 * θ)) * (4 * θ)
        = jj * (4 * θ) - restartOptimalAngle := by
      field_simp [ne_of_gt hpos4] <;> ring
    rw [hkey] at habs
    have h2 := mul_le_mul_of_nonneg_left hnear (by linarith : (0 : ℝ) ≤ 4 * θ)
    rw [hjj] at h2
    linarith
  have hA' := (abs_le).mp hA
  have hAlo : -2 * θ ≤ jj * (4 * θ) - restartOptimalAngle := by linarith [hA'.1]
  have hAhi : jj * (4 * θ) - restartOptimalAngle ≤ 2 * θ := by linarith [hA'.2]

  have hphase_lo : restartOptimalAngle / 2 ≤ (2 * jj + 1) * θ := by
    have h2 : (2 * jj + 1) * θ = jj * (4 * θ) / 2 + θ := by ring
    rw [h2]
    nlinarith [hAlo]
  have hphase_hi : (2 * jj + 1) * θ ≤ Real.pi / 2 := by
    have h2 : (2 * jj + 1) * θ = jj * (4 * θ) / 2 + θ := by ring
    have h4 : (2 : ℝ) * θ ≤ Real.pi - restartOptimalAngle := by
      have := hθ2
      linarith
    rw [h2]
    nlinarith [hAhi]

  have hsin : Real.sin ((2 * jj + 1) * θ) ≥ Real.sin (restartOptimalAngle / 2) := by
    have hmono : MonotoneOn Real.sin (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
      Real.strictMonoOn_sin.monotoneOn
    have h1 : restartOptimalAngle / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have h2 : (2 * jj + 1) * θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    exact hmono h1 h2 (by linarith)
  have hsinpos : 0 ≤ Real.sin (restartOptimalAngle / 2) := by
    have hmem : (restartOptimalAngle / 2 : ℝ) ∈ Set.Icc 0 Real.pi := by
      constructor <;> linarith [Real.pi_pos, hz.2.1]
    exact Real.sin_nonneg_of_mem_Icc hmem

  have hscale : jj * θ = restartScaledOptimum + (jj * (4 * θ) - restartOptimalAngle) / 4 := by
    rw [restartScaledOptimum]
    ring
  have hbudget : jj * θ ≤ restartScaledOptimum + θ / 2 := by
    rw [hscale]
    nlinarith [hAhi]
  have hzpi8 : restartScaledOptimum + θ / 2 ≤ (restartOptimalAngle + Real.pi) / 8 := by
    have h4 : (2 : ℝ) * θ ≤ Real.pi - restartOptimalAngle := by
      have := hθ2
      linarith
    rw [restartScaledOptimum]
    nlinarith
  have hmain : jj * θ ≤ Real.sin ((2 * jj + 1) * θ) ^ 2 := by
    have h1 : jj * θ ≤ (restartOptimalAngle + Real.pi) / 8 := by linarith [hbudget, hzpi8]
    have h2 : Real.sin (restartOptimalAngle / 2) ^ 2
        ≤ Real.sin ((2 * jj + 1) * θ) ^ 2 := by
      nlinarith [hsin, hsinpos]
    linarith
  rw [restartProfile, restartExpectedIterations]
  rw [hjj]
  rw [le_div_iff₀ hθ]
  have hden : 0 < Real.sin ((2 * jj + 1) * θ) ^ 2 := by
    have hbig : 0 < (2 * jj + 1) * θ ∧ (2 * jj + 1) * θ < Real.pi := by
      constructor <;> linarith [hphase_lo, hphase_hi, Real.pi_pos]
    have hsinpos' : 0 < Real.sin ((2 * jj + 1) * θ) := Real.sin_pos_of_pos_of_lt_pi hbig.1 hbig.2
    positivity
  have hkey2 : jj / Real.sin ((2 * jj + 1) * θ) ^ 2 * θ
      = (jj * θ) / Real.sin ((2 * jj + 1) * θ) ^ 2 := by
    field_simp [ne_of_gt hden] <;> ring
  rw [hkey2, div_le_one hden]
  exact hmain

private theorem restartIntegerOptimum_scaled_floor (θ : ℝ) (hθ : 0 < θ)
    (hθ2 : θ ≤ (Real.pi - restartOptimalAngle) / 4) :
    1 / 9 ≤ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ := by
  have hz := restartOptimalAngle_spec
  have hzpos : 0 < restartOptimalAngle := by linarith [hz.2.1]
  have hθ4 : θ ≤ Real.pi / 4 := by linarith [hθ2]
  have hM : 0 < restartWindowDepth θ := by
    obtain ⟨h1, _, _⟩ := restartWindowDepth_spec θ hθ hθ4
    omega
  obtain ⟨hj1, hj2, hj3⟩ := restartIntegerOptimum_spec θ (restartWindowDepth θ) hM
  set js : ℝ := (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) with hjs
  have hjs1 : (1 : ℝ) ≤ js := by
    rw [hjs]
    exact_mod_cast hj1

  have hj0win := restartRoundedDepth_window θ hθ hθ2
  have hge := restartProfile_ge_min θ (restartWindowDepth θ) hM
    (restartRoundedDepth θ restartOptimalAngle) hj0win.1 hj0win.2
  have hbest : restartProfile θ js ≤ restartProfile θ (restartRoundedDepth θ restartOptimalAngle : ℝ) := by
    rw [hjs]
    linarith [hge, hj3]
  have hrounded := restartProfile_rounded_le θ hθ hθ2

  have hphase_pos : 0 < (2 * js + 1) * θ := by
    have h2 : (0 : ℝ) < 2 * js + 1 := by linarith
    exact mul_pos h2 hθ
  have hphase_lt : (2 * js + 1) * θ < Real.pi := by
    obtain ⟨_, h2, _⟩ := restartWindowDepth_spec θ hθ hθ4
    have h3 : js ≤ (restartWindowDepth θ : ℝ) := by
      rw [hjs]
      exact_mod_cast hj2
    have h4 : js * θ ≤ (restartWindowDepth θ : ℝ) * θ := mul_le_mul_of_nonneg_right h3 hθ.le
    have h5 : 2 * (js * θ) + θ ≤ 2 * ((restartWindowDepth θ : ℝ) * θ) + θ := by linarith [h4]
    have h6 : (2 * js + 1) * θ = 2 * (js * θ) + θ := by ring
    rw [h6]
    linarith
  have hsinpos : 0 < Real.sin ((2 * js + 1) * θ) ^ 2 := by
    have h := Real.sin_pos_of_pos_of_lt_pi hphase_pos hphase_lt
    positivity

  have hlow : restartProfile θ js ≥ js / ((2 * js + 1) * θ) ^ 2 := by
    rw [hjs, restartProfile, restartExpectedIterations]
    have hsin : Real.sin ((2 * js + 1) * θ) ^ 2 ≤ ((2 * js + 1) * θ) ^ 2 := by
      have habs : |Real.sin ((2 * js + 1) * θ)| ≤ |(2 * js + 1) * θ| := Real.abs_sin_le_abs
      have hsq := mul_self_le_mul_self (abs_nonneg _) habs
      nlinarith [sq_abs (Real.sin ((2 * js + 1) * θ)), sq_abs ((2 * js + 1) * θ)]
    have hjspos : 0 ≤ js := by linarith
    apply (div_le_div_iff₀ (by positivity : 0 < ((2 * js + 1) * θ) ^ 2) hsinpos).2
    exact mul_le_mul_of_nonneg_left hsin hjspos

  have hcomb : js / ((2 * js + 1) * θ) ^ 2 ≤ 1 / θ := by
    calc
      js / ((2 * js + 1) * θ) ^ 2 ≤ restartProfile θ js := hlow
      _ ≤ restartProfile θ (restartRoundedDepth θ restartOptimalAngle : ℝ) := hbest
      _ ≤ 1 / θ := hrounded
  have hstep1 : (js / ((2 * js + 1) * θ) ^ 2) * θ ≤ 1 := (le_div_iff₀ hθ).1 hcomb
  have hstep2 : (js / ((2 * js + 1) * θ) ^ 2) * θ = (js * θ) / ((2 * js + 1) * θ) ^ 2 := by
    field_simp <;> ring
  rw [hstep2, div_le_one (by positivity : 0 < ((2 * js + 1) * θ) ^ 2)] at hstep1

  have hφ : ((2 * js + 1) * θ) ^ 2 = (2 * (js * θ) + θ) ^ 2 := by ring
  rw [hφ] at hstep1
  have hθu : θ ≤ js * θ := by
    have h3 : θ * 1 ≤ θ * js := mul_le_mul_of_nonneg_left hjs1 hθ.le
    nlinarith [h3]
  have hpos : 0 < js * θ := by
    have h1 : (1 : ℝ) ≤ js := hjs1
    exact mul_pos (by linarith) (by linarith)
  have h9 : (2 * (js * θ) + θ) ^ 2 ≤ 9 * (js * θ) ^ 2 := by
    have hbound : 2 * (js * θ) + θ ≤ 3 * (js * θ) := by linarith
    have hmul : 0 ≤ (3 * (js * θ) - (2 * (js * θ) + θ))
        * ((2 * (js * θ) + θ) + 3 * (js * θ)) :=
      mul_nonneg (sub_nonneg.mpr hbound) (by linarith [hpos, hθ])
    nlinarith [hmul]
  have h10 : js * θ * 1 ≤ js * θ * (9 * (js * θ)) := by nlinarith [hstep1, h9]
  have h11 : 1 ≤ 9 * (js * θ) := le_of_mul_le_mul_left h10 hpos
  rw [hjs]
  linarith

private theorem scaledProfile_edge_above :
    restartScaledProfile (Real.pi / 4) > restartScaledProfile restartScaledOptimum := by
  have h := clause36_source_constants
  have hedge : restartScaledProfile (Real.pi / 4) = Real.pi / 4 := by
    rw [restartScaledProfile]
    have hsin : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have hhalf : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [hhalf, hsin]
    ring
  rw [hedge, scaledProfile_optimum_value]
  have hp := Real.pi_gt_d4
  linarith

private theorem scaledProfile_ge_optimum_closed (u : ℝ) (hu : 0 < u)
    (hu2 : u ≤ Real.pi / 4) :
    restartScaledProfile u ≥ restartScaledProfile restartScaledOptimum := by
  by_cases hlt : u < Real.pi / 4
  · exact (scaledProfile_min_unique u hu hlt).1
  · have heq : u = Real.pi / 4 := by linarith
    rw [heq]
    linarith [scaledProfile_edge_above]

private theorem min6_le {a b c d e f g : ℝ} (h1 : a ≤ b) (h2 : a ≤ c) (h3 : a ≤ d)
    (h4 : a ≤ e) (h5 : a ≤ f) (h6 : a ≤ g) :
    a ≤ min b (min c (min d (min e (min f g)))) := by
  refine le_min h1 ?_
  refine le_min h2 ?_
  refine le_min h3 ?_
  refine le_min h4 ?_
  exact le_min h5 h6

private theorem clause36_scaled_setup (θ : ℝ) (hθ : 0 < θ)
    (hθ4 : θ ≤ Real.pi / 4) (hθz : θ ≤ (Real.pi - restartOptimalAngle) / 4)
    (hθA : θ ≤ 2 * restartScaledOptimum - 1 / 8)
    (hθB : θ ≤ 2 * (Real.pi / 4 - restartScaledOptimum)) :
    (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ
        ≤ Real.pi / 4 ∧
      1 / 16 ≤ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ ∧
      1 / 16 ≤ (restartRoundedDepth θ restartOptimalAngle : ℝ) * θ ∧
      (restartRoundedDepth θ restartOptimalAngle : ℝ) * θ ≤ Real.pi / 4 ∧
      |(restartRoundedDepth θ restartOptimalAngle : ℝ) * θ - restartScaledOptimum| ≤ θ / 2 := by
  have hM : 0 < restartWindowDepth θ := by
    obtain ⟨h1, _, _⟩ := restartWindowDepth_spec θ hθ hθ4
    omega
  obtain ⟨hj1, hj2, _⟩ := restartIntegerOptimum_spec θ (restartWindowDepth θ) hM
  obtain ⟨_, hMθ, _⟩ := restartWindowDepth_spec θ hθ hθ4

  have h1 : (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ)
      ≤ (restartWindowDepth θ : ℝ) := by exact_mod_cast hj2
  have h2 : (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ
      ≤ (restartWindowDepth θ : ℝ) * θ := mul_le_mul_of_nonneg_right h1 hθ.le
  have hfloor := restartIntegerOptimum_scaled_floor θ hθ hθz

  have hnear := restartRoundedDepth_nearest θ hθ
  have hu0 : |(restartRoundedDepth θ restartOptimalAngle : ℝ) * θ - restartScaledOptimum|
      ≤ θ / 2 := by
    have hpos4 : 0 < 4 * θ := by positivity
    have hkey : (restartRoundedDepth θ restartOptimalAngle : ℝ) * θ - restartScaledOptimum
        = ((restartRoundedDepth θ restartOptimalAngle : ℝ) - restartOptimalAngle / (4 * θ)) * θ := by
      have hq : restartOptimalAngle / (4 * θ) * θ = restartScaledOptimum := by
        rw [restartScaledOptimum]
        field_simp [ne_of_gt hpos4]
      linarith
    have habs : |((restartRoundedDepth θ restartOptimalAngle : ℝ)
          - restartOptimalAngle / (4 * θ)) * θ|
        = |(restartRoundedDepth θ restartOptimalAngle : ℝ)
          - restartOptimalAngle / (4 * θ)| * θ := by
      rw [abs_mul, abs_of_pos hθ]
    rw [hkey, habs]
    have h3 := mul_le_mul_of_nonneg_left hnear hθ.le
    linarith
  have hu0_lo : restartScaledOptimum - θ / 2
      ≤ (restartRoundedDepth θ restartOptimalAngle : ℝ) * θ := by
    have := (abs_le).mp hu0
    linarith
  have hu0_hi : (restartRoundedDepth θ restartOptimalAngle : ℝ) * θ
      ≤ restartScaledOptimum + θ / 2 := by
    have := (abs_le).mp hu0
    linarith
  have hu0_floor : 1 / 16 ≤ (restartRoundedDepth θ restartOptimalAngle : ℝ) * θ := by
    linarith
  have hu0_le : (restartRoundedDepth θ restartOptimalAngle : ℝ) * θ ≤ Real.pi / 4 := by
    linarith
  refine ⟨?_, ?_, hu0_floor, hu0_le, hu0⟩
  · linarith
  · linarith

private theorem clause36_integer_optimum_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ
        < restartScaledOptimum + ε := by
  by_cases hz4 : restartScaledOptimum + ε ≤ Real.pi / 4
  · set gap : ℝ := restartScaledProfile (restartScaledOptimum + ε)
      - restartScaledProfile restartScaledOptimum with hgapdef
    have hgap : 0 < gap := by
      rw [hgapdef]
      by_cases hlt : restartScaledOptimum + ε < Real.pi / 4
      · obtain ⟨h1, h2⟩ := scaledProfile_min_unique (restartScaledOptimum + ε)
          (by linarith [restartScaledOptimum_mem.1]) hlt
        have hne : restartScaledOptimum + ε ≠ restartScaledOptimum := by linarith
        linarith [h2 hne]
      · have heq : restartScaledOptimum + ε = Real.pi / 4 := by linarith
        rw [heq]
        linarith [scaledProfile_edge_above]
    have hhalf : 0 < gap / 2 := by linarith
    obtain ⟨δS, hδS, hcont⟩ := abs_sub_lt_of_continuousAt
      (scaledProfile_continuousAt restartScaledOptimum restartScaledOptimum_mem.1
        restartScaledOptimum_mem.2) hhalf
    have hpos1 : 0 < 2 * δS := by linarith
    have hpos2 : 0 < Real.pi / 4 := by
      have := Real.pi_pos
      linarith
    have hpos3 : 0 < (Real.pi - restartOptimalAngle) / 4 := by
      have := Real.pi_gt_d4
      have hz := restartOptimalAngle_spec
      linarith
    have hpos4 : 0 < 2 * restartScaledOptimum - 1 / 8 := by
      obtain ⟨_, _, _, h4, _, _, _⟩ := clause36_numeric_windows
      linarith
    have hpos5 : 0 < 2 * (Real.pi / 4 - restartScaledOptimum) := by
      obtain ⟨_, _, h3, _, _, _, _⟩ := clause36_numeric_windows
      linarith
    have hpos6 : 0 < gap / (4 * restartScaledSlack) := by
      have hslack : 0 < restartScaledSlack := by
        unfold restartScaledSlack
        have hsin : 0 < Real.sin (1 / 8) := by
          have h1 : (0 : ℝ) < 1 / 8 := by norm_num
          have h2 : (1 / 8 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
          exact Real.sin_pos_of_pos_of_lt_pi h1 h2
        have hpi : 0 < Real.pi / 4 := by
          have := Real.pi_pos
          linarith
        have hpow : 0 < Real.sin (1 / 8) ^ 4 := by positivity
        exact div_pos hpi hpow
      exact div_pos hgap (by positivity : 0 < 4 * restartScaledSlack)
    set δ : ℝ := min (2 * δS) (min (Real.pi / 4) (min ((Real.pi - restartOptimalAngle) / 4) (min (2 * restartScaledOptimum - 1 / 8) (min (2 * (Real.pi / 4 - restartScaledOptimum)) (gap / (4 * restartScaledSlack)))))) with hδ
    refine ⟨δ, ?_, ?_⟩
    · rw [hδ]
      exact lt_min hpos1 (lt_min hpos2 (lt_min hpos3 (lt_min hpos4 (lt_min hpos5 hpos6))))
    · intro θ hθ hθlt
      have hδ1 : δ ≤ 2 * δS := by rw [hδ]; exact min_le_left _ _
      have hδ2 : δ ≤ Real.pi / 4 := by
        rw [hδ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
      have hδ3 : δ ≤ (Real.pi - restartOptimalAngle) / 4 := by
        rw [hδ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      have hδ4 : δ ≤ 2 * restartScaledOptimum - 1 / 8 := by
        rw [hδ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))
      have hδ5 : δ ≤ 2 * (Real.pi / 4 - restartScaledOptimum) := by
        rw [hδ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
      have hδ6 : δ ≤ gap / (4 * restartScaledSlack) := by
        rw [hδ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
      have hθ4 : θ ≤ Real.pi / 4 := by linarith
      have hθz : θ ≤ (Real.pi - restartOptimalAngle) / 4 := by linarith
      have hθA : θ ≤ 2 * restartScaledOptimum - 1 / 8 := by linarith
      have hθB : θ ≤ 2 * (Real.pi / 4 - restartScaledOptimum) := by linarith
      have hθC : θ < 2 * δS := by linarith
      have hθD : θ < gap / (4 * restartScaledSlack) := by linarith
      obtain ⟨hu_le, hu_floor, hu0_floor, hu0_le, hu0_near⟩ :=
        clause36_scaled_setup θ hθ hθ4 hθz hθA hθB

      have hM : 0 < restartWindowDepth θ := by
        obtain ⟨h1, _, _⟩ := restartWindowDepth_spec θ hθ hθ4
        omega
      have hj0win := restartRoundedDepth_window θ hθ hθz
      have hge := restartProfile_ge_min θ (restartWindowDepth θ) hM
        (restartRoundedDepth θ restartOptimalAngle) hj0win.1 hj0win.2
      obtain ⟨_, _, hj3⟩ := restartIntegerOptimum_spec θ (restartWindowDepth θ) hM
      have hbest : restartProfile θ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ)
          ≤ restartProfile θ (restartRoundedDepth θ restartOptimalAngle : ℝ) := by
        linarith
      have hSmin : restartScaledProfileθ
            ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ) θ
          ≤ restartScaledProfileθ ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ) θ := by
        rw [scaledProfileθ_eq_profile, scaledProfileθ_eq_profile]
        have := mul_le_mul_of_nonneg_left hbest hθ.le
        linarith

      have hclose_u : |restartScaledProfileθ
              ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ) θ
            - restartScaledProfile ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)|
          ≤ restartScaledSlack * θ :=
        scaledProfile_close_wide θ ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)
          hθ hθ4 hu_floor hu_le
      have hclose_u0 : |restartScaledProfileθ
              ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ) θ
            - restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)|
          ≤ restartScaledSlack * θ :=
        scaledProfile_close_wide θ ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
          hθ hθ4 hu0_floor hu0_le
      have hval : restartScaledProfile ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)
          ≤ restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
            + 2 * restartScaledSlack * θ := by
        have hcu := (abs_le).mp hclose_u
        have hcu0 := (abs_le).mp hclose_u0
        linarith
      have hcont_u0 : |restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
            - restartScaledProfile restartScaledOptimum| < gap / 2 := by
        have h1 : |(restartRoundedDepth θ restartOptimalAngle : ℝ) * θ
            - restartScaledOptimum| < δS := by
          linarith
        exact hcont _ h1

      have hu_upper : (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ
          < restartScaledOptimum + ε := by
        by_contra hcon
        have hge : restartScaledOptimum + ε
            ≤ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ := le_of_not_gt hcon
        have hmono : restartScaledProfile (restartScaledOptimum + ε)
            ≤ restartScaledProfile ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ) := by
          have ha : restartScaledOptimum + ε ∈ Set.Icc restartScaledOptimum (Real.pi / 4) := by
            constructor
            · linarith
            · exact hz4
          have hb : (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ
              ∈ Set.Icc restartScaledOptimum (Real.pi / 4) := by
            constructor
            · linarith
            · exact hu_le
          exact scaledProfile_strictMonoOn_inc.monotoneOn ha hb hge
        have hcont_u0' : restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
            - restartScaledProfile restartScaledOptimum < gap / 2 :=
          (abs_lt).mp hcont_u0 |>.2
        have h2 : 2 * restartScaledSlack * θ < gap / 2 := by
          have hslack : 0 < restartScaledSlack := by
            unfold restartScaledSlack
            have hsin : 0 < Real.sin (1 / 8) := by
              have h1 : (0 : ℝ) < 1 / 8 := by norm_num
              have h2 : (1 / 8 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
              exact Real.sin_pos_of_pos_of_lt_pi h1 h2
            have hpi : 0 < Real.pi / 4 := by
              have := Real.pi_pos
              linarith
            have hpow : 0 < Real.sin (1 / 8) ^ 4 := by positivity
            exact div_pos hpi hpow
          have h3 : θ * (4 * restartScaledSlack) < gap := by
            exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * restartScaledSlack)).1 hθD
          linarith
        linarith
      exact hu_upper
  · refine ⟨Real.pi / 4, by positivity, ?_⟩
    intro θ hθ hθlt
    have hθ4 : θ ≤ Real.pi / 4 := by linarith
    obtain ⟨_, hMθ, _⟩ := restartWindowDepth_spec θ hθ hθ4
    have h1 : (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ)
        ≤ (restartWindowDepth θ : ℝ) := by
      have hM : 0 < restartWindowDepth θ := by
        obtain ⟨h2, _, _⟩ := restartWindowDepth_spec θ hθ hθ4
        omega
      obtain ⟨_, hj2, _⟩ := restartIntegerOptimum_spec θ (restartWindowDepth θ) hM
      exact_mod_cast hj2
    have h2 : (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ
        ≤ Real.pi / 4 := by
      have := mul_le_mul_of_nonneg_right h1 hθ.le
      linarith
    linarith

private theorem clause36_integer_optimum_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      restartScaledOptimum - ε
        < (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ := by
  by_cases hz4 : 1 / 16 ≤ restartScaledOptimum - ε
  · set gap : ℝ := restartScaledProfile (restartScaledOptimum - ε)
      - restartScaledProfile restartScaledOptimum with hgapdef
    have hgap : 0 < gap := by
      rw [hgapdef]
      obtain ⟨h1, h2⟩ := scaledProfile_min_unique (restartScaledOptimum - ε)
        (by linarith) (by linarith [restartScaledOptimum_mem.2])
      have hne : restartScaledOptimum - ε ≠ restartScaledOptimum := by linarith
      linarith [h2 hne]
    have hhalf : 0 < gap / 2 := by linarith
    obtain ⟨δS, hδS, hcont⟩ := abs_sub_lt_of_continuousAt
      (scaledProfile_continuousAt restartScaledOptimum restartScaledOptimum_mem.1
        restartScaledOptimum_mem.2) hhalf
    have hpos1 : 0 < 2 * δS := by linarith
    have hpos2 : 0 < Real.pi / 4 := by
      have := Real.pi_pos
      linarith
    have hpos3 : 0 < (Real.pi - restartOptimalAngle) / 4 := by
      have := Real.pi_gt_d4
      have hz := restartOptimalAngle_spec
      linarith
    have hpos4 : 0 < 2 * restartScaledOptimum - 1 / 8 := by
      obtain ⟨_, _, _, h4, _, _, _⟩ := clause36_numeric_windows
      linarith
    have hpos5 : 0 < 2 * (Real.pi / 4 - restartScaledOptimum) := by
      obtain ⟨_, _, h3, _, _, _, _⟩ := clause36_numeric_windows
      linarith
    have hslack : 0 < restartScaledSlack := by
      unfold restartScaledSlack
      have hsin : 0 < Real.sin (1 / 8) := by
        have h1 : (0 : ℝ) < 1 / 8 := by norm_num
        have h2 : (1 / 8 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
        exact Real.sin_pos_of_pos_of_lt_pi h1 h2
      have hpi : 0 < Real.pi / 4 := by
        have := Real.pi_pos
        linarith
      have hpow : 0 < Real.sin (1 / 8) ^ 4 := by positivity
      exact div_pos hpi hpow
    have hpos6 : 0 < gap / (4 * restartScaledSlack) :=
      div_pos hgap (by positivity : 0 < 4 * restartScaledSlack)
    set δ : ℝ := min (2 * δS) (min (Real.pi / 4) (min ((Real.pi - restartOptimalAngle) / 4) (min (2 * restartScaledOptimum - 1 / 8) (min (2 * (Real.pi / 4 - restartScaledOptimum)) (gap / (4 * restartScaledSlack)))))) with hδ
    refine ⟨δ, ?_, ?_⟩
    · rw [hδ]
      exact lt_min hpos1 (lt_min hpos2 (lt_min hpos3 (lt_min hpos4 (lt_min hpos5 hpos6))))
    · intro θ hθ hθlt
      have hδ1 : δ ≤ 2 * δS := by rw [hδ]; exact min_le_left _ _
      have hδ2 : δ ≤ Real.pi / 4 := by
        rw [hδ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
      have hδ3 : δ ≤ (Real.pi - restartOptimalAngle) / 4 := by
        rw [hδ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      have hδ4 : δ ≤ 2 * restartScaledOptimum - 1 / 8 := by
        rw [hδ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))
      have hδ5 : δ ≤ 2 * (Real.pi / 4 - restartScaledOptimum) := by
        rw [hδ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
      have hδ6 : δ ≤ gap / (4 * restartScaledSlack) := by
        rw [hδ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
      have hθ4 : θ ≤ Real.pi / 4 := by linarith
      have hθz : θ ≤ (Real.pi - restartOptimalAngle) / 4 := by linarith
      have hθA : θ ≤ 2 * restartScaledOptimum - 1 / 8 := by linarith
      have hθB : θ ≤ 2 * (Real.pi / 4 - restartScaledOptimum) := by linarith
      have hθC : θ < 2 * δS := by linarith
      have hθD : θ < gap / (4 * restartScaledSlack) := by linarith
      obtain ⟨hu_le, hu_floor, hu0_floor, hu0_le, hu0_near⟩ :=
        clause36_scaled_setup θ hθ hθ4 hθz hθA hθB
      have hM : 0 < restartWindowDepth θ := by
        obtain ⟨h1, _, _⟩ := restartWindowDepth_spec θ hθ hθ4
        omega
      have hj0win := restartRoundedDepth_window θ hθ hθz
      have hge := restartProfile_ge_min θ (restartWindowDepth θ) hM
        (restartRoundedDepth θ restartOptimalAngle) hj0win.1 hj0win.2
      obtain ⟨_, _, hj3⟩ := restartIntegerOptimum_spec θ (restartWindowDepth θ) hM
      have hbest : restartProfile θ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ)
          ≤ restartProfile θ (restartRoundedDepth θ restartOptimalAngle : ℝ) := by
        linarith
      have hSmin : restartScaledProfileθ
            ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ) θ
          ≤ restartScaledProfileθ ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ) θ := by
        rw [scaledProfileθ_eq_profile, scaledProfileθ_eq_profile]
        have := mul_le_mul_of_nonneg_left hbest hθ.le
        linarith
      have hclose_u : |restartScaledProfileθ
              ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ) θ
            - restartScaledProfile ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)|
          ≤ restartScaledSlack * θ :=
        scaledProfile_close_wide θ ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)
          hθ hθ4 hu_floor hu_le
      have hclose_u0 : |restartScaledProfileθ
              ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ) θ
            - restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)|
          ≤ restartScaledSlack * θ :=
        scaledProfile_close_wide θ ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
          hθ hθ4 hu0_floor hu0_le
      have hval : restartScaledProfile ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)
          ≤ restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
            + 2 * restartScaledSlack * θ := by
        have hcu := (abs_le).mp hclose_u
        have hcu0 := (abs_le).mp hclose_u0
        linarith
      have hcont_u0 : |restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
            - restartScaledProfile restartScaledOptimum| < gap / 2 := by
        have h1 : |(restartRoundedDepth θ restartOptimalAngle : ℝ) * θ
            - restartScaledOptimum| < δS := by
          linarith
        exact hcont _ h1

      have hu_lower : restartScaledOptimum - ε
          < (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ := by
        by_contra hcon
        have hle : (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ
            ≤ restartScaledOptimum - ε := le_of_not_gt hcon
        have hmono : -restartScaledProfile ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)
            ≤ -restartScaledProfile (restartScaledOptimum - ε) := by
          have ha : (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ
              ∈ Set.Icc (1 / 16) restartScaledOptimum := by
            constructor
            · exact hu_floor
            · linarith
          have hb : restartScaledOptimum - ε
              ∈ Set.Icc (1 / 16) restartScaledOptimum := by
            constructor
            · exact hz4
            · linarith
          exact scaledProfile_strictMonoOn_dec.monotoneOn ha hb hle
        have hcont_u0' : restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
            - restartScaledProfile restartScaledOptimum < gap / 2 :=
          (abs_lt).mp hcont_u0 |>.2
        have h2 : 2 * restartScaledSlack * θ < gap / 2 := by
          have h3 : θ * (4 * restartScaledSlack) < gap := by
            exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * restartScaledSlack)).1 hθD
          linarith
        linarith
      exact hu_lower
  · refine ⟨(Real.pi - restartOptimalAngle) / 4, by
      have := Real.pi_gt_d4
      have hz := restartOptimalAngle_spec
      linarith, ?_⟩
    intro θ hθ hθlt
    have hθ4 : θ ≤ Real.pi / 4 := by
      have := Real.pi_gt_d4
      have hz := restartOptimalAngle_spec
      linarith
    have hθz : θ ≤ (Real.pi - restartOptimalAngle) / 4 := by linarith
    have hfloor := restartIntegerOptimum_scaled_floor θ hθ hθz
    linarith

theorem clause36_integer_optimum_tendsto :
    Filter.Tendsto (fun θ : ℝ => (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)
      (𝓝[>] 0) (𝓝 restartScaledOptimum) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δup, hδup, hup⟩ := clause36_integer_optimum_upper ε hε
  obtain ⟨δlo, hδlo, hlo⟩ := clause36_integer_optimum_lower ε hε
  refine ⟨min δup δlo, lt_min hδup hδlo, ?_⟩
  intro θ hθ hθdist
  have hθpos : 0 < θ := by simpa only [Set.mem_Ioi] using! hθ
  have hθlt : θ < min δup δlo := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hθpos] at hθdist
    exact hθdist
  have h1 : (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ
      < restartScaledOptimum + ε := hup θ hθ (lt_of_lt_of_le hθlt (min_le_left _ _))
  have h2 : restartScaledOptimum - ε
      < (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ :=
    hlo θ hθ (lt_of_lt_of_le hθlt (min_le_right _ _))
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem clause36_expected_iterations_tendsto :
    Filter.Tendsto (fun θ : ℝ => θ * restartProfile θ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ))
      (𝓝[>] 0) (𝓝 restartScaledExpectation) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε

  have heps : 0 < min ε (ε / 2) := lt_min hε (by linarith)
  have hminε : min ε (ε / 2) ≤ ε := min_le_left _ _
  have hminε2 : min ε (ε / 2) ≤ ε / 2 := min_le_right _ _
  obtain ⟨δS, hδS, hcont⟩ := abs_sub_lt_of_continuousAt
    (scaledProfile_continuousAt restartScaledOptimum restartScaledOptimum_mem.1
      restartScaledOptimum_mem.2) heps
  have hslack : 0 < restartScaledSlack := by
    unfold restartScaledSlack
    have hsin : 0 < Real.sin (1 / 8) := by
      have h1 : (0 : ℝ) < 1 / 8 := by norm_num
      have h2 : (1 / 8 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
      exact Real.sin_pos_of_pos_of_lt_pi h1 h2
    have hpi : 0 < Real.pi / 4 := by
      have := Real.pi_pos
      linarith
    have hpow : 0 < Real.sin (1 / 8) ^ 4 := by positivity
    exact div_pos hpi hpow
  have hpos1 : 0 < 2 * δS := by linarith
  have hpos2 : 0 < Real.pi / 4 := by
    have := Real.pi_pos
    linarith
  have hpos3 : 0 < (Real.pi - restartOptimalAngle) / 4 := by
    have := Real.pi_gt_d4
    have hz := restartOptimalAngle_spec
    linarith
  have hpos4 : 0 < 2 * restartScaledOptimum - 1 / 8 := by
    obtain ⟨_, _, _, h4, _, _, _⟩ := clause36_numeric_windows
    linarith
  have hpos5 : 0 < 2 * (Real.pi / 4 - restartScaledOptimum) := by
    obtain ⟨_, _, h3, _, _, _, _⟩ := clause36_numeric_windows
    linarith
  have hpos6 : 0 < min ε (ε / 2) / (2 * restartScaledSlack) :=
    div_pos heps (by positivity : 0 < 2 * restartScaledSlack)
  set δ : ℝ := min (2 * δS) (min (Real.pi / 4) (min ((Real.pi - restartOptimalAngle) / 4) (min (2 * restartScaledOptimum - 1 / 8) (min (2 * (Real.pi / 4 - restartScaledOptimum)) (min ε (ε / 2) / (2 * restartScaledSlack)))))) with hδ
  refine ⟨δ, ?_, ?_⟩
  · rw [hδ]
    exact lt_min hpos1 (lt_min hpos2 (lt_min hpos3 (lt_min hpos4 (lt_min hpos5 hpos6))))
  · intro θ hθ hθdist
    have hθpos : 0 < θ := by simpa only [Set.mem_Ioi] using! hθ
    have hθlt : θ < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hθpos] at hθdist
      exact hθdist
    have hδ1 : δ ≤ 2 * δS := by rw [hδ]; exact min_le_left _ _
    have hδ2 : δ ≤ Real.pi / 4 := by
      rw [hδ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ3 : δ ≤ (Real.pi - restartOptimalAngle) / 4 := by
      rw [hδ]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hδ4 : δ ≤ 2 * restartScaledOptimum - 1 / 8 := by
      rw [hδ]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hδ5 : δ ≤ 2 * (Real.pi / 4 - restartScaledOptimum) := by
      rw [hδ]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    have hδ6 : δ ≤ min ε (ε / 2) / (2 * restartScaledSlack) := by
      rw [hδ]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
    have hθ4 : θ ≤ Real.pi / 4 := by linarith
    have hθz : θ ≤ (Real.pi - restartOptimalAngle) / 4 := by linarith
    have hθA : θ ≤ 2 * restartScaledOptimum - 1 / 8 := by linarith
    have hθB : θ ≤ 2 * (Real.pi / 4 - restartScaledOptimum) := by linarith
    have hθC : θ < 2 * δS := by linarith
    have hθE : θ < min ε (ε / 2) / (2 * restartScaledSlack) := by linarith
    obtain ⟨hu_le, hu_floor, hu0_floor, hu0_le, hu0_near⟩ :=
      clause36_scaled_setup θ hθ hθ4 hθz hθA hθB
    have hM : 0 < restartWindowDepth θ := by
      obtain ⟨h1, _, _⟩ := restartWindowDepth_spec θ hθ hθ4
      omega
    have hj0win := restartRoundedDepth_window θ hθ hθz
    have hge := restartProfile_ge_min θ (restartWindowDepth θ) hM
      (restartRoundedDepth θ restartOptimalAngle) hj0win.1 hj0win.2
    obtain ⟨_, _, hj3⟩ := restartIntegerOptimum_spec θ (restartWindowDepth θ) hM
    have hbest : restartProfile θ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ)
        ≤ restartProfile θ (restartRoundedDepth θ restartOptimalAngle : ℝ) := by
      linarith
    have hSmin : restartScaledProfileθ
          ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ) θ
        ≤ restartScaledProfileθ ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ) θ := by
      rw [scaledProfileθ_eq_profile, scaledProfileθ_eq_profile]
      have := mul_le_mul_of_nonneg_left hbest hθ.le
      linarith
    have hclose_u : |restartScaledProfileθ
            ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ) θ
          - restartScaledProfile ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)|
        ≤ restartScaledSlack * θ :=
      scaledProfile_close_wide θ ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)
        hθ hθ4 hu_floor hu_le
    have hclose_u0 : |restartScaledProfileθ
            ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ) θ
          - restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)|
        ≤ restartScaledSlack * θ :=
      scaledProfile_close_wide θ ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
        hθ hθ4 hu0_floor hu0_le
    have hval : restartScaledProfile ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)
        ≤ restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
          + 2 * restartScaledSlack * θ := by
      have hcu := (abs_le).mp hclose_u
      have hcu0 := (abs_le).mp hclose_u0
      linarith
    have hcont_u0 : |restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
          - restartScaledProfile restartScaledOptimum| < min ε (ε / 2) := by
      have h1 : |(restartRoundedDepth θ restartOptimalAngle : ℝ) * θ
          - restartScaledOptimum| < δS := by
        linarith
      exact hcont _ h1
    have hcont_u0' : restartScaledProfile ((restartRoundedDepth θ restartOptimalAngle : ℝ) * θ)
        - restartScaledProfile restartScaledOptimum < min ε (ε / 2) :=
      (abs_lt).mp hcont_u0 |>.2

    have hlink : θ * restartProfile θ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ)
        = restartScaledProfileθ ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ) θ := by
      rw [scaledProfileθ_eq_profile]
    have hlow : restartScaledProfile restartScaledOptimum
        - ε < θ * restartProfile θ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) := by
      rw [hlink]
      have hcu := (abs_le).mp hclose_u
      have hjpos : (0 : ℝ) < (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) := by
        obtain ⟨hj1, _, _⟩ := restartIntegerOptimum_spec θ (restartWindowDepth θ) hM
        have h1 : (1 : ℝ) ≤ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) := by
          exact_mod_cast hj1
        linarith
      have hmin := scaledProfile_ge_optimum_closed
        ((restartIntegerOptimum θ (restartWindowDepth θ) : ℝ) * θ)
        (mul_pos hjpos hθ) hu_le
      have hslack : 0 < restartScaledSlack := by
        unfold restartScaledSlack
        have hsin : 0 < Real.sin (1 / 8) := by
          have h1 : (0 : ℝ) < 1 / 8 := by norm_num
          have h2 : (1 / 8 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
          exact Real.sin_pos_of_pos_of_lt_pi h1 h2
        have hpi : 0 < Real.pi / 4 := by
          have := Real.pi_pos
          linarith
        have hpow : 0 < Real.sin (1 / 8) ^ 4 := by positivity
        exact div_pos hpi hpow
      have h3 : restartScaledSlack * θ < min ε (ε / 2) := by
        have h4 : θ * (2 * restartScaledSlack) < min ε (ε / 2) := by
          exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * restartScaledSlack)).1 hθE
        linarith
      linarith [hminε]
    have hupp : θ * restartProfile θ (restartIntegerOptimum θ (restartWindowDepth θ) : ℝ)
        < restartScaledProfile restartScaledOptimum + ε := by
      rw [hlink]
      have hslack : 0 < restartScaledSlack := by
        unfold restartScaledSlack
        have hsin : 0 < Real.sin (1 / 8) := by
          have h1 : (0 : ℝ) < 1 / 8 := by norm_num
          have h2 : (1 / 8 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
          exact Real.sin_pos_of_pos_of_lt_pi h1 h2
        have hpi : 0 < Real.pi / 4 := by
          have := Real.pi_pos
          linarith
        have hpow : 0 < Real.sin (1 / 8) ^ 4 := by positivity
        exact div_pos hpi hpow
      have h3 : restartScaledSlack * θ < min ε (ε / 2) := by
        have h4 : θ * (2 * restartScaledSlack) < min ε (ε / 2) := by
          exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * restartScaledSlack)).1 hθE
        linarith
      have hcu0 := (abs_le).mp hclose_u0
      linarith [hminε]
    have hopt : restartScaledProfile restartScaledOptimum = restartScaledExpectation :=
      scaledProfile_optimum_value
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hopt]

private theorem clause36_arcsin_ratio_tendsto :
    Filter.Tendsto (fun s : ℝ => Real.arcsin s / s) (𝓝[>] 0) (𝓝 1) := by
  have hderiv : HasDerivAt Real.arcsin 1 0 := by
    have h := Real.hasDerivAt_arcsin (x := (0 : ℝ)) (by norm_num) (by norm_num)
    simpa using! h
  have hslope : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (Real.arcsin (0 + t) - Real.arcsin 0)) (𝓝[>] 0) (𝓝 1) :=
    hderiv.tendsto_slope_zero_right
  simpa [Real.arcsin_zero, smul_eq_mul, inv_mul_eq_div] using! hslope

private theorem clause36_arcsin_tendsto_zero :
    Filter.Tendsto Real.arcsin (𝓝[>] 0) (𝓝[>] 0) := by
  have h1 : Filter.Tendsto Real.arcsin (𝓝[>] 0) (𝓝 0) := by
    have hcont : Filter.Tendsto Real.arcsin (𝓝 0) (𝓝 (Real.arcsin 0)) :=
      Real.continuous_arcsin.tendsto 0
    rw [Real.arcsin_zero] at hcont
    exact hcont.mono_left nhdsWithin_le_nhds
  have h2 : ∀ᶠ x in 𝓝[>] 0, Real.arcsin x ∈ Set.Ioi 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Real.arcsin_pos).2 hx
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 h2

theorem clause36_source_scale (N t : ℕ) (hN : 0 < N) (ht : 0 < t) :
    restartSourceScale N t = 1 / Real.sqrt ((t : ℝ) / (N : ℝ)) := by
  rw [restartSourceScale, Real.sqrt_div (by positivity : (0 : ℝ) ≤ (t : ℝ))]
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ (N : ℝ))]
  field_simp

theorem clause36_source_evaluation_ledger (j : ℕ) :
    restartSourceEvaluations j = j + 2 := rfl

theorem clause36_source_depth_asymptotic :
    Filter.Tendsto (fun s : ℝ => (restartIntegerOptimum (Real.arcsin s)
        (restartWindowDepth (Real.arcsin s)) : ℝ) * s)
      (𝓝[>] 0) (𝓝 restartScaledOptimum) := by
  have hratio : Filter.Tendsto (fun s : ℝ => s / Real.arcsin s) (𝓝[>] 0) (𝓝 1) := by
    have hinv : Filter.Tendsto (fun s : ℝ => (Real.arcsin s / s)⁻¹) (𝓝[>] 0) (𝓝 (1⁻¹)) :=
      clause36_arcsin_ratio_tendsto.inv₀ (by norm_num)
    simpa [div_eq_mul_inv] using! hinv
  have hcomp : Filter.Tendsto (fun s : ℝ =>
        (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ)
          * Real.arcsin s) (𝓝[>] 0) (𝓝 restartScaledOptimum) :=
    clause36_integer_optimum_tendsto.comp clause36_arcsin_tendsto_zero
  have hmul : Filter.Tendsto (fun s : ℝ =>
        ((restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ)
          * Real.arcsin s) * (s / Real.arcsin s))
      (𝓝[>] 0) (𝓝 (restartScaledOptimum * 1)) := hcomp.mul hratio
  have heq : (fun s : ℝ =>
        ((restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ)
          * Real.arcsin s) * (s / Real.arcsin s))
      =ᶠ[𝓝[>] 0] (fun s : ℝ => (restartIntegerOptimum (Real.arcsin s)
        (restartWindowDepth (Real.arcsin s)) : ℝ) * s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hne : Real.arcsin s ≠ 0 := by
      have hpos := (Real.arcsin_pos).mpr hspos
      exact fun h0 => hpos.ne' h0
    field_simp
  simpa using! hmul.congr' heq

theorem clause36_source_expectation_asymptotic :
    Filter.Tendsto (fun s : ℝ => s * restartProfile (Real.arcsin s)
        (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ))
      (𝓝[>] 0) (𝓝 restartScaledExpectation) := by
  have hratio : Filter.Tendsto (fun s : ℝ => s / Real.arcsin s) (𝓝[>] 0) (𝓝 1) := by
    have hinv : Filter.Tendsto (fun s : ℝ => (Real.arcsin s / s)⁻¹) (𝓝[>] 0) (𝓝 (1⁻¹)) :=
      clause36_arcsin_ratio_tendsto.inv₀ (by norm_num)
    simpa [div_eq_mul_inv] using! hinv
  have hcomp : Filter.Tendsto (fun s : ℝ =>
        Real.arcsin s * restartProfile (Real.arcsin s)
          (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ))
      (𝓝[>] 0) (𝓝 restartScaledExpectation) :=
    clause36_expected_iterations_tendsto.comp clause36_arcsin_tendsto_zero
  have hmul : Filter.Tendsto (fun s : ℝ =>
        (Real.arcsin s * restartProfile (Real.arcsin s)
          (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ))
          * (s / Real.arcsin s))
      (𝓝[>] 0) (𝓝 (restartScaledExpectation * 1)) := hcomp.mul hratio
  have heq : (fun s : ℝ =>
        (Real.arcsin s * restartProfile (Real.arcsin s)
          (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ))
          * (s / Real.arcsin s))
      =ᶠ[𝓝[>] 0] (fun s : ℝ => s * restartProfile (Real.arcsin s)
        (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hne : Real.arcsin s ≠ 0 := by
      have hpos := (Real.arcsin_pos).mpr hspos
      exact fun h0 => hpos.ne' h0
    field_simp
  simpa using! hmul.congr' heq

theorem clause36_source_evaluation_asymptotic :
    Filter.Tendsto (fun s : ℝ => (restartSourceEvaluations
        (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s))) : ℝ) * s)
      (𝓝[>] 0) (𝓝 restartScaledOptimum) := by
  have hdepth := clause36_source_depth_asymptotic
  have hone : Filter.Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := by
    have h : Filter.Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0) :=
      continuousAt_id (x := (0 : ℝ)).tendsto
    simpa using! h.mono_left nhdsWithin_le_nhds
  have hzero : Filter.Tendsto (fun s : ℝ => (2 : ℝ) * s) (𝓝[>] 0) (𝓝 0) := by
    have h := hone.mul_const 2
    simpa [mul_comm] using! h
  have hmul : Filter.Tendsto (fun s : ℝ =>
        (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ) * s
          + (2 : ℝ) * s) (𝓝[>] 0) (𝓝 (restartScaledOptimum + 0)) := hdepth.add hzero
  have heq : (fun s : ℝ =>
        (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s)) : ℝ) * s
          + (2 : ℝ) * s)
      =ᶠ[𝓝[>] 0] (fun s : ℝ => (restartSourceEvaluations
        (restartIntegerOptimum (Real.arcsin s) (restartWindowDepth (Real.arcsin s))) : ℝ) * s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [clause36_source_evaluation_ledger, Nat.cast_add]
    ring
  simpa using! hmul.congr' heq

private theorem queryCount_append {I : Type} (C D : Circuit I) :
    QueryCount (C ++ D) = QueryCount C + QueryCount D := by
  induction C with
  | nil => simp
  | cons s C ih =>
      cases s <;> simp [ih] <;> omega

private theorem gateCount_append {I : Type} (C D : Circuit I) :
    GateCount (C ++ D) = GateCount C + GateCount D := by
  induction C with
  | nil => simp
  | cons s C ih =>
      cases s <;> simp [ih] <;> omega

theorem ae_padded_query_count {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) :
    QueryCount (aePaddedAECircuit (I := I) M A j) = M := by
  have hq : QueryCount (countedAECircuit (I := I) M A j) = M - 1 :=
    (prepared_ae_access_ledger (I := I) M hM A j).1
  rw [aePaddedAECircuit, queryCount_append]
  simp
  omega

theorem ae_padded_gate_count {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) :
    GateCount (aePaddedAECircuit (I := I) M A j) = 5 * (M - 1) + 3 := by
  have hg : GateCount (countedAECircuit (I := I) M A j) = 5 * (M - 1) + 3 :=
    (prepared_ae_access_ledger (I := I) M hM A j).2.1
  rw [aePaddedAECircuit, gateCount_append]
  simp
  omega

theorem clause46_native_ledger_source_padding (M : ℕ) (hM : 0 < M)
    (A : Matrix (Fin M × (Bool × Fin M)) (Fin M × (Bool × Fin M)) ℂ)
    (j : Fin M × (Bool × Fin M)) :
    (aePaddedNativeLedger (I := Fin M × (Bool × Fin M)) M A j).queries = M ∧
      (aePaddedNativeLedger (I := Fin M × (Bool × Fin M)) M A j).gates = 5 * (M - 1) + 3 ∧
      (aePaddedNativeLedger (I := Fin M × (Bool × Fin M)) M A j).fairBits = 0 := by
  refine ⟨ae_padded_query_count M hM A j, ae_padded_gate_count M hM A j, rfl⟩

theorem clause46_native_ledger_access_transport (M : ℕ) (hM : 0 < M)
    (A : Matrix (Fin M × (Bool × Fin M)) (Fin M × (Bool × Fin M)) ℂ)
    (j : Fin M × (Bool × Fin M)) :
    aeSourceOracleAccesses (aeAccessWord (I := Fin M × (Bool × Fin M)) M) = M ∧
      (aeNativeLedger M A j).queries = M - 1 ∧
      (aePaddedNativeLedger (I := Fin M × (Bool × Fin M)) M A j).queries =
        aeSourceOracleAccesses (aeAccessWord (I := Fin M × (Bool × Fin M)) M) ∧
      (aeNativeLedger M A j).fairBits =
        (aePaddedNativeLedger (I := Fin M × (Bool × Fin M)) M A j).fairBits := by
  have hsrc := ae_source_evaluation_count (I := Fin M × (Bool × Fin M)) M hM A j
  have hq : QueryCount (countedAECircuit (I := Fin M × (Bool × Fin M)) M A j) = M - 1 :=
    (prepared_ae_access_ledger (I := Fin M × (Bool × Fin M)) M hM A j).1
  have hpad := ae_padded_query_count M hM A j
  constructor
  · exact hsrc
  constructor
  · rw [aeNativeLedger]
    exact hq
  constructor
  · change QueryCount (aePaddedAECircuit (I := Fin M × (Bool × Fin M)) M A j) = _
    exact hpad.trans hsrc.symm
  · rfl

private theorem int_floor_add_half_sub (x : ℝ) :
    |((Int.floor (x + 1 / 2) : ℝ)) - x| ≤ 1 / 2 := by
  have h1 : (Int.floor (x + 1 / 2) : ℝ) ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
  have h2 : x + 1 / 2 - 1 < (Int.floor (x + 1 / 2) : ℝ) := by
    have := Int.lt_floor_add_one (x + 1 / 2)
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem clause9_count_output_rounding {N : ℕ} (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω))) :
    |((basicApproxCountOutput N ε ω y : ℝ)) - (N : ℝ) *
        Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (basicApproxCountFinalM ε (basicApproxCountStop N ω)) y|
      ≤ 1 / 2 := by
  rw [basicApproxCountOutput]
  exact int_floor_add_half_sub _

theorem clause9_count_record_source_cost {I : Type} [Fintype I] [DecidableEq I] (M : ℕ)
    (hM : 0 < M) (A : Matrix I I ℂ) (j : I) :
    aeSourceOracleAccesses (aeAccessWord (I := I) M) = M ∧
      aeMarkAccesses (aeAccessWord (I := I) M) = M - 1 ∧
      QueryCount (countedAECircuit (I := I) M A j) = M - 1 := by
  exact ⟨ae_source_evaluation_count (I := I) M hM A j, ae_mark_access_count M hM A j,
    (prepared_ae_access_ledger (I := I) M hM A j).1⟩

theorem clause9_count_zero_branch {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : S.card = 0)
    (ε : ℝ) (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω * basicApproxCountFinalZero hN S ε ω (hω ω)) = 1 ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountPrefixWeight hN S ω * (basicApproxCountTotalCost N ε ω : ℝ)) =
        2 * (2 : ℝ) ^ basicApproxCountLoopCap N - 2 +
          (basicApproxCountFinalM ε (basicApproxCountLoopCap N) : ℝ) := by
  exact ⟨bhmt_basic_approx_count_zero hN S hS ε hω, bhmt_basic_approx_count_zero_cost hN S hS ε⟩

private theorem bbht_hypothesis_to_angle {P : ℕ} (hP : 0 < P) (θ : ℝ) (fObs : ℕ)
    (hag : bbhtCountHypothesis P θ fObs) :
    |θ - bbhtCountAngle P fObs| < Real.pi / (P : ℝ) := by
  have hf : |bbhtCountPeriod P θ - (fObs : ℝ)| < 1 := hag
  rw [bbhtCountPeriod] at hf
  have hfa : bbhtCountAngle P fObs = (fObs : ℝ) * Real.pi / (P : ℝ) := rfl
  rw [hfa]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have heq : (P : ℝ) * θ / Real.pi - (fObs : ℝ) =
      ((P : ℝ) * θ - Real.pi * (fObs : ℝ)) / Real.pi := by field_simp
  rw [heq, abs_div, abs_of_pos hpi] at hf
  have hkey : |(P : ℝ) * θ - Real.pi * (fObs : ℝ)| < Real.pi := by
    have := (div_lt_iff₀ hpi).mp hf
    linarith
  have hx : (P : ℝ) * (θ - (fObs : ℝ) * Real.pi / (P : ℝ)) =
      (P : ℝ) * θ - Real.pi * (fObs : ℝ) := by field_simp
  have habs : |(P : ℝ) * (θ - (fObs : ℝ) * Real.pi / (P : ℝ))| =
      (P : ℝ) * |θ - (fObs : ℝ) * Real.pi / (P : ℝ)| := by
    rw [abs_mul, abs_of_pos hPpos]
  have hmul : |θ - (fObs : ℝ) * Real.pi / (P : ℝ)| * (P : ℝ) < Real.pi := by
    rw [mul_comm, ← habs, hx]
    exact hkey
  have := (lt_div_iff₀ hPpos).mpr hmul
  simpa using! this

private theorem bbht_angle_to_sin {P : ℕ} (θ : ℝ) (fObs : ℕ)
    (h : |θ - bbhtCountAngle P fObs| < Real.pi / (P : ℝ)) :
    |Real.sin θ - Real.sin (bbhtCountAngle P fObs)| < Real.pi / (P : ℝ) := by
  have h1 := Real.abs_sin_sub_sin_le θ (bbhtCountAngle P fObs)
  exact lt_of_le_of_lt h1 h

theorem bbht_eq4_window {N P t : ℕ} (hN : 0 < N) (hP : 0 < P) (θ : ℝ) (fObs : ℕ)
    (hsin : Real.sin θ = Real.sqrt ((t : ℝ) / (N : ℝ)))
    (hag : bbhtCountHypothesis P θ fObs) :
    |(t : ℝ) - bbhtCountEstimate N P fObs| < bbhtCountWindow N (P : ℝ) (t : ℝ) := by
  have h1 := bbht_hypothesis_to_angle hP θ fObs hag
  have h2 := bbht_angle_to_sin θ fObs h1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsq : (t : ℝ) = (N : ℝ) * Real.sin θ ^ 2 := by
    rw [hsin, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (t : ℝ) / (N : ℝ))]
    field_simp [ne_of_gt hN]
  have hsplit : (t : ℝ) - bbhtCountEstimate N P fObs =
      (N : ℝ) * (Real.sin θ ^ 2 - Real.sin (bbhtCountAngle P fObs) ^ 2) := by
    rw [bbhtCountEstimate, hsq]
    ring
  rw [hsplit]
  have hx : (N : ℝ) * (Real.sin θ ^ 2 - Real.sin (bbhtCountAngle P fObs) ^ 2) =
      (N : ℝ) * (Real.sin θ - Real.sin (bbhtCountAngle P fObs)) *
        (Real.sin θ + Real.sin (bbhtCountAngle P fObs)) := by ring
  rw [hx, abs_mul, abs_mul, abs_of_nonneg (by exact_mod_cast hN.le)]
  have hsin0 : 0 ≤ Real.sin θ := by rw [hsin]; exact Real.sqrt_nonneg _
  have hlt : |Real.sin (bbhtCountAngle P fObs)| < Real.sin θ + Real.pi / (P : ℝ) := by
    have hlip : |Real.sin (bbhtCountAngle P fObs) - Real.sin θ| ≤
        |bbhtCountAngle P fObs - θ| := by
      simpa [abs_sub_comm] using!
        (Real.abs_sin_sub_sin_le (bbhtCountAngle P fObs) θ)
    have hangle : |bbhtCountAngle P fObs - θ| < Real.pi / (P : ℝ) := by
      simpa [abs_sub_comm] using! h1
    have htri : |Real.sin (bbhtCountAngle P fObs) - 0| ≤
        |Real.sin (bbhtCountAngle P fObs) - Real.sin θ| + |Real.sin θ - 0| :=
      abs_sub_le _ _ _
    have htri' : |Real.sin (bbhtCountAngle P fObs)| ≤
        |Real.sin (bbhtCountAngle P fObs) - Real.sin θ| + Real.sin θ := by
      simpa only [sub_zero, abs_of_nonneg hsin0] using! htri
    linarith
  have hsum : |Real.sin θ + Real.sin (bbhtCountAngle P fObs)| ≤
      2 * Real.sin θ + Real.pi / (P : ℝ) := by
    have h1 : |Real.sin θ + Real.sin (bbhtCountAngle P fObs)| ≤
        |Real.sin θ| + |Real.sin (bbhtCountAngle P fObs)| := abs_add_le _ _
    rw [abs_of_nonneg hsin0] at h1
    have h2' : Real.sin θ + |Real.sin (bbhtCountAngle P fObs)| <
        Real.sin θ + (Real.sin θ + Real.pi / (P : ℝ)) :=
      add_lt_add_right hlt (Real.sin θ)
    have h3 : |Real.sin θ + Real.sin (bbhtCountAngle P fObs)| ≤
        Real.sin θ + (Real.sin θ + Real.pi / (P : ℝ)) := le_trans h1 (le_of_lt h2')
    have h5 : Real.sin θ + (Real.sin θ + Real.pi / (P : ℝ)) =
        2 * Real.sin θ + Real.pi / (P : ℝ) := by ring
    rw [h5] at h3
    exact h3
  have hA : (N : ℝ) * |Real.sin θ - Real.sin (bbhtCountAngle P fObs)| *
        |Real.sin θ + Real.sin (bbhtCountAngle P fObs)| ≤
      (N : ℝ) * |Real.sin θ - Real.sin (bbhtCountAngle P fObs)| *
        (2 * Real.sin θ + Real.pi / (P : ℝ)) := by
    have hnonneg : 0 ≤ (N : ℝ) * |Real.sin θ - Real.sin (bbhtCountAngle P fObs)| := by
      positivity
    exact mul_le_mul_of_nonneg_left hsum hnonneg
  have hB : (N : ℝ) * |Real.sin θ - Real.sin (bbhtCountAngle P fObs)| *
        (2 * Real.sin θ + Real.pi / (P : ℝ)) <
      (N : ℝ) * (Real.pi / (P : ℝ)) * (2 * Real.sin θ + Real.pi / (P : ℝ)) := by
    have hK : (0 : ℝ) < (N : ℝ) * (2 * Real.sin θ + Real.pi / (P : ℝ)) := by positivity
    have hB1 : |Real.sin θ - Real.sin (bbhtCountAngle P fObs)| *
          ((N : ℝ) * (2 * Real.sin θ + Real.pi / (P : ℝ))) <
        (Real.pi / (P : ℝ)) * ((N : ℝ) * (2 * Real.sin θ + Real.pi / (P : ℝ))) :=
      mul_lt_mul_of_pos_right h2 hK
    convert! hB1 using 1 <;> ring
  have hmul : (N : ℝ) * Real.sin θ = Real.sqrt ((t : ℝ) * (N : ℝ)) := by
    rw [hsin]
    have hmul' : Real.sqrt ((t : ℝ) / (N : ℝ)) =
        Real.sqrt (t : ℝ) / Real.sqrt (N : ℝ) :=
      Real.sqrt_div' (t : ℝ) (by exact_mod_cast hN.le)
    have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt (by exact_mod_cast hN.le)
    have hn0 : Real.sqrt (N : ℝ) ≠ 0 := by positivity
    rw [hmul', Real.sqrt_mul (Nat.cast_nonneg t)]
    calc (N : ℝ) * (Real.sqrt (t : ℝ) / Real.sqrt (N : ℝ))
        = (N : ℝ) * Real.sqrt (t : ℝ) / Real.sqrt (N : ℝ) := by ring
      _ = (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) * Real.sqrt (t : ℝ)) / Real.sqrt (N : ℝ) := by
          rw [hsqN]
      _ = Real.sqrt (t : ℝ) * Real.sqrt (N : ℝ) := by field_simp
  calc (N : ℝ) * |Real.sin θ - Real.sin (bbhtCountAngle P fObs)| *
        |Real.sin θ + Real.sin (bbhtCountAngle P fObs)|
      ≤ (N : ℝ) * |Real.sin θ - Real.sin (bbhtCountAngle P fObs)| *
          (2 * Real.sin θ + Real.pi / (P : ℝ)) := hA
    _ < (N : ℝ) * (Real.pi / (P : ℝ)) * (2 * Real.sin θ + Real.pi / (P : ℝ)) := hB
    _ = 2 * Real.pi / (P : ℝ) * Real.sqrt ((t : ℝ) * (N : ℝ)) +
        Real.pi ^ 2 / (P : ℝ) ^ 2 * (N : ℝ) := by
      have hre : (N : ℝ) * (Real.pi / (P : ℝ)) * (2 * Real.sin θ + Real.pi / (P : ℝ)) =
          2 * Real.pi / (P : ℝ) * Real.sqrt ((t : ℝ) * (N : ℝ)) +
            Real.pi ^ 2 / (P : ℝ) ^ 2 * (N : ℝ) := by
        have hre' : (N : ℝ) * (Real.pi / (P : ℝ)) * (2 * Real.sin θ + Real.pi / (P : ℝ)) =
            (2 * Real.pi / (P : ℝ)) * ((N : ℝ) * Real.sin θ) +
              (Real.pi ^ 2 / (P : ℝ) ^ 2) * (N : ℝ) := by
          field_simp [ne_of_gt hpi, ne_of_gt hPpos]
        rw [hre', hmul]
      rw [hre]
    _ = bbhtCountWindow N (P : ℝ) (t : ℝ) := by
        unfold bbhtCountWindow
        ring

theorem bbht_bullet_single_grid (N t c : ℝ) (hN : 0 < N) (ht : 0 ≤ t) (hc : 0 < c) :
    bbhtCountWindow N (c * Real.sqrt N) t = 2 * Real.pi / c * Real.sqrt t + Real.pi ^ 2 / c ^ 2 := by
  unfold bbhtCountWindow
  have hn0 : Real.sqrt N ≠ 0 := by positivity
  have hc0 : c ≠ 0 := ne_of_gt hc
  rw [show (c * Real.sqrt N) ^ 2 = c ^ 2 * (Real.sqrt N ^ 2) by ring]
  rw [show Real.sqrt (t * N) = Real.sqrt t * Real.sqrt N from Real.sqrt_mul ht N]
  field_simp
  rw [Real.sq_sqrt hN.le]
  ring

theorem bbht_bullet_relative_grid (N t c : ℝ) (hN : 0 < N) (ht : 0 < t) (hc : 0 < c) :
    bbhtCountWindow N (c * Real.sqrt (N / t)) t =
      2 * Real.pi / c * t + Real.pi ^ 2 / c ^ 2 * t := by
  unfold bbhtCountWindow
  have hn0 : Real.sqrt N ≠ 0 := by positivity
  have hc0 : c ≠ 0 := ne_of_gt hc
  have ht0 : Real.sqrt t ≠ 0 := by positivity
  rw [show (c * Real.sqrt (N / t)) ^ 2 = c ^ 2 * (Real.sqrt (N / t) ^ 2) by ring]
  rw [show Real.sqrt (N / t) = Real.sqrt N / Real.sqrt t from
      Real.sqrt_div' N ht.le]
  rw [show Real.sqrt (t * N) = Real.sqrt t * Real.sqrt N from Real.sqrt_mul ht.le N]
  field_simp
  rw [Real.sq_sqrt hN.le, Real.sq_sqrt ht.le]
  ring

theorem bbht_bullet_relative_factor (N t c : ℝ) (hN : 0 < N) (ht : 0 < t) (hc : 0 < c) :
    1 + (bbhtCountWindow N (c * Real.sqrt (N / t)) t) / (t : ℝ) = (1 + Real.pi / c) ^ 2 := by
  have h := bbht_bullet_relative_grid N t c hN ht hc
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  rw [h]
  field_simp
  ring

theorem bbht_bullet_two_stage_grid (N t c : ℝ) (hN : 0 < N) (ht : 0 < t) (hc : 0 < c) :
    bbhtCountWindow N (c * Real.sqrt (t * N)) t = 2 * Real.pi / c + Real.pi ^ 2 / (c ^ 2 * t) := by
  unfold bbhtCountWindow
  have hn0 : Real.sqrt N ≠ 0 := by positivity
  have hc0 : c ≠ 0 := ne_of_gt hc
  have htn : 0 < t * N := by positivity
  have htn0 : Real.sqrt (t * N) ≠ 0 := by positivity
  rw [show (c * Real.sqrt (t * N)) ^ 2 = c ^ 2 * (Real.sqrt (t * N) ^ 2) by ring]
  field_simp
  rw [Real.sq_sqrt htn.le]
  ring

theorem bbht_bullet_two_stage_exact (t : ℝ) (ht : 1 ≤ t) (c : ℝ)
    (hc : 14 ≤ c) :
    2 * Real.pi / c + Real.pi ^ 2 / (c ^ 2 * t) < 1 / 2 := by
  have hc0 : 0 < c := by linarith
  have hpi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbase : 2 * Real.pi / 14 + Real.pi ^ 2 / (14 ^ 2 * 1) < 1 / 2 := by
    nlinarith [sq_nonneg (Real.pi - (3.1416 : ℝ))]
  have hstep1 : 2 * Real.pi / c ≤ 2 * Real.pi / 14 := by
    exact div_le_div₀ (by positivity : (0:ℝ) ≤ 2 * Real.pi) le_rfl
      (by norm_num : (0:ℝ) < 14) (by linarith : (14:ℝ) ≤ c)
  have hstep2 : Real.pi ^ 2 / (c ^ 2 * t) ≤ Real.pi ^ 2 / (14 ^ 2 * 1) := by
    have hsq : (14 : ℝ) ^ 2 * 1 ≤ c ^ 2 * t := by
      have h2' : (14 : ℝ) ^ 2 ≤ c ^ 2 := by
        have hc' : (0 : ℝ) < c := hc0
        nlinarith
      have ht' : (0 : ℝ) < t := by linarith
      nlinarith
    exact div_le_div₀ (by positivity : (0:ℝ) ≤ Real.pi ^ 2) le_rfl
      (by norm_num : (0:ℝ) < 14 ^ 2 * 1) hsq
  linarith

theorem bbht_two_stage_window_lower_bound (N t c : ℝ) (hN : 0 < N) (ht : 0 < t)
    (hc : 0 < c) :
    0 < Real.pi ^ 2 / (c ^ 2 * t) ∧
      bbhtCountWindow N (c * Real.sqrt (t * N)) t =
        2 * Real.pi / c + Real.pi ^ 2 / (c ^ 2 * t) := by
  have h1 : (0 : ℝ) < Real.pi ^ 2 / (c ^ 2 * t) := by positivity
  have h2 := bbht_bullet_two_stage_grid N t c hN ht hc
  exact ⟨h1, h2⟩

theorem bbht_perfect_square_two_stage_time (N t c : ℝ) (hN : 0 < N) (ht : 1 ≤ t)
    (hc : 0 < c) :
    c * Real.sqrt N ≤ c * Real.sqrt (t * N) := by
  have h1 : Real.sqrt N ≤ Real.sqrt (t * N) := by
    have hle : N ≤ t * N := by
      have ht' : (1 : ℝ) ≤ t := ht
      have hN' : (0 : ℝ) ≤ N := le_of_lt hN
      calc N = 1 * N := by ring
        _ ≤ t * N := mul_le_mul_of_nonneg_right ht' hN'
    exact Real.sqrt_le_sqrt hle
  exact mul_le_mul_of_nonneg_left h1 (by linarith)

theorem bbht_sqrt_mul_square (N m : ℕ) (hm : 0 < m) :
    Real.sqrt (((m * m : ℕ) : ℝ) * (N : ℝ)) = (m : ℝ) * Real.sqrt (N : ℝ) := by
  have hsq : ((m * m : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  rw [hsq]
  rw [Real.sqrt_mul (by positivity) (N : ℝ)]
  rw [Real.sqrt_sq (by positivity)]

theorem bbht_two_stage_time_perfect_square (N : ℕ) (m : ℕ) (c : ℝ) (hm : 0 < m) :
    bbhtTwoStageTime (N : ℝ) ((m * m : ℕ) : ℝ) c =
      c * (1 + (m : ℝ)) * Real.sqrt (N : ℝ) := by
  have hsqrt := bbht_sqrt_mul_square N m hm
  unfold bbhtTwoStageTime bbhtStageOneGrid bbhtStageTwoGrid
  rw [hsqrt]
  ring

theorem bbht_perfect_square_time_refuted (N : ℕ) (c K : ℝ) (hc : 0 < c) (hK : 0 < K)
    (hN : 0 < N) :
    ∃ t : ℕ, 0 < t ∧ (∃ m : ℕ, m * m = t) ∧
      K * Real.sqrt (N : ℝ) < bbhtTwoStageTime (N : ℝ) (t : ℝ) c := by

  have hex : ∃ m : ℕ, (K : ℝ) / c < m := exists_nat_gt (K / c)
  obtain ⟨m, hm⟩ := hex
  have hm0 : 0 < m := by
    have hpos : (0 : ℝ) < K / c := div_pos hK hc
    have hmc : (m : ℝ) > 0 := by
      by_contra hcon
      push Not at hcon
      exact (not_lt_of_ge hcon) (lt_of_lt_of_le hpos (le_of_lt hm))
    exact_mod_cast hmc
  refine ⟨m * m, by positivity, ⟨m, rfl⟩, ?_⟩
  have hform := bbht_two_stage_time_perfect_square N m c hm0
  have hkey : K < c * (m : ℝ) := by
    have h := (div_lt_iff₀ hc).mp hm
    linarith
  rw [hform]

  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hmul : c * (m : ℝ) * Real.sqrt (N : ℝ) ≤
      c * (1 + (m : ℝ)) * Real.sqrt (N : ℝ) := by
    have hc0 : 0 ≤ c := le_of_lt hc
    nlinarith [mul_le_mul_of_nonneg_left (by linarith) hc0]
  nlinarith [hmul]

theorem bbht_overstrong_perfect_square_refuted :
    ¬ ∃ K : ℝ, 0 < K ∧ bbhtOverStrongPerfectSquare K := by
  rintro ⟨K, hK, hclaim⟩

  have hc : 0 < bbhtCountExactConstant := by norm_num [bbhtCountExactConstant]
  obtain ⟨t, ht, ⟨m, hm⟩, hlt⟩ :=
    bbht_perfect_square_time_refuted 1 bbhtCountExactConstant K hc hK (by norm_num)
  have hm0 : 0 < m := by
    have hne : m ≠ 0 := by
      intro hz
      have : t = 0 := by rw [← hm]; simp [hz]
      omega
    exact Nat.pos_of_ne_zero hne
  have hform := bbht_two_stage_time_perfect_square 1 m bbhtCountExactConstant hm0

  have hclaim' : bbhtTwoStageTime (1 : ℝ) ((m * m : ℕ) : ℝ) bbhtCountExactConstant ≤
      K * Real.sqrt (1 : ℝ) := by
    simpa using! (hclaim 1 m (by norm_num) hm0)
  have hlt' : K * Real.sqrt (1 : ℝ) < bbhtTwoStageTime (1 : ℝ) ((m * m : ℕ) : ℝ)
      bbhtCountExactConstant := by
    have hsub : (t : ℝ) = ((m * m : ℕ) : ℝ) := by exact_mod_cast hm.symm
    rw [hsub] at hlt
    simpa using! hlt
  have hform' : bbhtTwoStageTime (1 : ℝ) ((m * m : ℕ) : ℝ) bbhtCountExactConstant =
      bbhtCountExactConstant * (1 + (m : ℝ)) * Real.sqrt (1 : ℝ) := by
    simpa using! hform
  linarith [hclaim', hform', hlt']

theorem bbht_source_readout_transport {N P : ℕ} (z : Fin P) :
    bbhtCountEstimate N P z.val = (N : ℝ) * aeEstimate P z := by
  have hsin : Real.sin (bbhtCountAngle P z.val) = Real.sin (Real.pi * (z.val : ℝ) / (P : ℝ)) := by
    unfold bbhtCountAngle
    congr 1
    ring
  unfold bbhtCountEstimate aeEstimate
  rw [hsin]

theorem bbht_source_output_at_label {N P : ℕ} (z : Fin P) :
    bbhtCountEstimate N P z.val = (N : ℝ) * aeEstimate P z :=
  bbht_source_readout_transport z

theorem bbht_eq4_window_eq_frozen {N P t : ℝ} :
    bbhtCountWindow N P t =
      2 * Real.pi / P * Real.sqrt (t * N) + Real.pi ^ 2 / P ^ 2 * N := rfl

theorem clause7_actual_success_probability (N P : ℕ) (S : Finset (Fin N))
    (hN : 0 < N) (hS : S.card ≤ N / 2) (hP : 4 ≤ P) :
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
          |(N : ℝ) * aeEstimate P z - (S.card : ℝ)| <
            bbhtCountWindow (N : ℝ) (P : ℝ) (S.card : ℝ)),
        (aeLaw P (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN)
          (by omega)).prob z := by
  have h := Qatlib.Concepts.AEMeanReadout.RankOneSubspace.theorem5ApproximateCounting
    N P S hN hS hP

  simpa only [bbhtCountWindow] using! h

theorem clause7_actual_eq4_holds (N P : ℕ) (S : Finset (Fin N)) (z : Fin P)
    (hz : |(N : ℝ) * aeEstimate P z - (S.card : ℝ)| <
        bbhtCountWindow (N : ℝ) (P : ℝ) (S.card : ℝ)) :
    |(S.card : ℝ) - bbhtCountEstimate N P z.val| <
      bbhtCountWindow (N : ℝ) (P : ℝ) (S.card : ℝ) := by
  rw [bbht_source_readout_transport z]
  rw [abs_sub_comm]
  exact hz

theorem clause7_source_output_is_actual_readout (N P : ℕ) (z : Fin P) :
    bbhtCountEstimate N P z.val = (N : ℝ) * aeEstimate P z :=
  bbht_source_readout_transport z

theorem clause7_actual_amplification_cost (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    aeSourceOracleAccesses (aeAccessWord (I := Fin N) P) = P ∧
      QueryCount (countedAECircuit (I := Fin N) P (QFTMatrix N) ⟨0, hN⟩) = P - 1 := by
  have hcost := clause7_source_cost_convention P hP (QFTMatrix N) ⟨0, hN⟩
  have hq : QueryCount (countedAECircuit (I := Fin N) P (QFTMatrix N) ⟨0, hN⟩) = P - 1 :=
    (prepared_ae_access_ledger (I := Fin N) P hP (QFTMatrix N) ⟨0, hN⟩).1
  exact ⟨hcost.1, hq⟩

theorem clause11_rough_grid_two_le (N : ℕ) (hN : 0 < N) : 2 ≤ BHMTTh17.exactCountM₀ N := by
  have hsqrt : (1:ℝ) ≤ Real.sqrt (N : ℝ) := by
    simpa using! (Real.sqrt_le_sqrt (show (1:ℝ) ≤ (N:ℝ) from by exact_mod_cast hN))
  have hpi : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have h : (1:ℝ) < 14 * Real.pi * Real.sqrt (N : ℝ) := by nlinarith
  rw [BHMTTh17.exactCountM₀]
  by_contra hcon
  have h1 : Nat.ceil (14 * Real.pi * Real.sqrt (N : ℝ)) ≤ 1 := by omega
  have h2 : (14 * Real.pi * Real.sqrt (N : ℝ)) ≤ (1:ℕ) :=
    (Nat.ceil_le (a := 14 * Real.pi * Real.sqrt (N : ℝ)) (n := 1)).mp h1
  have h2' : (14 * Real.pi * Real.sqrt (N : ℝ)) ≤ (1:ℝ) := by
    simpa only [Nat.cast_one] using! h2
  linarith

theorem clause11_rough_record_range (N : ℕ) (hN : 0 < N) (z : Fin (BHMTTh17.exactCountM₀ N)) :
    (0:ℝ) ≤ (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z ∧
      (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z ≤ (N:ℝ) := by
  have hest := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.aeEstimate_mem
    (BHMTTh17.exactCountM₀ N) z
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨mul_nonneg hNpos.le hest.1, ?_⟩
  have h2 : (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z ≤ (N:ℝ) * 1 :=
    mul_le_mul_of_nonneg_left hest.2 hNpos.le
  simpa using! h2

private theorem clause11_rough_quantity_ge (N : ℕ) (hN : 0 < N)
    (z : Fin (BHMTTh17.exactCountM₀ N)) :
    (1:ℝ) ≤ BHMTTh17.exactCountRough N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z) := by
  have hr := clause11_rough_record_range N hN z
  have e1 : (1:ℝ) ≤ (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 := by linarith
  have e2 : (1:ℝ) ≤ (N:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 := by linarith
  have hprod : (1:ℝ) ≤ ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1) *
      ((N:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1) := by
    have h := mul_le_mul e1 e2 (by linarith) (by linarith)
    linarith
  rw [BHMTTh17.exactCountRough]
  simpa using! (Real.sqrt_le_sqrt hprod)

theorem clause11_rough_quantity_le (N : ℕ) (hN : 0 < N)
    (z : Fin (BHMTTh17.exactCountM₀ N)) :
    BHMTTh17.exactCountRough N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z) ≤ (N:ℝ) + 1 := by
  have hr := clause11_rough_record_range N hN z
  have e1 : (0:ℝ) ≤ (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 := by linarith
  have e2 : (0:ℝ) ≤ (N:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 := by linarith
  have e1' : (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 ≤ (N:ℝ) + 1 := by linarith
  have e2' : (N:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 ≤ (N:ℝ) + 1 := by linarith
  have hprod : ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1) *
      ((N:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1) ≤ ((N:ℝ) + 1) * ((N:ℝ) + 1) :=
    mul_le_mul e1' e2' e2 (by linarith)
  rw [BHMTTh17.exactCountRough]
  have h2 := Real.sqrt_le_sqrt hprod
  rw [Real.sqrt_mul_self (by linarith)] at h2
  exact h2

theorem clause11_final_grid_two_le (N : ℕ) (hN : 0 < N)
    (z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N)) :
    2 ≤ BHMTTh17.exactCountGrid N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) := by
  have hr1 := clause11_rough_quantity_ge N hN z₁
  have hr2 := clause11_rough_quantity_ge N hN z₂
  have hmin : (1:ℝ) ≤ min (BHMTTh17.exactCountRough N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
      (BHMTTh17.exactCountRough N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) := le_min hr1 hr2
  have hceilN : (30:ℕ) ≤ BHMTTh17.exactCountGrid N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) := by
    rw [BHMTTh17.exactCountGrid]
    have h1 : (30:ℝ) ≤ 30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
        (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) := by
      have := mul_le_mul_of_nonneg_left hmin (by norm_num : (0:ℝ) ≤ 30)
      linarith
    have h2 : (30:ℝ) ≤ (Nat.ceil (30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
        (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂))) : ℝ) :=
      h1.trans (Nat.le_ceil (30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
        (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂))))
    exact_mod_cast h2
  omega

theorem clause11_source_cost_ledger (N : ℕ) (hN : 0 < N) (M₀ M : ℕ) (hM₀ : 0 < M₀) (hM : 0 < M) :
    aeSourceEvaluations (I := Fin N) M₀ + aeSourceEvaluations (I := Fin N) M₀ +
        aeSourceEvaluations (I := Fin N) M
      = exactCountSourceEvaluations M₀ M := by
  letI : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a = b)
  have h1 : aeSourceEvaluations (I := Fin N) M₀ = M₀ := by
    unfold aeSourceEvaluations
    exact ae_source_evaluation_count (I := Fin N) M₀ hM₀ (QFTMatrix N) ⟨0, hN⟩
  have h2 : aeSourceEvaluations (I := Fin N) M = M := by
    unfold aeSourceEvaluations
    exact ae_source_evaluation_count (I := Fin N) M hM (QFTMatrix N) ⟨0, hN⟩
  simp only [exactCountSourceEvaluations, h1, h2]
  omega

theorem clause11_frozen_bounds (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) :
    (2/3 ≤ BHMTTh17.exactCountSuccessMass hN S (clause11_rough_grid_two_le N hN)
        (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂)) ∧
    (BHMTTh17.exactCountCostMass hN S (clause11_rough_grid_two_le N hN)
        (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂) ≤
      1000 * Real.sqrt (((S.card : ℝ) + 1) * ((N : ℝ) - (S.card : ℝ) + 1))) := by
  have h := bhmt_theorem17_exact_count N hN S (clause11_rough_grid_two_le N hN)
    (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂)
  exact ⟨h.1, h.2⟩

theorem clause11_zero_branch (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) (hS : S.card = 0) :
    BHMTTh17.exactCountSuccessMass hN S (clause11_rough_grid_two_le N hN)
        (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂) = 1 ∧
    BHMTTh17.exactCountCostMass hN S (clause11_rough_grid_two_le N hN)
        (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂) =
      2 * (BHMTTh17.exactCountM₀ N : ℝ) + (BHMTTh17.exactCountGrid N 0 0 : ℝ) := by
  have h1 := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.bhmt_exact_count_zero_success hN S hS
    (clause11_rough_grid_two_le N hN)
    (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂)
  have h2 := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.bhmt_exact_count_zero_cost_eq hN S hS
    (clause11_rough_grid_two_le N hN)
    (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂)
  exact ⟨h1, h2⟩

theorem clause11_full_branch (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) (hS : S.card = N) :
    (2/3 ≤ BHMTTh17.exactCountSuccessMass hN S (clause11_rough_grid_two_le N hN)
        (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂)) ∧
    (BHMTTh17.exactCountCostMass hN S (clause11_rough_grid_two_le N hN)
        (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂) ≤
      1000 * Real.sqrt ((N:ℝ) + 1)) := by
  have h := clause11_frozen_bounds N hN S
  refine ⟨h.1, ?_⟩
  have hcard : (S.card : ℝ) = (N : ℝ) := by exact_mod_cast hS
  have h2 := h.2
  rw [hcard] at h2
  have hgap : (N:ℝ) - (N:ℝ) + 1 = 1 := by ring
  rw [hgap] at h2
  have hmul : ((N:ℝ) + 1) * 1 = (N:ℝ) + 1 := by ring
  rw [hmul] at h2
  exact h2

theorem clause11_rough_window_mass (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) :
    (∑ z ∈ Finset.univ.filter (fun z : Fin (BHMTTh17.exactCountM₀ N) =>
        countWindow N (BHMTTh17.exactCountM₀ N) 2 S.card z),
      (aeLaw (BHMTTh17.exactCountM₀ N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) (clause11_rough_grid_two_le N hN)).prob z) ≥ 1 / 2 := by
  have h := bhmt_counting_k2_window N (BHMTTh17.exactCountM₀ N) S hN
    (clause11_rough_grid_two_le N hN) 2 (by norm_num)
  have h' : (1:ℝ) - 1 / (2 * (((2:ℕ) : ℝ) - 1)) = 1 / 2 := by norm_num
  rw [h'] at h
  simpa [countWindow] using! h

theorem clause11_window_rough_ge (N : ℕ) (hN : 0 < N) (S : Finset (Fin N))
    (ht1 : 1 ≤ S.card) (htN : S.card < N)
    (z : Fin (BHMTTh17.exactCountM₀ N))
    (hz : countWindow N (BHMTTh17.exactCountM₀ N) 2 S.card z) :
    (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))
      ≤ BHMTTh17.exactCountRough N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z) := by
  have hM₀ : 2 ≤ BHMTTh17.exactCountM₀ N := clause11_rough_grid_two_le N hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hcardlt : S.card < N := htN
  have htR : (1:ℝ) ≤ (S.card:ℝ) := by exact_mod_cast ht1
  have hcard0 : (0:ℝ) ≤ (S.card:ℝ) := Nat.cast_nonneg _
  have hcardltR : (S.card:ℝ) < (N:ℝ) := by exact_mod_cast hcardlt
  have hgap0 : (0:ℝ) ≤ (N:ℝ) - (S.card:ℝ) := by linarith
  have hgapR : (1:ℝ) ≤ (N:ℝ) - (S.card:ℝ) := by
    have h1 : S.card + 1 ≤ N := by omega
    have h2 : (S.card:ℝ) + 1 ≤ (N:ℝ) := by exact_mod_cast h1
    linarith
  have hA : (0:ℝ) ≤ (S.card:ℝ) * ((N:ℝ) - (S.card:ℝ)) := mul_nonneg hcard0 hgap0

  have hz' := hz
  simp only [countWindow] at hz'
  have hz'' : |(N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z - (S.card:ℝ)| ≤
      4 * Real.pi * Real.sqrt ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (BHMTTh17.exactCountM₀ N : ℝ)
        + 4 * Real.pi ^ 2 * (N : ℝ) / (BHMTTh17.exactCountM₀ N : ℝ) ^ 2 := by
    convert! hz' using 1 <;> ring

  have hM₀ge : (14 * Real.pi * Real.sqrt (N : ℝ)) ≤ (BHMTTh17.exactCountM₀ N : ℝ) := by
    rw [BHMTTh17.exactCountM₀]
    exact Nat.le_ceil (14 * Real.pi * Real.sqrt (N : ℝ))
  have hM₀pos : (0:ℝ) < BHMTTh17.exactCountM₀ N := by
    have h1 : (0:ℝ) < 14 * Real.pi * Real.sqrt (N : ℝ) := by positivity
    linarith
  have hdenpos : (0:ℝ) < 14 * Real.pi * Real.sqrt (N : ℝ) := by positivity
  have hsq2 : (14 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 ≤ (BHMTTh17.exactCountM₀ N : ℝ) ^ 2 := by
    nlinarith [hM₀ge, hM₀pos]

  have hterm1 : 4 * Real.pi * Real.sqrt ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ)))
        / (BHMTTh17.exactCountM₀ N : ℝ)
      ≤ (2/7) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ)) := by
    apply (div_le_iff₀ (by positivity)).2
    have h1 : (2/7) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ))
        * (BHMTTh17.exactCountM₀ N : ℝ)
        ≥ (2/7) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ))
          * (14 * Real.pi * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hM₀ge (by positivity)
    have h2 : (2/7) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ))
        * (14 * Real.pi * Real.sqrt (N : ℝ))
        = 4 * Real.pi * Real.sqrt ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) := by
      rw [Real.sqrt_div hA (N:ℝ)]
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hsq : Real.sqrt (N : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    linarith

  have hterm2 : 4 * Real.pi ^ 2 * (N : ℝ) / (BHMTTh17.exactCountM₀ N : ℝ) ^ 2 ≤ 1 / 49 := by
    apply (div_le_iff₀ (by positivity)).2
    have h1 : (1/49) * (BHMTTh17.exactCountM₀ N : ℝ) ^ 2
        ≥ (1/49) * (14 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq2 (by norm_num)
    have h2 : (1/49) * (14 * Real.pi * Real.sqrt (N : ℝ)) ^ 2
        = 4 * Real.pi ^ 2 * (N : ℝ) := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hsq : Real.sqrt (N : ℝ) ≠ 0 := by positivity
      field_simp
      nlinarith [Real.sq_sqrt (x := (N : ℝ)) (by positivity)]
    linarith
  have hhalf : |(N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z - (S.card:ℝ)| ≤
      (2/7) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ)) + 1 / 49 := by
    linarith [hterm1, hterm2]

  have hdiv1 : ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ) ≤ (S.card:ℝ) := by
    have h1 : ((N:ℝ) - (S.card:ℝ)) / (N:ℝ) ≤ 1 := (div_le_one hNpos).2 (by linarith)
    have h2 : ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ)
        = (S.card:ℝ) * (((N:ℝ) - (S.card:ℝ)) / (N:ℝ)) := by ring
    rw [h2]
    have h3 : (S.card:ℝ) * (((N:ℝ) - (S.card:ℝ)) / (N:ℝ)) ≤ (S.card:ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h1 hcard0
    simpa using! h3
  have hdiv2 : ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ) ≤ (N:ℝ) - (S.card:ℝ) := by
    have h1 : (S.card:ℝ) / (N:ℝ) ≤ 1 := (div_le_one hNpos).2 (by linarith)
    have h2 : ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ)
        = ((N:ℝ) - (S.card:ℝ)) * ((S.card:ℝ) / (N:ℝ)) := by ring
    rw [h2]
    have h3 : ((N:ℝ) - (S.card:ℝ)) * ((S.card:ℝ) / (N:ℝ)) ≤ ((N:ℝ) - (S.card:ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left h1 hgap0
    simpa using! h3
  have hsq1 : Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ))
      ≤ Real.sqrt (S.card:ℝ) := Real.sqrt_le_sqrt hdiv1
  have hsq2' : Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ))
      ≤ Real.sqrt ((N:ℝ) - (S.card:ℝ)) := Real.sqrt_le_sqrt hdiv2
  have hone1 : (1:ℝ) ≤ Real.sqrt (S.card:ℝ) := by
    simpa using! (Real.sqrt_le_sqrt (show (1:ℝ) ≤ (S.card:ℝ) from by exact_mod_cast ht1))
  have hone2 : (1:ℝ) ≤ Real.sqrt ((N:ℝ) - (S.card:ℝ)) := by
    simpa using! (Real.sqrt_le_sqrt (show (1:ℝ) ≤ (N:ℝ) - (S.card:ℝ) from by linarith))
  have hε1 : (2/7) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ)) + 1 / 49
      ≤ (3/8) * Real.sqrt (S.card:ℝ) := by
    have h1 : (2/7) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ))
        ≤ (2/7) * Real.sqrt (S.card:ℝ) := mul_le_mul_of_nonneg_left hsq1 (by norm_num)
    have h2 : (1/49:ℝ) ≤ (1/49) * Real.sqrt (S.card:ℝ) := by
      have := mul_le_mul_of_nonneg_left hone1 (by norm_num : (0:ℝ) ≤ 1/49)
      linarith
    have h3 : (2/7) * Real.sqrt (S.card:ℝ) + (1/49) * Real.sqrt (S.card:ℝ)
        = (15/49) * Real.sqrt (S.card:ℝ) := by ring
    have h4 : (15/49:ℝ) * Real.sqrt (S.card:ℝ) ≤ (3/8) * Real.sqrt (S.card:ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
    linarith [h1, h2, h3, h4]
  have hε2 : (2/7) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ)) + 1 / 49
      ≤ (3/8) * Real.sqrt ((N:ℝ) - (S.card:ℝ)) := by
    have h1 : (2/7) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) / (N:ℝ))
        ≤ (2/7) * Real.sqrt ((N:ℝ) - (S.card:ℝ)) := mul_le_mul_of_nonneg_left hsq2' (by norm_num)
    have h2 : (1/49:ℝ) ≤ (1/49) * Real.sqrt ((N:ℝ) - (S.card:ℝ)) := by
      have := mul_le_mul_of_nonneg_left hone2 (by norm_num : (0:ℝ) ≤ 1/49)
      linarith
    have h3 : (2/7) * Real.sqrt ((N:ℝ) - (S.card:ℝ)) + (1/49) * Real.sqrt ((N:ℝ) - (S.card:ℝ))
        = (15/49) * Real.sqrt ((N:ℝ) - (S.card:ℝ)) := by ring
    have h4 : (15/49:ℝ) * Real.sqrt ((N:ℝ) - (S.card:ℝ))
        ≤ (3/8) * Real.sqrt ((N:ℝ) - (S.card:ℝ)) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
    linarith [h1, h2, h3, h4]

  have hlo1 : (5/8) * (S.card:ℝ) ≤ (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 := by
    have hsq : Real.sqrt (S.card:ℝ) ≤ (S.card:ℝ) := by
      have h1 : (S.card:ℝ) ≥ 1 := htR
      have h2 : (Real.sqrt (S.card:ℝ)) ^ 2 = (S.card:ℝ) := Real.sq_sqrt hcard0
      nlinarith only [h1, h2]
    have hhalf' : |(N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z - (S.card:ℝ)|
        ≤ (3/8) * Real.sqrt (S.card:ℝ) := le_trans hhalf hε1
    have habs : (S.card:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z
        ≤ (3/8) * Real.sqrt (S.card:ℝ) := by
      have hh := abs_le.mp hhalf'
      linarith
    have h3 : (3/8) * Real.sqrt (S.card:ℝ) ≤ (3/8) * (S.card:ℝ) :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    linarith
  have hlo2 : (5/8) * ((N:ℝ) - (S.card:ℝ))
      ≤ (N:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 := by
    have hsq : Real.sqrt ((N:ℝ) - (S.card:ℝ)) ≤ (N:ℝ) - (S.card:ℝ) := by
      have h1 : (N:ℝ) - (S.card:ℝ) ≥ 1 := hgapR
      have h2 : (Real.sqrt ((N:ℝ) - (S.card:ℝ))) ^ 2 = (N:ℝ) - (S.card:ℝ) := Real.sq_sqrt hgap0
      nlinarith only [h1, h2]
    have hhalf' : |(N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z - (S.card:ℝ)|
        ≤ (3/8) * Real.sqrt ((N:ℝ) - (S.card:ℝ)) := le_trans hhalf hε2
    have habs : (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z - (S.card:ℝ)
        ≤ (3/8) * Real.sqrt ((N:ℝ) - (S.card:ℝ)) := by
      have hh := abs_le.mp hhalf'
      linarith
    have h3 : (3/8) * Real.sqrt ((N:ℝ) - (S.card:ℝ)) ≤ (3/8) * ((N:ℝ) - (S.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    linarith

  have hest := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.aeEstimate_mem
    (BHMTTh17.exactCountM₀ N) z
  have e1 : (0:ℝ) ≤ (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 := by
    have hh := mul_nonneg hNpos.le hest.1
    linarith
  have e2 : (0:ℝ) ≤ (N:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1 := by
    have hh := mul_le_mul_of_nonneg_left hest.2 hNpos.le
    linarith
  have f1 : (0:ℝ) ≤ (5/8) * (S.card:ℝ) := by positivity
  have f2 : (0:ℝ) ≤ (5/8) * ((N:ℝ) - (S.card:ℝ)) := by positivity
  have hprod : (5/8) * (S.card:ℝ) * ((5/8) * ((N:ℝ) - (S.card:ℝ)))
      ≤ ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1) *
        ((N:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1) :=
    mul_le_mul hlo1 hlo2 f2 e1
  have hsqprod : Real.sqrt (((5/8) * (S.card:ℝ)) * ((5/8) * ((N:ℝ) - (S.card:ℝ))))
      ≤ Real.sqrt (((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1) *
        ((N:ℝ) - (N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z + 1)) :=
    Real.sqrt_le_sqrt hprod
  rw [BHMTTh17.exactCountRough]
  have hid4 : Real.sqrt (((5/8) * (S.card:ℝ)) * ((5/8) * ((N:ℝ) - (S.card:ℝ))))
      = (5/8) * Real.sqrt ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) := by
    have hA' : (5/8) * (S.card:ℝ) * ((5/8) * ((N:ℝ) - (S.card:ℝ)))
        = (25/64) * ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) := by ring
    rw [hA']
    have h1 : Real.sqrt ((25/64) * ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))
        = Real.sqrt (25/64) * Real.sqrt ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) :=
      Real.sqrt_mul (by norm_num) ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ)))
    have h2 : Real.sqrt (25/64) = 5/8 := by
      rw [show (25/64:ℝ) = ((5/8)*(5/8) : ℝ) by ring, Real.sqrt_mul_self (by norm_num)]
    rw [h1, h2]
  linarith [hsqprod]

theorem clause11_cost_lower_bound (N : ℕ) (hN : 0 < N) (S : Finset (Fin N))
    (ht1 : 1 ≤ S.card) (htN : S.card < N) :
    (75/32) * Real.sqrt (((S.card:ℝ) + 1) * ((N:ℝ) - (S.card:ℝ) + 1))
      ≤ BHMTTh17.exactCountCostMass hN S (clause11_rough_grid_two_le N hN)
        (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂) := by
  classical
  have hM₀ : 2 ≤ BHMTTh17.exactCountM₀ N := clause11_rough_grid_two_le N hN
  let W : Finset (Fin (BHMTTh17.exactCountM₀ N)) :=
    Finset.univ.filter (fun z => countWindow N (BHMTTh17.exactCountM₀ N) 2 S.card z)
  have hW : (∑ z ∈ W, (aeLaw (BHMTTh17.exactCountM₀ N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).prob z) ≥ 1 / 2 := by
    simpa [W] using! clause11_rough_window_mass N hN S
  have hcardltR : (S.card:ℝ) < (N:ℝ) := by exact_mod_cast htN
  have hcard0 : (0:ℝ) ≤ (S.card:ℝ) := Nat.cast_nonneg _
  have hgap0 : (0:ℝ) ≤ (N:ℝ) - (S.card:ℝ) := by linarith
  have hApos : (0:ℝ) ≤ (S.card:ℝ) * ((N:ℝ) - (S.card:ℝ)) := mul_nonneg hcard0 hgap0
  have hgrid (z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N)) (h1 : z₁ ∈ W) (h2 : z₂ ∈ W) :
      (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) ≤
        (BHMTTh17.exactCountGrid N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
          ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) : ℝ) := by
    have hw1 := clause11_window_rough_ge N hN S ht1 htN z₁ (Finset.mem_filter.mp h1).2
    have hw2 := clause11_window_rough_ge N hN S ht1 htN z₂ (Finset.mem_filter.mp h2).2
    have hmin : (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))
        ≤ min (BHMTTh17.exactCountRough N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
          (BHMTTh17.exactCountRough N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) :=
      le_min hw1 hw2
    have hceil : (30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
        (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) : ℝ) ≤
        (BHMTTh17.exactCountGrid N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
          ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) : ℝ) := by
      rw [BHMTTh17.exactCountGrid]
      exact Nat.le_ceil (30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
        (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)))
    have hmul : (30:ℝ) * ((5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ)))))
        ≤ 30 * min (BHMTTh17.exactCountRough N
          ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
          (BHMTTh17.exactCountRough N
          ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) :=
      mul_le_mul_of_nonneg_left hmin (by norm_num)
    linarith
  let p : Fin (BHMTTh17.exactCountM₀ N) → ℝ := fun z =>
    (aeLaw (BHMTTh17.exactCountM₀ N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).prob z
  let c : Fin (BHMTTh17.exactCountM₀ N) → Fin (BHMTTh17.exactCountM₀ N) → ℝ := fun z₁ z₂ =>
    ((2 * (BHMTTh17.exactCountM₀ N : ℕ) + BHMTTh17.exactCountGrid N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) : ℕ) : ℝ)
  have hpnonneg : ∀ z : Fin (BHMTTh17.exactCountM₀ N), 0 ≤ p z := by
    intro z
    exact (aeLaw (BHMTTh17.exactCountM₀ N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).nonneg z
  have hstep1 : (∑ z₁ : Fin (BHMTTh17.exactCountM₀ N),
        ∑ z₂ : Fin (BHMTTh17.exactCountM₀ N), p z₁ * p z₂ * c z₁ z₂)
      ≥ (∑ z₁ ∈ W, ∑ z₂ ∈ W, p z₁ * p z₂ * c z₁ z₂) := by
    have hinner (z₁ : Fin (BHMTTh17.exactCountM₀ N)) :
        (∑ z₂ : Fin (BHMTTh17.exactCountM₀ N), p z₁ * p z₂ * c z₁ z₂)
          ≥ (∑ z₂ ∈ W, p z₁ * p z₂ * c z₁ z₂) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W) ?_
      intro z₂ _ _
      exact mul_nonneg (mul_nonneg (hpnonneg z₁) (hpnonneg z₂)) (by positivity)
    have houter : (∑ z₁ : Fin (BHMTTh17.exactCountM₀ N),
          (∑ z₂ : Fin (BHMTTh17.exactCountM₀ N), p z₁ * p z₂ * c z₁ z₂))
        ≥ (∑ z₁ : Fin (BHMTTh17.exactCountM₀ N), (∑ z₂ ∈ W, p z₁ * p z₂ * c z₁ z₂)) :=
      Finset.sum_le_sum (fun z₁ _ => hinner z₁)
    have houter' : (∑ z₁ : Fin (BHMTTh17.exactCountM₀ N),
          (∑ z₂ ∈ W, p z₁ * p z₂ * c z₁ z₂))
        ≥ (∑ z₁ ∈ W, (∑ z₂ ∈ W, p z₁ * p z₂ * c z₁ z₂)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W) ?_
      intro z₁ _ _
      exact Finset.sum_nonneg (f := fun z₂ => p z₁ * p z₂ * c z₁ z₂)
        (fun z₂ _ => mul_nonneg (mul_nonneg (hpnonneg z₁) (hpnonneg z₂)) (by positivity))
    linarith
  have hstep2 : (∑ z₁ ∈ W, ∑ z₂ ∈ W, p z₁ * p z₂ * c z₁ z₂)
      ≥ (∑ z₁ ∈ W, ∑ z₂ ∈ W, p z₁ * p z₂ *
        (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ)))))) := by
    apply Finset.sum_le_sum
    intro z₁ hz₁
    apply Finset.sum_le_sum
    intro z₂ hz₂
    have hgc := hgrid z₁ z₂ hz₁ hz₂
    have hgc' : (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) ≤ c z₁ z₂ := by
      have h2 : (BHMTTh17.exactCountGrid N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
            ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) : ℝ)
          ≤ ((2 * (BHMTTh17.exactCountM₀ N : ℕ) + BHMTTh17.exactCountGrid N
            ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
            ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) : ℕ) : ℝ) := by
        have h3 : BHMTTh17.exactCountGrid N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
            ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)
            ≤ 2 * (BHMTTh17.exactCountM₀ N : ℕ) + BHMTTh17.exactCountGrid N
            ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
            ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) := by omega
        exact_mod_cast h3
      exact hgc.trans h2
    exact mul_le_mul_of_nonneg_left hgc' (mul_nonneg (hpnonneg z₁) (hpnonneg z₂))
  let pW : ℝ := ∑ z ∈ W, p z
  have hS : (1/2:ℝ) ≤ pW := by
    have h1 := hW.le
    simpa [p, pW] using! h1
  have hS0 : (0:ℝ) ≤ pW := by
    exact Finset.sum_nonneg (f := fun z => p z) (s := W) fun z _ => hpnonneg z
  have hstep3 : (∑ z₁ ∈ W, ∑ z₂ ∈ W, p z₁ * p z₂ *
        (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))))
      = (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) * (pW * pW) := by
    have hinner (z₁ : Fin (BHMTTh17.exactCountM₀ N)) :
        (∑ z₂ ∈ W, p z₁ * p z₂ * (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))))
          = (p z₁ * pW) * (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]
    have houter : (∑ z₁ ∈ W, (p z₁ * pW) *
          (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))))
        = (pW * pW) * (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    calc
      (∑ z₁ ∈ W, ∑ z₂ ∈ W, p z₁ * p z₂ *
          (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))))
          = ∑ z₁ ∈ W, (p z₁ * pW) *
            (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) := by
              apply Finset.sum_congr rfl
              intro z₁ _
              exact hinner z₁
      _ = (pW * pW) * (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) := houter
      _ = (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) * (pW * pW) := by ring
  have hstep4 : (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) * (1/4)
      ≤ (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) * (pW * pW) := by
    have hprod : (1/4:ℝ) ≤ pW * pW := by
      have h1 : (0:ℝ) ≤ pW * (pW - 1/2) := mul_nonneg hS0 (by linarith)
      nlinarith
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  have hshape : (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) * (1/4)
      ≥ (75/32) * Real.sqrt (((S.card:ℝ) + 1) * ((N:ℝ) - (S.card:ℝ) + 1)) := by
    have h3 : (S.card:ℝ) + 1 ≤ 2 * (S.card:ℝ) := by
      have : (1:ℝ) ≤ (S.card:ℝ) := by exact_mod_cast ht1
      linarith
    have h4 : (N:ℝ) - (S.card:ℝ) + 1 ≤ 2 * ((N:ℝ) - (S.card:ℝ)) := by
      have h1 : S.card + 1 ≤ N := by omega
      have h2 : (S.card:ℝ) + 1 ≤ (N:ℝ) := by exact_mod_cast h1
      have : (1:ℝ) ≤ (N:ℝ) - (S.card:ℝ) := by linarith
      linarith
    have h5 : ((S.card:ℝ) + 1) * ((N:ℝ) - (S.card:ℝ) + 1)
        ≤ 4 * ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) := by
      have h7 := mul_le_mul h3 h4 (by positivity) (by positivity)
      nlinarith
    have h7 : Real.sqrt (((S.card:ℝ) + 1) * ((N:ℝ) - (S.card:ℝ) + 1))
        ≤ 2 * Real.sqrt ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) := by
      have h8 := Real.sqrt_le_sqrt h5
      have h9s : Real.sqrt (4 * ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))
          = 2 * Real.sqrt ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) := by
        have hs : 0 ≤ 2 * Real.sqrt ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))) :=
          mul_nonneg (by norm_num)
            (Real.sqrt_nonneg ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))
        rw [show (4 * ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))
            = (2 * Real.sqrt ((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ)))) ^ 2 by
              rw [mul_pow, Real.sq_sqrt (by positivity)]; ring]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
      rw [h9s] at h8
      exact h8
    have h9 : (75/16 : ℝ) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ)))) ≥
        (75/32) * Real.sqrt (((S.card:ℝ) + 1) * ((N:ℝ) - (S.card:ℝ) + 1)) := by
      nlinarith
    have h10 : (30 * (5/8) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ))))) * (1/4)
        = (75/16) * Real.sqrt (((S.card:ℝ) * ((N:ℝ) - (S.card:ℝ)))) := by ring
    linarith
  have hcost : BHMTTh17.exactCountCostMass hN S hM₀
      (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂)
      = ∑ z₁ : Fin (BHMTTh17.exactCountM₀ N), ∑ z₂ : Fin (BHMTTh17.exactCountM₀ N),
        p z₁ * p z₂ * c z₁ z₂ := rfl
  rw [hcost]
  exact hshape.trans (((hstep3.symm ▸ hstep4).trans hstep2).trans hstep1)

theorem clause11_output_transport (N : ℕ) {M : ℕ} (z : Fin M) :
    countOutput N M z = (BHMTTh17.exactCountOutput N z).toNat := by
  have h : countOutput N M z = Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) := by
    simp [countOutput, countRounded]
  rw [h, BHMTTh17.exactCountOutput]
  exact (Int.floor_toNat _).symm

theorem clause11_output_eq_iff (N : ℕ) {M : ℕ} (t : ℕ) (y : Fin M) :
    countOutput N M y = t ↔ BHMTTh17.exactCountOutput N y = (t : ℤ) := by
  have hfloor : (0:ℝ) ≤ (N : ℝ) * aeEstimate M y + 1 / 2 := by
    have h := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.aeEstimate_mem M y
    have hm : (0:ℝ) ≤ (N : ℝ) * aeEstimate M y := by
      have hh := mul_nonneg (Nat.cast_nonneg N) h.1
      linarith
    linarith
  have hnonneg : (0:ℤ) ≤ BHMTTh17.exactCountOutput N y := by
    rw [BHMTTh17.exactCountOutput]
    exact Int.floor_nonneg.mpr hfloor
  constructor
  · intro h
    have h1 := clause11_output_transport N y
    have h2 : (BHMTTh17.exactCountOutput N y).toNat = t := h1.symm.trans h
    have h3 : BHMTTh17.exactCountOutput N y = (t : ℤ) := by
      have h4 : ((BHMTTh17.exactCountOutput N y).toNat : ℤ) = (t : ℤ) := by
        exact_mod_cast h2
      calc
        BHMTTh17.exactCountOutput N y = ((BHMTTh17.exactCountOutput N y).toNat : ℤ) :=
          (Int.toNat_of_nonneg hnonneg).symm
        _ = (t : ℤ) := h4
    exact h3
  · intro h
    have h1 := clause11_output_transport N y
    have h2 : ((t : ℤ)).toNat = t := by
      have hh := Int.toNat_of_nonneg (show (0:ℤ) ≤ (t:ℤ) by exact_mod_cast (Nat.zero_le t))
      exact_mod_cast hh
    rw [h1, h, h2]

theorem clause11_output_rounding (N : ℕ) {M : ℕ} (z : Fin M) :
    |(countOutput N M z : ℝ) - (N : ℝ) * aeEstimate M z| ≤ 1 / 2 := by
  have hnonneg : (0:ℝ) ≤ (N : ℝ) * aeEstimate M z := by
    have h := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.aeEstimate_mem M z
    have hh := mul_nonneg (Nat.cast_nonneg N) h.1
    linarith
  simpa [countOutput] using! countRounded_abs ((N : ℝ) * aeEstimate M z) hnonneg

theorem clause11_final_grid_le (N : ℕ) (hN : 0 < N)
    (z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N)) :
    exactCountFinalGrid N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) ≤ 31 * (N + 1) := by
  have h1 := clause11_rough_quantity_le N hN z₁
  have h2 := clause11_rough_quantity_le N hN z₂
  have hmin : min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
      (BHMTTh17.exactCountRough N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) ≤ (N:ℝ) + 1 :=
    (min_le_left _ _).trans h1
  have hmin0 : (0:ℝ) ≤ min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
      (BHMTTh17.exactCountRough N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h3 : (30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
      (BHMTTh17.exactCountRough N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) : ℝ) ≤ 30 * ((N:ℝ) + 1) := by
      have hh := mul_le_mul_of_nonneg_left hmin (by norm_num : (0:ℝ) ≤ 30)
      linarith
  have h4 : (exactCountFinalGrid N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) : ℝ)
      < 30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
        (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) + 1 := by
    rw [exactCountFinalGrid, BHMTTh17.exactCountGrid]
    have ha : (30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
      (BHMTTh17.exactCountRough N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) : ℝ) ≤
        (Nat.ceil (30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
      (BHMTTh17.exactCountRough N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂))) : ℝ) :=
      Nat.le_ceil (30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
        (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)))
    have hb : (Nat.ceil (30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
      (BHMTTh17.exactCountRough N
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂))) : ℝ)
      < 30 * min (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁))
        (BHMTTh17.exactCountRough N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    linarith
  have h5 : (exactCountFinalGrid N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) : ℝ) < 30 * (N : ℝ) + 31 := by
    linarith
  have h6 : exactCountFinalGrid N ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
      ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂) < 30 * (N + 1) + 1 := by
    exact_mod_cast h5
  omega

theorem clause11_space_ledger (N : ℕ) (hN : 0 < N)
    (z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N)) :
    exactCountSpaceBits N (exactCountFinalGrid N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) ≤ 4 * stateBits (N + 1) + 5 := by
  have hgrid := clause11_final_grid_le N hN z₁ z₂
  have hmono : Nat.log 2 (exactCountFinalGrid N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) ≤ Nat.log 2 (31 * (N + 1)) :=
    Nat.log_mono_right hgrid
  have hmono' : Nat.log 2 (31 * (N + 1)) ≤ Nat.log 2 (32 * (N + 1)) :=
    Nat.log_mono_right (by omega)
  have hlog : Nat.log 2 (32 * (N + 1)) = Nat.log 2 (N + 1) + 5 := by
    have hx : N + 1 ≠ 0 := by omega
    have e1 : Nat.log 2 ((N + 1) * 2) = Nat.log 2 (N + 1) + 1 := Nat.log_mul_base (by norm_num) hx
    have e2 : Nat.log 2 ((N + 1) * 2 * 2) = Nat.log 2 ((N + 1) * 2) + 1 :=
      Nat.log_mul_base (by norm_num) (by omega)
    have e3 : Nat.log 2 ((N + 1) * 2 * 2 * 2) = Nat.log 2 ((N + 1) * 2 * 2) + 1 :=
      Nat.log_mul_base (by norm_num) (by omega)
    have e4 : Nat.log 2 ((N + 1) * 2 * 2 * 2 * 2) = Nat.log 2 ((N + 1) * 2 * 2 * 2) + 1 :=
      Nat.log_mul_base (by norm_num) (by omega)
    have e5 : Nat.log 2 ((N + 1) * 2 * 2 * 2 * 2 * 2) = Nat.log 2 ((N + 1) * 2 * 2 * 2 * 2) + 1 :=
      Nat.log_mul_base (by norm_num) (by omega)
    have h32 : 32 * (N + 1) = (N + 1) * 2 * 2 * 2 * 2 * 2 := by omega
    rw [h32, e5, e4, e3, e2, e1]
  have hbits : stateBits (exactCountFinalGrid N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) ≤ stateBits (N + 1) + 5 := by
    have h1 : Nat.log 2 (exactCountFinalGrid N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) ≤ Nat.log 2 (N + 1) + 5 := by
      linarith
    simp only [stateBits]
    linarith
  simp only [exactCountSpaceBits, stateBits]
  linarith

theorem clause11_endpoint (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) :
    (2/3 ≤ BHMTTh17.exactCountSuccessMass hN S (clause11_rough_grid_two_le N hN)
        (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂)) ∧
    (BHMTTh17.exactCountCostMass hN S (clause11_rough_grid_two_le N hN)
        (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂) ≤
      1000 * Real.sqrt (((S.card : ℝ) + 1) * ((N : ℝ) - (S.card : ℝ) + 1))) ∧
    (∀ t : ℕ, 1 ≤ t → t < N → S.card = t →
      (75/32) * Real.sqrt (((t : ℝ) + 1) * ((N : ℝ) - (t : ℝ) + 1))
        ≤ BHMTTh17.exactCountCostMass hN S (clause11_rough_grid_two_le N hN)
          (fun z₁ z₂ => clause11_final_grid_two_le N hN z₁ z₂)) ∧
    (∀ z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N),
      exactCountSpaceBits N (exactCountFinalGrid N
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
        ((N:ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) ≤ 4 * stateBits (N + 1) + 5) := by
  have hbounds := clause11_frozen_bounds N hN S
  refine ⟨hbounds.1, hbounds.2, ?_, ?_⟩
  · intro t ht1 htN hcard
    have hsub : S.card = t := hcard
    subst hsub
    exact clause11_cost_lower_bound N hN S ht1 htN
  · intro z₁ z₂
    exact clause11_space_ledger N hN z₁ z₂

theorem clause9_record_native_ledger_eq {N : ℕ} (hN : 0 < N) (M : ℕ) (hM : 0 < M) :
    basicApproxCountRecordEvaluations N M = M := by
  letI : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a = b)
  unfold basicApproxCountRecordEvaluations aeSourceEvaluations
  exact ae_source_evaluation_count (I := Fin N) M hM (QFTMatrix N) ⟨0, hN⟩

theorem clause9_record_native_circuit_queries {N : ℕ} (hN : 0 < N) (M : ℕ) (hM : 0 < M) :
    QueryCount (aePaddedAECircuit (I := Fin N) M (QFTMatrix N) ⟨0, hN⟩) = M ∧
      GateCount (aePaddedAECircuit (I := Fin N) M (QFTMatrix N) ⟨0, hN⟩)
        = 5 * (M - 1) + 3 := by
  refine ⟨ae_padded_query_count M hM (QFTMatrix N) ⟨0, hN⟩,
    ae_padded_gate_count M hM (QFTMatrix N) ⟨0, hN⟩⟩

theorem clause9_native_cost_eq_frozen {N : ℕ} (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
    basicApproxCountNativeCost N ε ω = basicApproxCountTotalCost N ε ω := by
  have hfin : basicApproxCountRecordEvaluations N
      (basicApproxCountFinalM ε (basicApproxCountStop N ω))
      = basicApproxCountFinalM ε (basicApproxCountStop N ω) :=
    clause9_record_native_ledger_eq hN _ (by
      have hpos := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.basicApproxCount_final_grid_pos
        N ε hε ω
      omega)
  have hs : (∑ l : Fin (basicApproxCountLoopCap N),
      if l.val < basicApproxCountStop N ω then
        basicApproxCountRecordEvaluations N (2 * 2 ^ l.val) else 0)
      = (∑ l : Fin (basicApproxCountLoopCap N),
        if l.val < basicApproxCountStop N ω then 2 * 2 ^ l.val else 0) := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l.val < basicApproxCountStop N ω
    · rw [if_pos hl, if_pos hl]
      exact clause9_record_native_ledger_eq hN _ (by positivity)
    · rw [if_neg hl, if_neg hl]
  unfold basicApproxCountNativeCost basicApproxCountTotalCost
  rw [hfin, hs]

theorem clause9_cost_mass_eq_frozen {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (hε : 0 < ε) :
    basicApproxCountProcedureCostMass hN S ε =
      ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountPrefixWeight hN S ω *
          ((basicApproxCountTotalCost N ε ω : ℕ) : ℝ) := by
  unfold basicApproxCountProcedureCostMass
  apply Finset.sum_congr rfl
  intro ω _
  rw [clause9_native_cost_eq_frozen hN ε hε ω]

theorem clause9_expected_cost_zero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hS : S.card = 0) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    40 * Real.pi ^ 2 / ε * Real.sqrt (N : ℝ) ≤ basicApproxCountProcedureCostMass hN S ε ∧
      basicApproxCountProcedureCostMass hN S ε ≤
        (9 + 80 * Real.pi ^ 2 / ε) * Real.sqrt (N : ℝ) := by
  obtain ⟨hzero, _⟩ := bhmt_basic_approx_count_expected_cost N S hN ε hε hε1
  obtain ⟨hlo, hhi⟩ := hzero hS
  rw [clause9_cost_mass_eq_frozen hN S ε hε]
  exact ⟨hlo, hhi⟩

theorem clause9_expected_cost_positive {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hS : 0 < S.card) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    7 * Real.pi / 2 * (1 / ε) * Real.sqrt ((N : ℝ) / (S.card : ℝ))
        ≤ basicApproxCountProcedureCostMass hN S ε ∧
      basicApproxCountProcedureCostMass hN S ε ≤
        2000 * (1 / ε) * Real.sqrt ((N : ℝ) / (S.card : ℝ)) := by
  obtain ⟨_, hpos⟩ := bhmt_basic_approx_count_expected_cost N S hN ε hε hε1
  obtain ⟨hlo, hhi⟩ := hpos hS
  rw [clause9_cost_mass_eq_frozen hN S ε hε]
  exact ⟨hlo, hhi⟩

theorem clause9_final_grid_ceiling (ε : ℝ) (hε : 0 < ε) (s : ℕ) :
    basicApproxCountRealFinalGrid ε s ≤ (basicApproxCountFinalM ε s : ℝ) ∧
      (basicApproxCountFinalM ε s : ℝ) < basicApproxCountRealFinalGrid ε s + 1 := by
  have hpos : 0 ≤ basicApproxCountRealFinalGrid ε s := by
    have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have h2 : (0 : ℝ) < (2 ^ s : ℝ) := by positivity
    unfold basicApproxCountRealFinalGrid
    positivity
  have hle : basicApproxCountRealFinalGrid ε s ≤ (basicApproxCountFinalM ε s : ℝ) := by
    have h := Nat.le_ceil (basicApproxCountRealFinalGrid ε s)
    exact h
  have hlt : (basicApproxCountFinalM ε s : ℝ) < basicApproxCountRealFinalGrid ε s + 1 := by
    have h := Nat.ceil_lt_add_one hpos
    exact h
  exact ⟨hle, hlt⟩

theorem clause9_final_grid_rounding_cost {N : ℕ} (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
    (basicApproxCountRecordEvaluations N
        (basicApproxCountFinalM ε (basicApproxCountStop N ω)) : ℝ)
      < basicApproxCountRealFinalGrid ε (basicApproxCountStop N ω) + 1 := by
  rw [clause9_record_native_ledger_eq hN _ (by
    have hpos := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.basicApproxCount_final_grid_pos
      N ε hε ω
    omega)]
  exact (clause9_final_grid_ceiling ε hε (basicApproxCountStop N ω)).2

theorem clause9_output_bits {N : ℕ} (M : ℕ) (z : Fin M) :
    countOutput N M z ≤ N ∧ countOutput N M z < 2 ^ stateBits (N + 1) := by
  have hm := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.aeEstimate_mem M z
  have hNpos : (0 : ℝ) ≤ N := by positivity
  have hx : 0 ≤ (N : ℝ) * aeEstimate M z + 1 / 2 := by
    linarith [mul_nonneg hNpos hm.1]
  have h1 : (N : ℝ) * aeEstimate M z + 1 / 2 < ((N + 1 : ℕ) : ℝ) := by
    have h2 : aeEstimate M z ≤ 1 := hm.2
    have h3 : (N : ℝ) * aeEstimate M z ≤ (N : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h2 hNpos
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hlt : countOutput N M z < N + 1 := by
    unfold countOutput countRounded
    exact (Nat.floor_lt hx).2 h1
  have h5 : N + 1 < 2 ^ stateBits (N + 1) := by
    have h6 : N + 1 < 2 ^ (Nat.log 2 (N + 1)).succ :=
      Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (N + 1)
    have h7 : (Nat.log 2 (N + 1)).succ = stateBits (N + 1) := by simp [stateBits]
    rw [← h7]
    exact h6
  constructor
  · omega
  · omega

theorem clause9_output_transport {N : ℕ} (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω))) :
    (countOutput N (basicApproxCountFinalM ε (basicApproxCountStop N ω)) y : ℤ)
      = basicApproxCountOutput N ε ω y := by
  have hm := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.aeEstimate_mem
    (basicApproxCountFinalM ε (basicApproxCountStop N ω)) y
  have hNpos : (0 : ℝ) ≤ N := by positivity
  have hpos : 0 ≤ (N : ℝ) * aeEstimate
      (basicApproxCountFinalM ε (basicApproxCountStop N ω)) y + 1 / 2 := by
    linarith [mul_nonneg hNpos hm.1]
  unfold countOutput countRounded
  rw [Int.natCast_floor_eq_floor hpos]
  rfl

private theorem clause9_two_pow_bounds : ∀ n : ℕ, 1 ≤ n →
    (2 : ℝ) * n ≤ (2 : ℝ) ^ n ∧ (2 : ℝ) ≤ (2 : ℝ) ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : 1 ≤ k
    · obtain ⟨h1, h2⟩ := ih hk
      rw [pow_succ]
      constructor
      · have h3 : (2 : ℝ) * ↑(k + 1) = (2 : ℝ) * ↑k + 2 := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
        rw [h3]
        nlinarith [h1, h2]
      · nlinarith [h2]
    · have hk0 : k = 0 := by omega
      subst hk0
      norm_num

theorem clause9_loop_cap_le (N : ℕ) (hN : 0 < N) :
    basicApproxCountLoopCap N ≤ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hN0 : (0 : ℝ) ≤ N := by exact_mod_cast (Nat.zero_le N)
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have h3 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
    have h4 : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := mul_nonneg hN0 h3
    have hsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    exact Real.sqrt_le_iff.mpr ⟨hN0, hsq⟩
  have htwo : (2 : ℝ) * (N : ℝ) ≤ (2 : ℝ) ^ N := (clause9_two_pow_bounds N hN).1
  have hmain : (2 : ℝ) * Real.sqrt (N : ℝ) ≤ (2 : ℝ) ^ N :=
    le_trans (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) htwo
  have hlogb : Real.logb 2 (2 * Real.sqrt (N : ℝ)) ≤ (N : ℝ) := by
    have hpos : (0 : ℝ) < 2 * Real.sqrt (N : ℝ) := by
      have hsq : (0 : ℝ) < Real.sqrt (N : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast hN)
      positivity
    rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hpos]
    simpa [Real.rpow_natCast] using! hmain
  have hceil : ⌈Real.logb 2 (2 * Real.sqrt (N : ℝ))⌉₊ ≤ N := by
    have h1 : ⌈Real.logb 2 (2 * Real.sqrt (N : ℝ))⌉₊ ≤ ⌈(N : ℝ)⌉₊ :=
      Nat.ceil_le_ceil hlogb
    simpa using! h1
  unfold basicApproxCountLoopCap
  exact hceil

theorem clause9_space_ledger {N : ℕ} (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
    basicApproxCountSpaceBits N (basicApproxCountFinalM ε (basicApproxCountStop N ω))
      = stateBits (basicApproxCountFinalM ε (basicApproxCountStop N ω))
        + stateBits (N + 1)
        + stateBits (basicApproxCountLoopCap N + 1) ∧
      0 < basicApproxCountFinalM ε (basicApproxCountStop N ω) ∧
      stateBits (basicApproxCountLoopCap N + 1) ≤ stateBits (N + 1) := by
  refine ⟨rfl, ?_, ?_⟩
  · have hpos :=
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.basicApproxCount_final_grid_pos N ε hε ω
    omega
  · have hcap : basicApproxCountLoopCap N ≤ N := clause9_loop_cap_le N hN
    have h1 : basicApproxCountLoopCap N + 1 ≤ N + 1 := by omega
    have h2 : Nat.log 2 (basicApproxCountLoopCap N + 1) ≤ Nat.log 2 (N + 1) :=
      Nat.log_mono_right (b := 2) h1
    unfold stateBits
    omega

private theorem clause44_cost_flip {h n : ℕ} (hh : 0 < h) (hn : 0 < n) :
    (400:ℝ)/Real.sqrt (((h:ℝ))/((n:ℝ))) = 400 * Real.sqrt (((n:ℝ))/((h:ℝ))) := by
  have h0 : (0:ℝ) ≤ (h:ℝ) := Nat.cast_nonneg _
  have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_div h0, Real.sqrt_div h1]
  have hhp : (0:ℝ) < Real.sqrt ((h:ℝ)) := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hnp : (0:ℝ) < Real.sqrt ((n:ℝ)) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  field_simp

private theorem clause44_per_instance_aa_cost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (T : ℕ) (f : Fin n → Bool)
    (hf : 0 < BHMTTh6.heuristicGoodCount n G f) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (BHMTQSearch.qSearchLoop (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
          (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
          (Finset.univ.filter (fun r => f (G f r) = true)) T 0)
        (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal
          (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ))) := by
  have hmass := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.prepared_qft_mark_mass n hn
    (Finset.univ.filter (fun r => f (G f r) = true))
  have hpos : 0 < Qatlib.Foundations.PureStateMath.MeasureProb
      (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n) (⟨0, hn⟩ : Fin n))
      (Finset.univ.filter (fun r => f (G f r) = true)) := by
    rw [hmass]
    exact div_pos (by exact_mod_cast hf) (by exact_mod_cast hn)
  have hcard : (Finset.univ.filter (fun r => f (G f r) = true)).card
      = BHMTTh6.heuristicGoodCount n G f := rfl
  have hG1 := BHMTQSearch.bhmt_theorem3_qsearch (Fin n) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
    (Finset.univ.filter (fun r => f (G f r) = true)) T
  have hE := (hG1.2.2 hpos).1
  rw [hmass, hcard, clause44_cost_flip hf hn] at hE
  exact hE

theorem clause44_quantum_aa_cost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool)) (T : ℕ)
    (hsupp : ∀ f ∈ D.support, 0 < BHMTTh6.heuristicGoodCount n G f) :
    heuristicQuantumAaCost hn G D T ≤
      ENNReal.ofReal (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) := by
  simp only [heuristicQuantumAaCost]
  have hxnn : ∀ f : Fin n → Bool,
      (0:ℝ) ≤ (n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ) :=
    fun f => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hCS : ∑ f : Fin n → Bool, (D f).toReal
        * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ))
      ≤ Real.sqrt (BHMTTh6.heuristicClassicalTime n G D) := by
    have hsq := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset (Fin n → Bool))
      (r := fun f => (D f).toReal
        * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))
      (f := fun f => (D f).toReal)
      (g := fun f => (D f).toReal * ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))
      (fun f _ => ENNReal.toReal_nonneg)
      (fun f _ => mul_nonneg (ENNReal.toReal_nonneg) (hxnn f))
      (fun f _ => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (hxnn f)]
        ring))
    have h1 : ∑ f : Fin n → Bool, (D f).toReal = 1 := by
      rw [← ENNReal.toReal_sum (fun a _ => ne_of_lt
        (lt_of_le_of_lt (PMF.coe_le_one D a) (by norm_num)))]
      rw [show ∑ f : Fin n → Bool, (D f : ℝ≥0∞) = 1 from
        (hasSum_fintype (fun f => (D f : ℝ≥0∞))).unique (PMF.hasSum_coe_one D)]
      exact ENNReal.toReal_one
    have hT2 : (Real.sqrt (BHMTTh6.heuristicClassicalTime n G D))^2
        = BHMTTh6.heuristicClassicalTime n G D :=
      Real.sq_sqrt (Finset.sum_nonneg (fun f _ => mul_nonneg ENNReal.toReal_nonneg
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
    have hT : (∑ f : Fin n → Bool, (D f).toReal)
        * ∑ f : Fin n → Bool, (D f).toReal
            * ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ))
        = (Real.sqrt (BHMTTh6.heuristicClassicalTime n G D))^2 := by
      rw [h1, one_mul, hT2]
      rfl
    exact le_of_sq_le_sq (hsq.trans_eq hT) (Real.sqrt_nonneg _)
  have hsum1 : ∑ f : Fin n → Bool, (D f) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (BHMTQSearch.qSearchLoop (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
          (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
          (Finset.univ.filter (fun r => f (G f r) = true)) T 0)
        (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ∑ f : Fin n → Bool, ENNReal.ofReal ((D f).toReal
          * (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))) := by
    refine Finset.sum_le_sum (fun f _ => ?_)
    by_cases hmem : f ∈ D.support
    · have hE := clause44_per_instance_aa_cost hn G T f (hsupp f hmem)
      refine le_trans (mul_le_mul_right hE _) ?_
      have hDne : D f ≠ ⊤ := ne_of_lt
        (lt_of_le_of_lt (PMF.coe_le_one D f) (by norm_num))
      have hDeq : (D f) * ENNReal.ofReal
            (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))
          = ENNReal.ofReal ((D f).toReal
              * (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hDne]
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact hDeq.le
    · have hz : D f = 0 := by
        by_contra hcon
        exact hmem ((PMF.mem_support_iff D f).mpr hcon)
      rw [hz, zero_mul]
      exact zero_le
  refine le_trans hsum1 ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hre : ∀ f : Fin n → Bool, (D f).toReal
      * (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))
      = 400 * ((D f).toReal
          * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ))) :=
    fun f => by ring
  rw [Finset.sum_congr rfl (fun f _ => hre f), ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hCS (by norm_num)

theorem clause44_quantum_full_cost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool)) (T : ℕ)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hsupp : ∀ f ∈ D.support, 0 < BHMTTh6.heuristicGoodCount n G f) :
    heuristicQuantumFullCost hn G D T kappa ≤
      ENNReal.ofReal (400 * (heuristicTrialCost n kappa + 1) *
        Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) := by
  have htrial : (0:ℝ) ≤ heuristicTrialCost n kappa := by
    unfold heuristicTrialCost heuristicDescriptionBits
    have : (0:ℝ) ≤ kappa * (n : ℝ) := mul_nonneg hkappa (Nat.cast_nonneg _)
    linarith
  have hchi := bhmt_theorem6_heuristic n hn G D T hsupp
  have haa := clause44_quantum_aa_cost hn G D T hsupp
  have hrate0 : (0:ℝ≥0∞) ≤ ENNReal.ofReal (heuristicTrialCost n kappa) := bot_le
  have hstep1 : ENNReal.ofReal (heuristicTrialCost n kappa) *
        BHMTTh6.heuristicQuantumChiCost hn G D T
      ≤ ENNReal.ofReal (heuristicTrialCost n kappa) *
          ENNReal.ofReal (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) :=
    mul_le_mul_of_nonneg_left hchi hrate0
  have hstep1' : ENNReal.ofReal (heuristicTrialCost n kappa) *
          ENNReal.ofReal (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D))
      = ENNReal.ofReal (heuristicTrialCost n kappa *
          (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D))) := by
    rw [← ENNReal.ofReal_mul htrial]
  have hstep3 : ENNReal.ofReal (heuristicTrialCost n kappa *
          (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)))
        + ENNReal.ofReal (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D))
      = ENNReal.ofReal (400 * (heuristicTrialCost n kappa + 1) *
          Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  unfold heuristicQuantumFullCost
  calc ENNReal.ofReal (heuristicTrialCost n kappa) *
        BHMTTh6.heuristicQuantumChiCost hn G D T
        + heuristicQuantumAaCost hn G D T
      ≤ ENNReal.ofReal (heuristicTrialCost n kappa) *
          ENNReal.ofReal (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D))
        + heuristicQuantumAaCost hn G D T := add_le_add hstep1 (le_refl _)
    _ = ENNReal.ofReal (heuristicTrialCost n kappa *
          (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)))
        + heuristicQuantumAaCost hn G D T := congrArg (fun x => x + heuristicQuantumAaCost hn G D T) hstep1'
    _ ≤ ENNReal.ofReal (heuristicTrialCost n kappa *
          (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)))
        + ENNReal.ofReal (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) :=
        add_le_add (le_refl _) haa
    _ = ENNReal.ofReal (400 * (heuristicTrialCost n kappa + 1) *
          Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) := hstep3

theorem clause44_same_instance_output {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (T : ℕ) (f : Fin n → Bool)
    (_hf : 0 < BHMTTh6.heuristicGoodCount n G f) :
    ∀ out ∈ PMF.support
        (BHMTQSearch.qSearchLoop (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
          (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
          (Finset.univ.filter (fun r => f (G f r) = true)) T 0),
      ∀ y, out.1 = some y → f (G f y) = true := by
  have hG1 := BHMTQSearch.bhmt_theorem3_qsearch (Fin n) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
    (Finset.univ.filter (fun r => f (G f r) = true)) T
  intro out hout y hy
  have hyS := (hG1.1 out hout y hy)
  exact (Finset.mem_filter.mp hyS).2

theorem clause44_unsolvable_never_outputs {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (T : ℕ) (f : Fin n → Bool)
    (hf : BHMTTh6.heuristicGoodCount n G f = 0) :
    ∀ out ∈ PMF.support
        (BHMTQSearch.qSearchLoop (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
          (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
          (Finset.univ.filter (fun r => f (G f r) = true)) T 0),
      out.1 = none := by
  have hmass := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.prepared_qft_mark_mass n hn
    (Finset.univ.filter (fun r => f (G f r) = true))
  have hcard : (Finset.univ.filter (fun r => f (G f r) = true)).card
      = BHMTTh6.heuristicGoodCount n G f := rfl
  have ha : Qatlib.Foundations.PureStateMath.MeasureProb
      (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n) (⟨0, hn⟩ : Fin n))
      (Finset.univ.filter (fun r => f (G f r) = true)) = 0 := by
    rw [hmass, hcard, hf]
    simp
  have hG1 := BHMTQSearch.bhmt_theorem3_qsearch (Fin n) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
    (Finset.univ.filter (fun r => f (G f r) = true)) T
  exact fun out hout => (hG1.2.1 ha out hout)

theorem clause44_classical_time_lower {n : ℕ} (_hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool))
    (hsupp : ∀ f ∈ D.support, 0 < BHMTTh6.heuristicGoodCount n G f) :
    (1:ℝ) ≤ BHMTTh6.heuristicClassicalTime n G D := by
  have hle : ∀ f : (Fin n → Bool),
      BHMTTh6.heuristicGoodCount n G f ≤ n := by
    intro f
    exact (Finset.card_le_univ _).trans (by simp)
  have hpoint : ∀ f : (Fin n → Bool),
      (if f ∈ D.support then (D f).toReal else 0) = (D f).toReal := by
    intro f
    by_cases h : f ∈ D.support
    · simp [h]
    · have hz : D f = 0 := by
        by_contra hc
        exact h ((PMF.mem_support_iff D f).mpr hc)
      simp [h, hz]
  have hone : (∑ f : (Fin n → Bool),
      (if f ∈ D.support then (D f).toReal else 0)) = 1 := by
    rw [Finset.sum_congr rfl (fun f _ => hpoint f)]
    have h1 : ∑ f : Fin n → Bool, (D f).toReal = 1 := by
      rw [← ENNReal.toReal_sum (fun a _ => ne_of_lt
        (lt_of_le_of_lt (PMF.coe_le_one D a) (by norm_num)))]
      rw [show ∑ f : Fin n → Bool, (D f : ℝ≥0∞) = 1 from
        (hasSum_fintype (fun f => (D f : ℝ≥0∞))).unique (PMF.hasSum_coe_one D)]
      exact ENNReal.toReal_one
    exact h1
  have hsum : (1:ℝ) ≤ ∑ f : (Fin n → Bool),
      (D f).toReal * ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)) := by
    refine hone.symm.le.trans (Finset.sum_le_sum (fun f _ => ?_))
    by_cases hmem : f ∈ D.support
    · have hf0 := hsupp f hmem
      have hden : (0:ℝ) < ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ) := by
        exact_mod_cast hf0
      have hleN : ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ) ≤ (n : ℝ) := by
        have hle' := hle f
        exact_mod_cast hle'
      have hle'' : (1:ℝ) ≤ (n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ) := by
        rw [le_div_iff₀ hden]
        linarith
      rw [if_pos hmem]
      simpa using! mul_le_mul_of_nonneg_left hle'' (ENNReal.toReal_nonneg)
    · have hz : D f = 0 := by
        by_contra hc
        exact hmem ((PMF.mem_support_iff D f).mpr hc)
      simp [hmem, hz]
  unfold BHMTTh6.heuristicClassicalTime
  exact hsum

theorem clause44_classical_vs_quantum {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool)) (T : ℕ)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hsupp : ∀ f ∈ D.support, 0 < BHMTTh6.heuristicGoodCount n G f) :
    heuristicClassicalFullCost n G D kappa ≥
      (Real.sqrt (BHMTTh6.heuristicClassicalTime n G D) / 800) *
        ENNReal.toReal (heuristicQuantumFullCost hn G D T kappa) := by
  have htrial : (1:ℝ) ≤ heuristicTrialCost n kappa := by
    unfold heuristicTrialCost heuristicDescriptionBits
    have : (0:ℝ) ≤ kappa * (n : ℝ) := mul_nonneg hkappa (Nat.cast_nonneg _)
    linarith
  have hfull := clause44_quantum_full_cost hn G D T kappa hkappa hsupp
  have hfullLt : heuristicQuantumFullCost hn G D T kappa < ∞ :=
    lt_of_le_of_lt hfull (ENNReal.ofReal_lt_top)
  have hfullNe : heuristicQuantumFullCost hn G D T kappa ≠ ∞ := ne_of_lt hfullLt
  have hboundNe : ENNReal.ofReal (400 * (heuristicTrialCost n kappa + 1) *
        Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hQ : ENNReal.toReal (heuristicQuantumFullCost hn G D T kappa)
      ≤ 400 * (heuristicTrialCost n kappa + 1) *
        Real.sqrt (BHMTTh6.heuristicClassicalTime n G D) := by
    have h1 := (ENNReal.toReal_le_toReal hfullNe hboundNe).mpr hfull
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hT0 : (0:ℝ) ≤ BHMTTh6.heuristicClassicalTime n G D := by
    exact Finset.sum_nonneg (fun f _ => mul_nonneg ENNReal.toReal_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hTpos : (0:ℝ) < BHMTTh6.heuristicClassicalTime n G D :=
    lt_of_lt_of_le (by norm_num) (clause44_classical_time_lower hn G D hsupp)
  calc (Real.sqrt (BHMTTh6.heuristicClassicalTime n G D) / 800) *
        ENNReal.toReal (heuristicQuantumFullCost hn G D T kappa)
      ≤ (Real.sqrt (BHMTTh6.heuristicClassicalTime n G D) / 800) *
          (400 * (heuristicTrialCost n kappa + 1) *
            Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = (heuristicTrialCost n kappa + 1) / 2 *
          (Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) ^ 2 := by ring
    _ = (heuristicTrialCost n kappa + 1) / 2 *
          BHMTTh6.heuristicClassicalTime n G D := by
        rw [Real.sq_sqrt hT0]
    _ ≤ heuristicTrialCost n kappa *
          BHMTTh6.heuristicClassicalTime n G D := by
        have hhalf : (heuristicTrialCost n kappa + 1) / 2 ≤ heuristicTrialCost n kappa := by
          linarith
        exact mul_le_mul_of_nonneg_right hhalf hT0
    _ = heuristicClassicalFullCost n G D kappa := rfl

private theorem sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith [sq_nonneg (b - a)]

private theorem sq_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  nlinarith [sq_nonneg (a - b)]

theorem walkGoal_window_le_first {N t : ℕ} (hN : 0 < N) (M : ℕ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 < ε) (_het : 1 ≤ ε * (t : ℝ)) (htN : t ≤ N) (ht1 : 1 ≤ t)
    (hscale : (M:ℝ) ≥ approxCountScaleFirst N t ε) :
    2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ) +
        Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2 ≤ ε * (t:ℝ) / 3 := by
  have hN0 : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have htN0 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast htN
  have ht10 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
  have hNm : 0 ≤ (N:ℝ) - (t:ℝ) := by linarith
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hsqrtε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε

  have hMf : 10 * Real.pi * (M:ℝ) ≤ (approxCountFinalM M : ℝ) := by
    unfold approxCountFinalM
    exact Nat.le_ceil _
  have hMfpos : 0 < (approxCountFinalM M : ℝ) := by
    have : (0:ℝ) < 10 * Real.pi * (M:ℝ) := by positivity
    linarith

  have hscale' : (M:ℝ) ≥ (1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) *
      (1 + Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)))) := by
    simpa [approxCountScaleFirst] using! hscale
  have hB0 : 0 ≤ Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ))) := by positivity
  have hX0 : 0 ≤ (1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) := by positivity

  have hfirst : (1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) ≤ (M:ℝ) := by
    have h2 : 0 ≤ (1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) *
        Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ))) := mul_nonneg hX0 hB0
    linarith

  have hW2 : ((1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) *
      Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)))) ^ 2
      = ((N:ℝ) - (t:ℝ)) / (ε ^ 2 * ((t:ℝ) + 1)) := by
    rw [mul_pow, mul_pow]
    have h1 : (1 / Real.sqrt ε) ^ 2 = 1 / ε := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hε)]
      field_simp
    have h3 : (Real.sqrt ((N:ℝ) / ((t:ℝ) + 1))) ^ 2 = (N:ℝ) / ((t:ℝ) + 1) :=
      Real.sq_sqrt (by positivity)
    have h4 : (Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)))) ^ 2
        = ((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)) := Real.sq_sqrt (by positivity)
    rw [h1, h3, h4]
    field_simp
  have hMge : (M:ℝ) ≥ (1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) *
      Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ))) := by
    have h2 : 0 ≤ Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ))) := hB0
    linarith
  have hM2 : (M:ℝ) ^ 2 ≥ ((N:ℝ) - (t:ℝ)) / (ε ^ 2 * ((t:ℝ) + 1)) := by
    have h1 : ((N:ℝ) - (t:ℝ)) / (ε ^ 2 * ((t:ℝ) + 1)) ≤ (M:ℝ) ^ 2 := by
      have h2 := sq_le_sq (mul_nonneg hX0 hB0) hMge
      rw [hW2] at h2
      exact h2
    exact h1
  have hεM2 : (ε * (M:ℝ)) ^ 2 ≥ ((N:ℝ) - (t:ℝ)) / ((t:ℝ) + 1) := by
    rw [mul_pow]
    have h1 : (0:ℝ) < (t:ℝ) + 1 := by linarith
    have h3 : ((N:ℝ) - (t:ℝ)) / (ε ^ 2 * ((t:ℝ) + 1)) ≤ (M:ℝ) ^ 2 := hM2
    have h4 : (0:ℝ) < ε ^ 2 * ((t:ℝ) + 1) := by positivity
    have h5 := (div_le_iff₀ h4).mp h3
    exact (div_le_iff₀ h1).2 (by linarith)
  have hepsM : Real.sqrt (((N:ℝ) - (t:ℝ)) / ((t:ℝ) + 1)) ≤ ε * (M:ℝ) := by
    exact (Real.sqrt_le_iff).2 ⟨mul_nonneg hε.le hM0.le, hεM2⟩

  have hwin1 : 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ)
      ≤ Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (5 * (M:ℝ)) := by
    have h1 : 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ)
        ≤ 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (10 * Real.pi * (M:ℝ)) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (approxCountFinalM M : ℝ))
        (by positivity : (0:ℝ) < 10 * Real.pi * (M:ℝ))]
      exact mul_le_mul_of_nonneg_left hMf (by positivity)
    have h2 : 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (10 * Real.pi * (M:ℝ))
        = Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (5 * (M:ℝ)) := by
      field_simp
      ring
    rw [← h2]
    exact h1
  have hwin2 : Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2
      ≤ (N:ℝ) / (100 * (M:ℝ) ^ 2) := by
    have h1 : Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2
        ≤ Real.pi ^ 2 * (N:ℝ) / (10 * Real.pi * (M:ℝ)) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (approxCountFinalM M : ℝ) ^ 2)
        (by positivity : (0:ℝ) < (10 * Real.pi * (M:ℝ)) ^ 2)]
      exact mul_le_mul_of_nonneg_left (by
        have : (10 * Real.pi * (M:ℝ)) ^ 2 ≤ (approxCountFinalM M : ℝ) ^ 2 :=
          sq_le_sq (by positivity) hMf
        linarith) (by positivity)
    have h2 : Real.pi ^ 2 * (N:ℝ) / (10 * Real.pi * (M:ℝ)) ^ 2
        = (N:ℝ) / (100 * (M:ℝ) ^ 2) := by
      field_simp
      ring
    rw [← h2]
    exact h1

  have hcost1 : Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (5 * (M:ℝ))
      ≤ ε * Real.sqrt ((t:ℝ) * ((t:ℝ) + 1)) / 5 := by
    have hP2 : (Real.sqrt (((N:ℝ) - (t:ℝ)) / ((t:ℝ) + 1)) *
        Real.sqrt ((t:ℝ) * ((t:ℝ) + 1))) ^ 2 = (t:ℝ) * ((N:ℝ) - (t:ℝ)) := by
      rw [mul_pow]
      have h1 : (Real.sqrt (((N:ℝ) - (t:ℝ)) / ((t:ℝ) + 1))) ^ 2
          = ((N:ℝ) - (t:ℝ)) / ((t:ℝ) + 1) := Real.sq_sqrt (by positivity)
      have h2 : (Real.sqrt ((t:ℝ) * ((t:ℝ) + 1))) ^ 2
          = (t:ℝ) * ((t:ℝ) + 1) := Real.sq_sqrt (by positivity)
      rw [h1, h2]
      field_simp
    have hQ2 : (ε * (M:ℝ) * Real.sqrt ((t:ℝ) * ((t:ℝ) + 1))) ^ 2
        ≥ (t:ℝ) * ((N:ℝ) - (t:ℝ)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (t:ℝ) * ((t:ℝ) + 1))]
      have h3 : (0:ℝ) < (t:ℝ) + 1 := by linarith
      have h4 : (N:ℝ) - (t:ℝ) ≤ (ε * (M:ℝ)) ^ 2 * ((t:ℝ) + 1) :=
        (div_le_iff₀ h3).mp hεM2
      have h5 : (ε * (M:ℝ)) ^ 2 * ((t:ℝ) * ((t:ℝ) + 1))
          = (ε * (M:ℝ)) ^ 2 * ((t:ℝ) + 1) * (t:ℝ) := by ring
      rw [h5]
      have h6 : ((N:ℝ) - (t:ℝ)) * (t:ℝ) ≤ ((ε * (M:ℝ)) ^ 2 * ((t:ℝ) + 1)) * (t:ℝ) :=
        mul_le_mul_of_nonneg_right h4 (le_trans (by norm_num : (0:ℝ) ≤ 1) ht10)
      linarith [h6]
    have hQ : ε * (M:ℝ) * Real.sqrt ((t:ℝ) * ((t:ℝ) + 1))
        ≥ Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) := by
      have h1 : 0 ≤ ε * (M:ℝ) * Real.sqrt ((t:ℝ) * ((t:ℝ) + 1)) := by positivity
      have h2 : 0 ≤ Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) := by positivity
      have h3 : Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ)))
          = Real.sqrt (((N:ℝ) - (t:ℝ)) / ((t:ℝ) + 1)) *
            Real.sqrt ((t:ℝ) * ((t:ℝ) + 1)) := by
        symm
        apply sq_eq_of_sq_eq (by positivity) (by positivity)
        rw [Real.sq_sqrt (by positivity : 0 ≤ (t:ℝ) * ((N:ℝ) - (t:ℝ)))]
        exact hP2
      rw [h3]
      have h4 := mul_le_mul_of_nonneg_right hepsM
        (Real.sqrt_nonneg ((t:ℝ) * ((t:ℝ) + 1)))
      linarith
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 5 * (M:ℝ))]
    calc Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ)))
          ≤ ε * (M:ℝ) * Real.sqrt ((t:ℝ) * ((t:ℝ) + 1)) := hQ
        _ = ε * Real.sqrt ((t:ℝ) * ((t:ℝ) + 1)) / 5 * (5 * (M:ℝ)) := by ring
  have hcost2 : (N:ℝ) / (100 * (M:ℝ) ^ 2) ≤ ε * ((t:ℝ) + 1) / 100 := by
    have h1 : (M:ℝ) ^ 2 ≥ (1 / ε) * ((N:ℝ) / ((t:ℝ) + 1)) := by
      have h2 : 0 ≤ (1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) := hX0
      have h3 : (1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) ≤ (M:ℝ) := hfirst
      have h4 := sq_le_sq h2 h3
      have h5 : ((1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)))^2
          = (1 / ε) * ((N:ℝ) / ((t:ℝ) + 1)) := by
        rw [mul_pow]
        have h6 : (1 / Real.sqrt ε) ^ 2 = 1 / ε := by
          rw [div_pow, Real.sq_sqrt (le_of_lt hε)]
          field_simp
        have h7 : (Real.sqrt ((N:ℝ) / ((t:ℝ) + 1))) ^ 2 = (N:ℝ) / ((t:ℝ) + 1) :=
          Real.sq_sqrt (by positivity)
        rw [h6, h7]
      rw [h5] at h4
      exact h4
    have h2 : (1 / ε) * ((N:ℝ) / ((t:ℝ) + 1)) = (N:ℝ) / (ε * ((t:ℝ) + 1)) := by
      field_simp
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 100 * (M:ℝ) ^ 2)]
    calc (N:ℝ) ≤ ε * ((t:ℝ) + 1) * (M:ℝ) ^ 2 := by
          have h3 : ε * ((t:ℝ) + 1) * (M:ℝ) ^ 2
              ≥ ε * ((t:ℝ) + 1) * ((1 / ε) * ((N:ℝ) / ((t:ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          have h4 : ε * ((t:ℝ) + 1) *
              ((1 / ε) * ((N:ℝ) / ((t:ℝ) + 1))) = (N:ℝ) := by
            field_simp
          linarith
        _ = ε * ((t:ℝ) + 1) / 100 * (100 * (M:ℝ) ^ 2) := by ring

  calc 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ) +
          Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2
      ≤ Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (5 * (M:ℝ)) +
          (N:ℝ) / (100 * (M:ℝ) ^ 2) := by linarith
    _ ≤ ε * Real.sqrt ((t:ℝ) * ((t:ℝ) + 1)) / 5 + ε * ((t:ℝ) + 1) / 100 := by
          linarith
    _ ≤ ε * (21 * (t:ℝ) + 11) / 100 := by
          have h1 : Real.sqrt ((t:ℝ) * ((t:ℝ) + 1)) ≤ (t:ℝ) + 1/2 := by
            have h2 : 0 ≤ (t:ℝ) * ((t:ℝ) + 1) := by positivity
            have h3 : (t:ℝ) * ((t:ℝ) + 1) ≤ ((t:ℝ) + 1/2) ^ 2 := by nlinarith
            exact (Real.sqrt_le_iff).2 ⟨by positivity, h3⟩
          have h4 : 0 ≤ ε / 5 := by positivity
          have h5 := mul_le_mul_of_nonneg_left h1 h4
          linarith
    _ ≤ ε * (t:ℝ) / 3 := by
          have h1 : (21:ℝ) * (t:ℝ) + 11 ≤ 100 * (t:ℝ) / 3 := by
            have : (1:ℝ) ≤ (t:ℝ) := ht10
            linarith
          have h2 := mul_le_mul_of_nonneg_left h1 hε.le
          linarith [h2]

private theorem walkGoal_final_window_bound {N t : ℕ} (M : ℕ) (hM : 0 < M) :
    2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ) +
        Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2
      ≤ Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (5 * (M:ℝ)) +
          (N:ℝ) / (100 * (M:ℝ) ^ 2) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hMf : 10 * Real.pi * (M:ℝ) ≤ (approxCountFinalM M : ℝ) := by
    unfold approxCountFinalM
    exact Nat.le_ceil _
  have hMfpos : 0 < (approxCountFinalM M : ℝ) := by
    have : (0:ℝ) < 10 * Real.pi * (M:ℝ) := by positivity
    linarith
  have hwin1 : 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ)
      ≤ Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (5 * (M:ℝ)) := by
    have h1 : 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ)
        ≤ 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (10 * Real.pi * (M:ℝ)) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (approxCountFinalM M : ℝ))
        (by positivity : (0:ℝ) < 10 * Real.pi * (M:ℝ))]
      exact mul_le_mul_of_nonneg_left hMf (by positivity)
    have h2 : 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (10 * Real.pi * (M:ℝ))
        = Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (5 * (M:ℝ)) := by
      field_simp
      ring
    rw [← h2]
    exact h1
  have hwin2 : Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2
      ≤ (N:ℝ) / (100 * (M:ℝ) ^ 2) := by
    have h1 : Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2
        ≤ Real.pi ^ 2 * (N:ℝ) / (10 * Real.pi * (M:ℝ)) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (approxCountFinalM M : ℝ) ^ 2)
        (by positivity : (0:ℝ) < (10 * Real.pi * (M:ℝ)) ^ 2)]
      exact mul_le_mul_of_nonneg_left (by
        have : (10 * Real.pi * (M:ℝ)) ^ 2 ≤ (approxCountFinalM M : ℝ) ^ 2 :=
          sq_le_sq (by positivity) hMf
        linarith) (by positivity)
    have h2 : Real.pi ^ 2 * (N:ℝ) / (10 * Real.pi * (M:ℝ)) ^ 2
        = (N:ℝ) / (100 * (M:ℝ) ^ 2) := by
      field_simp
      ring
    rw [← h2]
    exact h1
  linarith

private theorem walkGoal_window_le_second {N t : ℕ} (hN : 0 < N) (M : ℕ) (hM : 0 < M)
    (ε : ℝ) (_hε : 0 < ε) (het : 1 ≤ ε * (t : ℝ)) (htN : t ≤ N) (ht1 : 1 ≤ t)
    (hscale : (M:ℝ) ≥ approxCountScaleSecond N t ε) :
    2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ) +
        Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2 ≤ ε * (t:ℝ) / 3 := by
  have hN0 : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have htN0 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast htN
  have ht10 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
  have hNm : 0 ≤ (N:ℝ) - (t:ℝ) := by linarith
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hC2 : approxCountScaleSecond N t ε ^ 2
      = (t:ℝ) * ((N:ℝ) - (t:ℝ)) + (N:ℝ) + 1 := by
    have h1 : approxCountScaleSecond N t ε
        = Real.sqrt (((t:ℝ) + 1) * ((N:ℝ) - (t:ℝ) + 1)) := rfl
    rw [h1, Real.sq_sqrt (by positivity)]
    ring
  have hC0 : 0 ≤ approxCountScaleSecond N t ε := by
    have : 0 ≤ ((t:ℝ) + 1) * ((N:ℝ) - (t:ℝ) + 1) := by positivity
    exact Real.sqrt_nonneg _
  have hCu : Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) ≤ approxCountScaleSecond N t ε := by
    apply (Real.sqrt_le_iff).2
    refine ⟨hC0, ?_⟩
    rw [hC2]
    have : (0:ℝ) ≤ (N:ℝ) + 1 := by linarith
    linarith
  have hcost1 : Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (5 * (M:ℝ)) ≤ 1 / 5 := by
    have h1 : Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) ≤ (M:ℝ) := by
      exact hCu.trans hscale
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 5 * (M:ℝ))]
    linarith
  have hcost2 : (N:ℝ) / (100 * (M:ℝ) ^ 2) ≤ 1 / 100 := by
    have h1 : (M:ℝ) ^ 2 ≥ (N:ℝ) := by
      have h2 : (M:ℝ) ≥ approxCountScaleSecond N t ε := hscale
      have h3 : approxCountScaleSecond N t ε ^ 2 ≥ (N:ℝ) := by
        rw [hC2]
        have : 0 ≤ (t:ℝ) * ((N:ℝ) - (t:ℝ)) := by positivity
        linarith
      have h4 := sq_le_sq hC0 h2
      linarith
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 100 * (M:ℝ) ^ 2)]
    linarith
  calc 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ) +
          Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2
      ≤ Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (5 * (M:ℝ)) +
          (N:ℝ) / (100 * (M:ℝ) ^ 2) := walkGoal_final_window_bound M hM
    _ ≤ 1 / 5 + 1 / 100 := by linarith
    _ ≤ 1 / 3 := by norm_num
    _ ≤ ε * (t:ℝ) / 3 := by linarith

theorem walkGoal_window_le {N t : ℕ} (hN : 0 < N) (M : ℕ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 < ε) (het : 1 ≤ ε * (t : ℝ)) (htN : t ≤ N) (ht1 : 1 ≤ t)
    (hscale : (M:ℝ) ≥ approxCountScaleFirst N t ε ∨
      (M:ℝ) ≥ approxCountScaleSecond N t ε) :
    2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ) +
        Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2 ≤ ε * (t:ℝ) / 3 := by
  rcases hscale with h | h
  · exact walkGoal_window_le_first hN M hM ε hε het htN ht1 h
  · exact walkGoal_window_le_second hN M hM ε hε het htN ht1 h

private theorem walkGoal_sqrt_two_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 ≤ 2 * y ^ 2) :
    x ≤ Real.sqrt 2 * y := by
  have hz : 0 ≤ Real.sqrt 2 * y := mul_nonneg (Real.sqrt_nonneg _) hy
  by_contra hcon
  have hlt : Real.sqrt 2 * y < x := lt_of_not_ge hcon
  have hsq : (Real.sqrt 2 * y) ^ 2 < x ^ 2 := (sq_lt_sq₀ hz hx).2 hlt
  have hz2 : (Real.sqrt 2 * y) ^ 2 = 2 * y ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  linarith

private theorem walkGoal_eff_prec_one {t : ℕ} {ε : ℝ} : (1:ℝ) ≤ (approxCountEffPrec t ε : ℝ) := by
  have h1 : (0:ℕ) ≤ Nat.floor (ε * (t : ℝ)) := Nat.zero_le _
  have h2 : (0:ℝ) ≤ (Nat.floor (ε * (t : ℝ)) : ℝ) := by exact_mod_cast h1
  unfold approxCountEffPrec
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

private theorem walkGoal_eff_prec_ge {t : ℕ} {ε : ℝ} :
    ε * (t : ℝ) ≤ (approxCountEffPrec t ε : ℝ) := by
  have h := Nat.lt_floor_add_one (ε * (t : ℝ))
  have h' : ε * (t : ℝ) < (approxCountEffPrec t ε : ℝ) := by
    unfold approxCountEffPrec
    simp only [Nat.cast_add, Nat.cast_one]
    exact h
  linarith

private theorem walkGoal_eff_prec_le {t : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (approxCountEffPrec t ε : ℝ) ≤ ε * (t : ℝ) + 1 := by
  have het0 : (0:ℝ) ≤ ε * (t : ℝ) := by positivity
  have hfl := Nat.floor_le het0
  unfold approxCountEffPrec
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

private theorem walkGoal_scale_squares (N t : ℕ) (hN : 0 < N) (ht1 : 1 ≤ t) (htN : t ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ((1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1))) ^ 2
        = (N:ℝ) / (ε * ((t:ℝ) + 1)) ∧
      (Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)))) ^ 2
        = ((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)) ∧
      ((1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1))
        * Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)))) ^ 2
        = ((N:ℝ) - (t:ℝ)) / (ε ^ 2 * ((t:ℝ) + 1)) := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have ht10 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
  have htN0 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast htN
  have hden : (0:ℝ) < (t:ℝ) + 1 := by linarith
  have hlead0 : (0:ℝ) ≤ (N:ℝ) / ((t:ℝ) + 1) := div_nonneg hN0.le (le_of_lt hden)
  have htail0 : (0:ℝ) ≤ ((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)) := by
    have hnm : 0 ≤ (N:ℝ) - (t:ℝ) := by linarith
    have hεN : (0:ℝ) < ε * (N:ℝ) := by positivity
    exact div_nonneg hnm (le_of_lt hεN)
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (le_of_lt hε), Real.sq_sqrt hlead0]
    field_simp
  · rw [Real.sq_sqrt htail0]
  · rw [show ((1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1))
        * Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)))) ^ 2
      = ((1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1))) ^ 2
        * (Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)))) ^ 2 by ring]
    rw [show ((1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1))) ^ 2
      = (1 / Real.sqrt ε) ^ 2 * (Real.sqrt ((N:ℝ) / ((t:ℝ) + 1))) ^ 2 by ring]
    rw [show (1 / Real.sqrt ε) ^ 2 = 1 / ε by
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hε)]]
    rw [Real.sq_sqrt hlead0, Real.sq_sqrt htail0]
    field_simp

private theorem walkGoal_scale_le_sqrt_two_first {N t : ℕ} (hN : 0 < N) (ht1 : 1 ≤ t) (htN : t ≤ N)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    approxCountSourceScale N t ε ≤ Real.sqrt 2 * approxCountScaleFirst N t ε := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have ht10 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
  have htN0 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast htN
  have hNm : 0 ≤ (N:ℝ) - (t:ℝ) := by linarith
  have he_pos : (0:ℝ) < (approxCountEffPrec t ε : ℝ) := by
    linarith [walkGoal_eff_prec_one (t := t) (ε := ε)]
  have he_ge : ε * (t:ℝ) ≤ (approxCountEffPrec t ε : ℝ) := walkGoal_eff_prec_ge (t := t) (ε := ε)
  have he_one : (1:ℝ) ≤ (approxCountEffPrec t ε : ℝ) := walkGoal_eff_prec_one (t := t) (ε := ε)
  have hkey1 : ε * ((t:ℝ) + 1) ≤ 2 * (approxCountEffPrec t ε : ℝ) := by
    linarith
  have hkey2 : ε ^ 2 * (t:ℝ) * ((t:ℝ) + 1) ≤ 2 * (approxCountEffPrec t ε : ℝ) ^ 2 := by
    have h1 : (t:ℝ) + 1 ≤ 2 * (t:ℝ) := by linarith
    have h2 : 0 ≤ ε ^ 2 * (t:ℝ) := by positivity
    have h3 : ε ^ 2 * (t:ℝ) * ((t:ℝ) + 1) ≤ ε ^ 2 * (t:ℝ) * (2 * (t:ℝ)) :=
      mul_le_mul_of_nonneg_left h1 h2
    have h5 : (ε * (t:ℝ)) ^ 2 ≤ (approxCountEffPrec t ε : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) he_ge 2
    linarith [h3, h5]
  set p : ℝ := (1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) with hp
  set q : ℝ := Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ))) with hq
  set S1 : ℝ := Real.sqrt ((N:ℝ) / (approxCountEffPrec t ε : ℝ)) with hS1
  set S2 : ℝ := Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountEffPrec t ε : ℝ) with hS2
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hS10 : 0 ≤ S1 := by positivity
  have hS20 : 0 ≤ S2 := by positivity
  have hsq3 := walkGoal_scale_squares N t hN ht1 htN ε hε
  have hp2 : p ^ 2 = (N:ℝ) / (ε * ((t:ℝ) + 1)) := hsq3.1
  have hq2 : q ^ 2 = ((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ)) := hsq3.2.1
  have hpq2 : (p * q) ^ 2 = ((N:ℝ) - (t:ℝ)) / (ε ^ 2 * ((t:ℝ) + 1)) := hsq3.2.2
  have hS1sq : S1 ^ 2 = (N:ℝ) / (approxCountEffPrec t ε : ℝ) := by
    rw [hS1, Real.sq_sqrt (by positivity)]
  have hS2sq : S2 ^ 2 = ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountEffPrec t ε : ℝ) ^ 2 := by
    rw [hS2, div_pow, Real.sq_sqrt (by positivity : 0 ≤ (t:ℝ) * ((N:ℝ) - (t:ℝ)))]
  have hsq1 : S1 ^ 2 ≤ 2 * p ^ 2 := by
    rw [hS1sq, hp2, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (approxCountEffPrec t ε : ℝ))
      (by positivity : (0:ℝ) < ε * ((t:ℝ) + 1))]
    have hmul : (N:ℝ) * (ε * ((t:ℝ) + 1)) ≤ (2 * (N:ℝ)) * (approxCountEffPrec t ε : ℝ) := by
      calc (N:ℝ) * (ε * ((t:ℝ) + 1))
          ≤ (N:ℝ) * (2 * (approxCountEffPrec t ε : ℝ)) := mul_le_mul_of_nonneg_left hkey1 hN0.le
        _ = (2 * (N:ℝ)) * (approxCountEffPrec t ε : ℝ) := by ring
    exact hmul
  have h1 : S1 ≤ Real.sqrt 2 * p := walkGoal_sqrt_two_mul hS10 hp0 hsq1
  have hsq2 : S2 ^ 2 ≤ 2 * (p * q) ^ 2 := by
    rw [hS2sq, hpq2, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (approxCountEffPrec t ε : ℝ) ^ 2)
      (by positivity : (0:ℝ) < ε ^ 2 * ((t:ℝ) + 1))]
    have hbr : ε ^ 2 * (t:ℝ) * ((t:ℝ) + 1) - 2 * (approxCountEffPrec t ε : ℝ) ^ 2 ≤ 0 := by
      linarith [hkey2]
    have hmul : ((N:ℝ) - (t:ℝ)) *
        (ε ^ 2 * (t:ℝ) * ((t:ℝ) + 1) - 2 * (approxCountEffPrec t ε : ℝ) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hNm hbr
    linarith [hmul]
  have h2 : S2 ≤ Real.sqrt 2 * (p * q) := walkGoal_sqrt_two_mul hS20 (mul_nonneg hp0 hq0) hsq2
  have hA : approxCountScaleFirst N t ε = p * (1 + q) := by
    unfold approxCountScaleFirst
    rw [hp, hq]
  have hS : approxCountSourceScale N t ε = S1 + S2 := by
    unfold approxCountSourceScale
    rw [hS1, hS2]
  rw [hS, hA]
  have h3 : Real.sqrt 2 * p + Real.sqrt 2 * (p * q) = Real.sqrt 2 * (p * (1 + q)) := by ring
  linarith

private theorem walkGoal_scale_le_sqrt_two_second {N t : ℕ} (hN : 0 < N) (ht1 : 1 ≤ t) (htN : t ≤ N)
    (ε : ℝ) :
    approxCountSourceScale N t ε ≤ Real.sqrt 2 * approxCountScaleSecond N t ε := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have ht10 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
  have htN0 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast htN
  have hNm : 0 ≤ (N:ℝ) - (t:ℝ) := by linarith
  have he_pos : (0:ℝ) < (approxCountEffPrec t ε : ℝ) := by
    linarith [walkGoal_eff_prec_one (t := t) (ε := ε)]
  have he_one : (1:ℝ) ≤ (approxCountEffPrec t ε : ℝ) := walkGoal_eff_prec_one (t := t) (ε := ε)
  set S1 : ℝ := Real.sqrt ((N:ℝ) / (approxCountEffPrec t ε : ℝ)) with hS1
  set S2 : ℝ := Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountEffPrec t ε : ℝ) with hS2
  set C : ℝ := Real.sqrt (((t:ℝ) + 1) * ((N:ℝ) - (t:ℝ) + 1)) with hC
  set D : ℝ := Real.sqrt (N:ℝ) with hD
  set E : ℝ := Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) with hE
  have hS10 : 0 ≤ S1 := by positivity
  have hS20 : 0 ≤ S2 := by positivity
  have hC0 : 0 ≤ C := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hE0 : 0 ≤ E := by positivity
  have h1 : S1 ≤ D := by
    rw [hS1, hD]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ he_pos]
    have hmul : (N:ℝ) * 1 ≤ (N:ℝ) * (approxCountEffPrec t ε : ℝ) :=
      mul_le_mul_of_nonneg_left he_one hN0.le
    linarith [hmul]
  have h2 : S2 ≤ E := by
    rw [hS2, hE]
    rw [div_le_iff₀ he_pos]
    have hmul : Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) * 1
        ≤ Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) * (approxCountEffPrec t ε : ℝ) :=
      mul_le_mul_of_nonneg_left he_one (Real.sqrt_nonneg _)
    linarith [hmul]
  have hD2 : D ^ 2 = (N:ℝ) := by rw [hD, Real.sq_sqrt (by positivity)]
  have hE2 : E ^ 2 = ((t:ℝ) * ((N:ℝ) - (t:ℝ))) := by rw [hE, Real.sq_sqrt (by positivity)]
  have hC2 : C ^ 2 = ((t:ℝ) + 1) * ((N:ℝ) - (t:ℝ) + 1) := by
    rw [hC, Real.sq_sqrt (by positivity)]
  have hAMGM : 2 * D * E ≤ D ^ 2 + E ^ 2 := by nlinarith [sq_nonneg (D - E)]
  have hsum : (D + E) ^ 2 ≤ 2 * (D ^ 2 + E ^ 2) := by nlinarith [sq_nonneg (D - E)]
  have hCdom : (D ^ 2 + E ^ 2) ≤ C ^ 2 := by
    rw [hD2, hE2, hC2]
    have hid : ((t:ℝ) + 1) * ((N:ℝ) - (t:ℝ) + 1)
        = (N:ℝ) + ((t:ℝ) * ((N:ℝ) - (t:ℝ))) + 1 := by ring
    linarith
  have hsq : (S1 + S2) ^ 2 ≤ 2 * C ^ 2 := by
    have hle : S1 + S2 ≤ D + E := by linarith
    have h0 : 0 ≤ S1 + S2 := by linarith
    have h1' : 0 ≤ D + E := by linarith
    have hsq1 : (S1 + S2) ^ 2 ≤ (D + E) ^ 2 := (sq_le_sq₀ h0 h1').2 hle
    linarith [hsq1, hsum, hCdom]
  have hS : approxCountSourceScale N t ε = S1 + S2 := by
    unfold approxCountSourceScale
    rw [hS1, hS2]
  have hCeq : approxCountScaleSecond N t ε = C := by
    unfold approxCountScaleSecond
    rw [hC]
  rw [hS, hCeq]
  exact walkGoal_sqrt_two_mul (by linarith) hC0 hsq

private theorem walkGoal_first_le_two_scale {N t : ℕ} (hN : 0 < N) (ht1 : 1 ≤ t) (htN : t ≤ N)
    (ε : ℝ) (hε : 0 < ε) (het : 1 ≤ ε * (t:ℝ)) :
    approxCountScaleFirst N t ε ≤ 2 * approxCountSourceScale N t ε := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have ht10 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
  have htN0 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast htN
  have hNm : 0 ≤ (N:ℝ) - (t:ℝ) := by linarith
  have he_pos : (0:ℝ) < (approxCountEffPrec t ε : ℝ) := by
    linarith [walkGoal_eff_prec_one (t := t) (ε := ε)]
  have he_le : (approxCountEffPrec t ε : ℝ) ≤ ε * (t:ℝ) + 1 :=
    walkGoal_eff_prec_le (t := t) (ε := ε) hε
  have hkeyA : (approxCountEffPrec t ε : ℝ) ≤ 2 * (ε * ((t:ℝ) + 1)) := by
    have h1 : ε * (t:ℝ) + 1 ≤ 2 * (ε * (t:ℝ)) := by linarith
    have h2 : 2 * (ε * (t:ℝ)) ≤ 2 * (ε * ((t:ℝ) + 1)) := by
      have hx : ε * (t:ℝ) ≤ ε * ((t:ℝ) + 1) := by linarith
      exact mul_le_mul_of_nonneg_left hx (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have hkeyB : (approxCountEffPrec t ε : ℝ) ^ 2 ≤ 4 * (ε ^ 2 * (t:ℝ) * ((t:ℝ) + 1)) := by
    have h1 : (approxCountEffPrec t ε : ℝ) ≤ 2 * (ε * (t:ℝ)) := by
      have : ε * (t:ℝ) + 1 ≤ 2 * (ε * (t:ℝ)) := by linarith
      linarith
    have h2 : 0 ≤ (approxCountEffPrec t ε : ℝ) := by linarith
    have h4 : (approxCountEffPrec t ε : ℝ) ^ 2 ≤ (2 * (ε * (t:ℝ))) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    have h5 : (2 * (ε * (t:ℝ))) ^ 2 = 4 * (ε ^ 2 * (t:ℝ) * (t:ℝ)) := by ring
    have h6 : 4 * (ε ^ 2 * (t:ℝ) * (t:ℝ)) ≤ 4 * (ε ^ 2 * (t:ℝ) * ((t:ℝ) + 1)) := by
      have hx : ε ^ 2 * (t:ℝ) * (t:ℝ) ≤ ε ^ 2 * (t:ℝ) * ((t:ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith : (t:ℝ) ≤ (t:ℝ) + 1) (by positivity)
      exact mul_le_mul_of_nonneg_left hx (by norm_num : (0:ℝ) ≤ 4)
    linarith [h4, h5, h6]
  set p : ℝ := (1 / Real.sqrt ε) * Real.sqrt ((N:ℝ) / ((t:ℝ) + 1)) with hp
  set q : ℝ := Real.sqrt (((N:ℝ) - (t:ℝ)) / (ε * (N:ℝ))) with hq
  set S1 : ℝ := Real.sqrt ((N:ℝ) / (approxCountEffPrec t ε : ℝ)) with hS1
  set S2 : ℝ := Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountEffPrec t ε : ℝ) with hS2
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hS10 : 0 ≤ S1 := by positivity
  have hS20 : 0 ≤ S2 := by positivity
  have hsq3 := walkGoal_scale_squares N t hN ht1 htN ε hε
  have hp2 : p ^ 2 = (N:ℝ) / (ε * ((t:ℝ) + 1)) := hsq3.1
  have hpq2 : (p * q) ^ 2 = ((N:ℝ) - (t:ℝ)) / (ε ^ 2 * ((t:ℝ) + 1)) := hsq3.2.2
  have hS1sq : S1 ^ 2 = (N:ℝ) / (approxCountEffPrec t ε : ℝ) := by
    rw [hS1, Real.sq_sqrt (by positivity)]
  have hS2sq : S2 ^ 2 = ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountEffPrec t ε : ℝ) ^ 2 := by
    rw [hS2, div_pow, Real.sq_sqrt (by positivity : 0 ≤ (t:ℝ) * ((N:ℝ) - (t:ℝ)))]
  have hsqA : p ^ 2 ≤ 2 * S1 ^ 2 := by
    rw [hp2, hS1sq, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ε * ((t:ℝ) + 1))
      (by positivity : (0:ℝ) < (approxCountEffPrec t ε : ℝ))]
    have hmul : (N:ℝ) * (approxCountEffPrec t ε : ℝ) ≤ (2 * (N:ℝ)) * (ε * ((t:ℝ) + 1)) := by
      calc (N:ℝ) * (approxCountEffPrec t ε : ℝ)
          ≤ (N:ℝ) * (2 * (ε * ((t:ℝ) + 1))) := mul_le_mul_of_nonneg_left hkeyA hN0.le
        _ = (2 * (N:ℝ)) * (ε * ((t:ℝ) + 1)) := by ring
    exact hmul
  have h1 : p ≤ Real.sqrt 2 * S1 := walkGoal_sqrt_two_mul hp0 hS10 hsqA
  have hcrossB : ((N:ℝ) - (t:ℝ)) * (approxCountEffPrec t ε : ℝ) ^ 2
      ≤ 4 * ((t:ℝ) * ((N:ℝ) - (t:ℝ))) * (ε ^ 2 * ((t:ℝ) + 1)) := by
    calc ((N:ℝ) - (t:ℝ)) * (approxCountEffPrec t ε : ℝ) ^ 2
        ≤ ((N:ℝ) - (t:ℝ)) * (4 * (ε ^ 2 * (t:ℝ) * ((t:ℝ) + 1))) := by
          exact mul_le_mul_of_nonneg_left hkeyB hNm
      _ = 4 * ((t:ℝ) * ((N:ℝ) - (t:ℝ))) * (ε ^ 2 * ((t:ℝ) + 1)) := by ring
  have hsqB : (p * q) ^ 2 ≤ 4 * S2 ^ 2 := by
    rw [hpq2, hS2sq, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ε ^ 2 * ((t:ℝ) + 1))
      (by positivity : (0:ℝ) < (approxCountEffPrec t ε : ℝ) ^ 2)]
    exact hcrossB
  have h2 : p * q ≤ 2 * S2 := by
    have hpq0 : 0 ≤ p * q := mul_nonneg hp0 hq0
    have hS2sq0 : 0 ≤ S2 ^ 2 := sq_nonneg S2
    nlinarith [hsqB, hpq0, hS2sq0]
  have hA : approxCountScaleFirst N t ε = p + p * q := by
    unfold approxCountScaleFirst
    rw [hp, hq]
    ring
  have hS : approxCountSourceScale N t ε = S1 + S2 := by
    unfold approxCountSourceScale
    rw [hS1, hS2]
  rw [hA, hS]
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    have : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have h1' : Real.sqrt 2 * S1 ≤ 2 * S1 := by
    calc Real.sqrt 2 * S1 = S1 * Real.sqrt 2 := by ring
      _ ≤ S1 * 2 := mul_le_mul_of_nonneg_left hsqrt hS10
      _ = 2 * S1 := by ring
  linarith

private theorem walkGoal_second_le_two_scale_small {N t : ℕ} (hN : 0 < N) (ht1 : 1 ≤ t) (htN : t ≤ N)
    (ε : ℝ) (hε : 0 < ε) (het : ε * (t:ℝ) < 1) :
    approxCountScaleSecond N t ε ≤ 2 * approxCountSourceScale N t ε := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have ht10 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
  have htN0 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast htN
  have hNm : 0 ≤ (N:ℝ) - (t:ℝ) := by linarith
  have hfloor0 : Nat.floor (ε * (t:ℝ)) = 0 := by
    have het0 : (0:ℝ) ≤ ε * (t:ℝ) := by positivity
    have hfl := Nat.floor_le het0
    have hlt : (Nat.floor (ε * (t:ℝ)) : ℝ) < 1 := by linarith
    have hlt' : Nat.floor (ε * (t:ℝ)) < 1 := by exact_mod_cast hlt
    exact Nat.lt_one_iff.mp hlt'
  have he1 : (approxCountEffPrec t ε : ℝ) = 1 := by
    unfold approxCountEffPrec
    simp only [hfloor0, Nat.zero_add, Nat.cast_one]
  set C : ℝ := Real.sqrt (((t:ℝ) + 1) * ((N:ℝ) - (t:ℝ) + 1)) with hC
  set D : ℝ := Real.sqrt (N:ℝ) with hD
  set E : ℝ := Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) with hE
  have hC0 : 0 ≤ C := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hC2 : C ^ 2 = ((t:ℝ) + 1) * ((N:ℝ) - (t:ℝ) + 1) := by
    rw [hC, Real.sq_sqrt (by positivity)]
  have hD2 : D ^ 2 = (N:ℝ) := by rw [hD, Real.sq_sqrt (by positivity)]
  have hE2 : E ^ 2 = ((t:ℝ) * ((N:ℝ) - (t:ℝ))) := by rw [hE, Real.sq_sqrt (by positivity)]
  have hAMGM : 2 * D * E ≤ D ^ 2 + E ^ 2 := by nlinarith [sq_nonneg (D - E)]
  have hTN0 : 0 ≤ (t:ℝ) * ((N:ℝ) - (t:ℝ)) :=
    mul_nonneg (by linarith : (0:ℝ) ≤ (t:ℝ)) hNm
  have hDE0 : 0 ≤ D * E := mul_nonneg hD0 hE0
  have hAMGM' : 2 * D * E ≤ (N:ℝ) + ((t:ℝ) * ((N:ℝ) - (t:ℝ))) := by
    linarith [hAMGM, hD2, hE2]
  have hkey : C ^ 2 ≤ 4 * (D + E) ^ 2 := by
    have hsq : (D + E) ^ 2 = D ^ 2 + 2 * D * E + E ^ 2 := by ring
    rw [hC2, hsq, hD2, hE2]
    have hid : ((t:ℝ) + 1) * ((N:ℝ) - (t:ℝ) + 1)
        = (N:ℝ) + ((t:ℝ) * ((N:ℝ) - (t:ℝ))) + 1 := by ring
    have hmul : 8 * D * E ≤ 4 * ((N:ℝ) + ((t:ℝ) * ((N:ℝ) - (t:ℝ)))) := by
      have h := mul_le_mul_of_nonneg_left hAMGM' (by norm_num : (0:ℝ) ≤ 4)
      linarith [h]
    linarith [hmul, hTN0, hDE0]
  have hfinal : C ≤ 2 * (D + E) := by
    have h0 : 0 ≤ 2 * (D + E) := by linarith
    have hsq : C ^ 2 ≤ (2 * (D + E)) ^ 2 := by
      have hid : (2 * (D + E)) ^ 2 = 4 * (D + E) ^ 2 := by ring
      linarith [hkey, hid]
    exact (sq_le_sq₀ hC0 h0).1 hsq
  have hS : approxCountSourceScale N t ε = D + E := by
    unfold approxCountSourceScale
    rw [he1]
    simp only [div_one]
    rw [← hD, ← hE]
  have hCeq : approxCountScaleSecond N t ε = C := by
    unfold approxCountScaleSecond
    rw [hC]
  rw [hCeq, hS]
  exact hfinal

theorem walkGoal_scale_le_sqrt_two_scale_prime {N t : ℕ} (hN : 0 < N) (ht1 : 1 ≤ t) (htN : t ≤ N)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    approxCountSourceScale N t ε ≤ Real.sqrt 2 * approxCountSourceScalePrime N t ε := by
  have h1 := walkGoal_scale_le_sqrt_two_first hN ht1 htN ε hε hε1
  have h2 := walkGoal_scale_le_sqrt_two_second hN ht1 htN ε
  have hmin : min (Real.sqrt 2 * approxCountScaleFirst N t ε)
      (Real.sqrt 2 * approxCountScaleSecond N t ε)
      = Real.sqrt 2 * approxCountSourceScalePrime N t ε := by
    unfold approxCountSourceScalePrime
    by_cases hAC : approxCountScaleFirst N t ε ≤ approxCountScaleSecond N t ε
    · rw [min_eq_left hAC, min_eq_left (mul_le_mul_of_nonneg_left hAC (Real.sqrt_nonneg _))]
    · rw [min_eq_right (le_of_not_ge hAC),
        min_eq_right (mul_le_mul_of_nonneg_left (le_of_not_ge hAC) (Real.sqrt_nonneg _))]
  rw [← hmin]
  exact le_min h1 h2

theorem walkGoal_scale_prime_le_scale {N t : ℕ} (hN : 0 < N) (ht1 : 1 ≤ t) (htN : t ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    approxCountSourceScalePrime N t ε ≤ 2 * approxCountSourceScale N t ε := by
  by_cases het : 1 ≤ ε * (t:ℝ)
  · have h1 := walkGoal_first_le_two_scale hN ht1 htN ε hε het
    have hmin : approxCountSourceScalePrime N t ε ≤ approxCountScaleFirst N t ε := by
      unfold approxCountSourceScalePrime
      exact min_le_left _ _
    linarith
  · have het' : ε * (t:ℝ) < 1 := lt_of_not_ge het
    have h2 := walkGoal_second_le_two_scale_small hN ht1 htN ε hε het'
    have hmin : approxCountSourceScalePrime N t ε ≤ approxCountScaleSecond N t ε := by
      unfold approxCountSourceScalePrime
      exact min_le_right _ _
    linarith

theorem walkGoal_scale_prime_theta {N t : ℕ} (hN : 0 < N) (ht1 : 1 ≤ t) (htN : t ≤ N)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    approxCountSourceScale N t ε / Real.sqrt 2 ≤ approxCountSourceScalePrime N t ε ∧
      approxCountSourceScalePrime N t ε ≤ 2 * approxCountSourceScale N t ε := by
  refine ⟨?_, walkGoal_scale_prime_le_scale hN ht1 htN ε hε⟩
  have h := walkGoal_scale_le_sqrt_two_scale_prime hN ht1 htN ε hε hε1
  have hsqrt : 0 < Real.sqrt 2 := by
    have : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  rw [div_le_iff₀ hsqrt]
  linarith [h]

private theorem walkGoal_nat_eq_of_abs_lt_one {a b : ℕ} (h : |(a:ℝ) - (b:ℝ)| < 1) : a = b := by
  by_cases hab : a ≤ b
  · have h1 : (b:ℝ) - (a:ℝ) = ((b - a : ℕ) : ℝ) := by rw [Nat.cast_sub hab]
    have h2 : (0:ℝ) ≤ (b:ℝ) - (a:ℝ) := by rw [h1]; positivity
    have h3 : |(a:ℝ) - (b:ℝ)| = (b:ℝ) - (a:ℝ) := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have h4 : (b - a : ℕ) < 1 := by
      have : ((b - a : ℕ) : ℝ) < 1 := by linarith
      exact_mod_cast this
    omega
  · have h1 : (a:ℝ) - (b:ℝ) = ((a - b : ℕ) : ℝ) := by rw [Nat.cast_sub (Nat.le_of_not_ge hab)]
    have h2 : (0:ℝ) ≤ (a:ℝ) - (b:ℝ) := by rw [h1]; positivity
    have h3 : |(a:ℝ) - (b:ℝ)| = (a:ℝ) - (b:ℝ) := by rw [abs_of_nonneg h2]
    have h4 : (a - b : ℕ) < 1 := by
      have : ((a - b : ℕ) : ℝ) < 1 := by linarith
      exact_mod_cast this
    omega

theorem walkGoal_rounding_composition {t tc tr : ℕ} {ε : ℝ}
    (h1 : |(tc : ℝ) - (t : ℝ)| ≤ ε * (t : ℝ) / 3)
    (h2 : |(tr : ℝ) - (tc : ℝ)| ≤ 2 / 3) :
    |(tr : ℝ) - (t : ℝ)| ≤ ε * (t : ℝ) / 3 + 2 / 3 := by
  have htri : |(tr : ℝ) - (t : ℝ)| ≤ |(tr : ℝ) - (tc : ℝ)| + |(tc : ℝ) - (t : ℝ)| :=
    abs_sub_le _ _ _
  linarith

theorem walkGoal_relative_error_le {t tc tr : ℕ} {ε : ℝ} (het : 1 ≤ ε * (t:ℝ))
    (h1 : |(tc : ℝ) - (t : ℝ)| ≤ ε * (t : ℝ) / 3)
    (h2 : |(tr : ℝ) - (tc : ℝ)| ≤ 2 / 3) :
    |(tr : ℝ) - (t : ℝ)| ≤ ε * (t : ℝ) := by
  have h3 := walkGoal_rounding_composition h1 h2
  have h4 : (2:ℝ)/3 ≤ (2:ℝ)/3 * (ε * (t:ℝ)) := by
    have := mul_le_mul_of_nonneg_left het (by norm_num : (0:ℝ) ≤ 2 / 3)
    linarith
  linarith

theorem walkGoal_relative_error_on_scale_event {N t : ℕ} (hN : 0 < N) (htN : t ≤ N) (ht1 : 1 ≤ t)
    (ε : ℝ) (hε : 0 < ε) (het : 1 ≤ ε * (t:ℝ)) (M : ℕ) (hM : 0 < M)
    (hscale : (M:ℝ) ≥ approxCountScaleFirst N t ε ∨
      (M:ℝ) ≥ approxCountScaleSecond N t ε)
    (tc tr : ℕ)
    (hwin : |(tc:ℝ) - (t:ℝ)| ≤ 2 * Real.pi * Real.sqrt ((t:ℝ) * ((N:ℝ) - (t:ℝ))) / (approxCountFinalM M : ℝ) +
        Real.pi ^ 2 * (N:ℝ) / (approxCountFinalM M : ℝ) ^ 2)
    (hround : |(tr:ℝ) - (tc:ℝ)| ≤ 2 / 3) :
    |(tr:ℝ) - (t:ℝ)| ≤ ε * (t:ℝ) := by
  have h1 := walkGoal_window_le hN M hM ε hε het htN ht1 hscale
  exact walkGoal_relative_error_le het (by linarith [h1, hwin]) hround

theorem walkGoal_relative_error_exact {t tc tr : ℕ} {ε : ℝ} (het : ε * (t:ℝ) < 1)
    (h1 : |(tc : ℝ) - (t : ℝ)| ≤ ε * (t : ℝ) / 3)
    (h2 : |(tr : ℝ) - (tc : ℝ)| ≤ 2 / 3) : tr = t := by
  have h3 := walkGoal_rounding_composition h1 h2
  have hlt : |(tr : ℝ) - (t : ℝ)| < 1 := by linarith
  exact walkGoal_nat_eq_of_abs_lt_one hlt

theorem walkGoal_small_epsilon_exact_counting {N t tc tr : ℕ} {ε : ℝ} (htN : t ≤ N)
    (hε : 0 < ε) (hsmall : ε * (N:ℝ) ≤ 1 / 3)
    (h1 : |(tc : ℝ) - (t : ℝ)| ≤ ε * (t : ℝ) / 3)
    (h2 : |(tr : ℝ) - (tc : ℝ)| ≤ 2 / 3) : tr = t := by
  have het : ε * (t:ℝ) < 1 := by
    have h1' : ε * (t:ℝ) ≤ ε * (N:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast htN) hε.le
    linarith
  exact walkGoal_relative_error_exact het h1 h2

theorem walkGoal_scale_event_prob_above_floor :
    approxCountScaleEventProb > approxCountScaleEventFloor := by
  show approxCountScaleEventFloor < approxCountScaleEventProb
  norm_num [approxCountScaleEventProb, approxCountScaleEventFloor]

theorem walkGoal_final_success_prob :
    approxCountScaleEventFloor * approxCountFinalRecordProb > 2 / 3 := by
  show (2 : ℝ) / 3 < approxCountScaleEventFloor * approxCountFinalRecordProb
  have hpi : Real.pi ^ 2 < 51 / 5 := by
    have h1 : Real.pi < 63 / 20 := by
      have h2 := Real.pi_lt_d2
      norm_num at h2
      linarith
    have hpi0 : 0 ≤ Real.pi := Real.pi_nonneg
    nlinarith
  have hpos : (0:ℝ) < Real.pi ^ 2 := by positivity
  rw [show approxCountScaleEventFloor * approxCountFinalRecordProb
      = (34 / 5 : ℝ) / Real.pi ^ 2 by
        unfold approxCountScaleEventFloor approxCountFinalRecordProb
        ring]
  rw [lt_div_iff₀ hpos]
  nlinarith

theorem clause12_growth_marginal_uniform (m r : ℕ) (hm : 0 < m) (j : Fin m) :
    growthMarginal m r j = (1 - growthRejectProb m ^ r) * (1 / (m : ℝ)) := by
  have h := thresholdRunLaw_accepted_matches_frozen_initial m hm r j
  have hunif := threshold_matches_frozen_initial m hm j
  simp only [growthMarginal, growthSamplerLaw]
  rw [h, hunif]
  rfl

theorem clause12_growth_marginal_total (m r : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, growthMarginal m r j) = 1 - growthRejectProb m ^ r := by
  have h := thresholdRunLaw_accepted_total m hm r
  simp only [growthMarginal, growthSamplerLaw]
  rw [h]
  rfl

theorem clause12_growth_timeout_mass (m r : ℕ) (hm : 0 < m) :
    ((growthSamplerLaw m r) (ThresholdOutcome.failed : ThresholdOutcome m r)).toReal
      = growthRejectProb m ^ r := by
  have h := thresholdRunLaw_failed_mass m hm r
  simp only [growthSamplerLaw]
  rw [h]
  rfl

private theorem clause12_nat_le_real_sqrt (n : ℕ) : (n.sqrt : ℝ) ≤ Real.sqrt n := by
  have h1 : (n.sqrt : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have h2 : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt (by positivity)
  nlinarith [Real.sqrt_nonneg n]

private theorem clause12_real_sqrt_lt_sqrt_add_one (n : ℕ) : Real.sqrt n < n.sqrt + 1 := by
  have hnot : ¬ ((n.sqrt + 1) * (n.sqrt + 1) ≤ n) := by
    intro h
    have hle := (Nat.le_sqrt : (n.sqrt + 1) ≤ n.sqrt ↔
      (n.sqrt + 1) * (n.sqrt + 1) ≤ n)
    omega
  have h3 : (n.sqrt + 1) ^ 2 > n := by
    have h2 : (n.sqrt + 1) * (n.sqrt + 1) = (n.sqrt + 1) ^ 2 := by ring
    omega
  rw [Real.sqrt_lt' (by positivity)]
  have h3' : ((n.sqrt + 1 : ℕ) : ℝ) ^ 2 > (n : ℝ) := by exact_mod_cast h3
  simpa [Nat.cast_add] using! h3'

theorem clause12_thresholdWords_lt_two_mul (m : ℕ) (hm : 0 < m) :
    thresholdWords m < 2 * m := by
  have hlog2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hbl : 0 ≤ binaryLog m := div_nonneg hlogm hlog2.le
  have hceil : binaryLog m ≤ (thresholdWidth m : ℝ) := by
    rw [thresholdWidth_eq]
    exact_mod_cast Nat.le_ceil _
  have hceil1 : (thresholdWidth m : ℝ) < binaryLog m + 1 := by
    rw [thresholdWidth_eq]
    exact Nat.ceil_lt_add_one hbl
  have hprod : (thresholdWidth m : ℝ) * Real.log 2 < (binaryLog m + 1) * Real.log 2 :=
    mul_lt_mul_of_pos_right hceil1 hlog2
  have hexp : Real.exp ((thresholdWidth m : ℝ) * Real.log 2) <
      Real.exp ((binaryLog m + 1) * Real.log 2) := Real.exp_lt_exp.mpr hprod
  have hid : Real.exp (binaryLog m * Real.log 2) = m := by
    rw [show binaryLog m * Real.log 2 = Real.log m by unfold binaryLog; field_simp]
    exact Real.exp_log (by exact_mod_cast hm)
  have hid3 : Real.exp ((binaryLog m + 1) * Real.log 2) = 2 * m := by
    rw [show (binaryLog m + 1) * Real.log 2 = binaryLog m * Real.log 2 + Real.log 2 by ring,
      Real.exp_add, hid, Real.exp_log (by norm_num)]
    ring
  have hid2 : Real.exp ((thresholdWidth m : ℝ) * Real.log 2) = (thresholdWords m : ℝ) := by
    rw [thresholdWords, Nat.cast_pow]
    have htwo : ∀ (k : ℕ), Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.cast_succ, show (↑k + 1) * Real.log 2 = (↑k : ℝ) * Real.log 2 + Real.log 2 by
          ring, Real.exp_add, ih, Real.exp_log (by norm_num)]
        ring
    exact htwo (thresholdWidth m)
  have hfinal : (thresholdWords m : ℝ) < 2 * (m : ℝ) := by
    calc (thresholdWords m : ℝ) = Real.exp ((thresholdWidth m : ℝ) * Real.log 2) := hid2.symm
      _ < Real.exp ((binaryLog m + 1) * Real.log 2) := hexp
      _ = 2 * m := hid3
  exact_mod_cast hfinal

theorem clause12_growth_reject_prob_lt_half (m : ℕ) (hm : 0 < m) :
    growthRejectProb m < 1 / 2 := by
  have htw := clause12_thresholdWords_lt_two_mul m hm
  have hNM : m ≤ thresholdWords m := thresholdWords_ge m hm
  have hcast : ((thresholdWords m - m : ℕ) : ℝ) = (thresholdWords m : ℝ) - (m : ℝ) :=
    Nat.cast_sub hNM
  have hpos : (0 : ℝ) < thresholdWords m := Nat.cast_pos.mpr (thresholdWords_pos m)
  rw [growthRejectProb, thresholdRejectProb, hcast]
  rw [div_lt_iff₀ hpos]
  have h1 : (thresholdWords m : ℝ) < 2 * (m : ℝ) := by exact_mod_cast htw
  have h2 : 0 ≤ (thresholdWords m : ℝ) := hpos.le
  linarith

theorem clause12_growth_tail_bound (m r : ℕ) (hm : 0 < m) :
    growthRejectProb m ^ r ≤ (1 / 2 : ℝ) ^ r := by
  have hq := clause12_growth_reject_prob_lt_half m hm
  have hq0 : 0 ≤ growthRejectProb m := by
    rw [growthRejectProb, thresholdRejectProb]
    have hNM : m ≤ thresholdWords m := thresholdWords_ge m hm
    have hcast : ((thresholdWords m - m : ℕ) : ℝ) = (thresholdWords m : ℝ) - (m : ℝ) :=
      Nat.cast_sub hNM
    rw [hcast]
    have hsub : 0 ≤ thresholdWords m - m := by omega
    apply div_nonneg
    · exact_mod_cast hsub
    · exact (Nat.cast_pos.mpr (thresholdWords_pos m)).le
  have hle : growthRejectProb m ≤ (1 / 2 : ℝ) := le_of_lt hq
  exact pow_le_pow_left₀ hq0 hle r

theorem clause12_growth_timeout_mass_le (m r : ℕ) (hm : 0 < m) :
    ((growthSamplerLaw m r) (ThresholdOutcome.failed : ThresholdOutcome m r)).toReal
      ≤ (1 / 2 : ℝ) ^ r := by
  rw [clause12_growth_timeout_mass m r hm]
  exact clause12_growth_tail_bound m r hm

theorem clause12_growth_draws_le (m r : ℕ) (o : ThresholdOutcome m r) :
    growthDraws o ≤ r := by
  cases o with
  | accepted i n =>
    simp [growthDraws]
  | failed => simp [growthDraws]

theorem clause12_growth_bits_accepted (m r : ℕ) (i : Fin m) (n : Fin r) :
    growthBits (.accepted i n : ThresholdOutcome m r) = growthWidth m * (n.val + 1) := by
  simp [growthBits, growthDraws]

theorem clause12_growth_bits_failed (m r : ℕ) :
    growthBits (.failed : ThresholdOutcome m r) = growthWidth m * r := by
  simp [growthBits, growthDraws]

theorem clause12_growth_bits_le (m r : ℕ) (o : ThresholdOutcome m r) :
    growthBits o ≤ growthWidth m * r := by
  cases o with
  | accepted i n =>
    have hn : n.val + 1 ≤ r := by omega
    simp only [growthBits, growthDraws]
    exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (growthWidth m))
  | failed => simp only [growthBits, growthDraws]; exact le_rfl

theorem clause12_growth_space_eq_width (m : ℕ) : growthSpace m = growthWidth m := rfl

theorem clause12_growth_width_one (m : ℕ) (hm : m = 1) : growthWidth m = 0 := by
  subst hm
  rw [growthWidth, thresholdWidth_eq]
  have h : binaryLog ((1 : ℕ) : ℝ) = 0 := by unfold binaryLog; simp
  rw [h]
  simp

theorem clause12_native_attempt_success {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m r : ℕ) (hm : 0 < m) :
    growthAttemptSuccess A m r = (1 - growthRejectProb m ^ r) * CheckedSuccess A m := by
  have hmar (j : ℕ) (hj : j < m) :
      growthMarginalAt m r j = (1 - growthRejectProb m ^ r) * (1 / (m : ℝ)) := by
    simp only [growthMarginalAt, dif_pos hj]
    exact clause12_growth_marginal_uniform m r hm ⟨j, hj⟩
  unfold growthAttemptSuccess
  calc
    (∑ j ∈ Finset.range m, growthMarginalAt m r j * (∑ i, CheckedOutputMass A j i))
        = ∑ j ∈ Finset.range m, ((1 - growthRejectProb m ^ r) * (1 / (m : ℝ)))
            * (∑ i, CheckedOutputMass A j i) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hmar j (Finset.mem_range.mp hj)]
    _ = ((1 - growthRejectProb m ^ r) * (1 / (m : ℝ))) *
            (∑ j ∈ Finset.range m, ∑ i, CheckedOutputMass A j i) := by
              rw [← Finset.mul_sum]
    _ = (1 - growthRejectProb m ^ r) * CheckedSuccess A m := by
              unfold CheckedSuccess
              rw [div_eq_mul_inv]
              ring

theorem clause12_native_attempt_failure {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m r : ℕ) (hm : 0 < m) :
    growthAttemptFailure A m r = (1 - growthRejectProb m ^ r) * CheckedFailure A m := by
  have hmar (j : ℕ) (hj : j < m) :
      growthMarginalAt m r j = (1 - growthRejectProb m ^ r) * (1 / (m : ℝ)) := by
    simp only [growthMarginalAt, dif_pos hj]
    exact clause12_growth_marginal_uniform m r hm ⟨j, hj⟩
  unfold growthAttemptFailure
  calc
    (∑ j ∈ Finset.range m, growthMarginalAt m r j * CheckedRejectMass A j)
        = ∑ j ∈ Finset.range m, ((1 - growthRejectProb m ^ r) * (1 / (m : ℝ)))
            * CheckedRejectMass A j := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hmar j (Finset.mem_range.mp hj)]
    _ = ((1 - growthRejectProb m ^ r) * (1 / (m : ℝ))) *
            (∑ j ∈ Finset.range m, CheckedRejectMass A j) := by
              rw [← Finset.mul_sum]
    _ = (1 - growthRejectProb m ^ r) * CheckedFailure A m := by
              unfold CheckedFailure
              rw [div_eq_mul_inv]
              ring

theorem clause12_native_attempt_queries (I : Type*) [Fintype I] [DecidableEq I]
    (m r : ℕ) (hm : 0 < m) :
    growthAttemptQueries I m r = (1 - growthRejectProb m ^ r) * CheckedMeanQueries I m := by
  have hmar (j : ℕ) (hj : j < m) :
      growthMarginalAt m r j = (1 - growthRejectProb m ^ r) * (1 / (m : ℝ)) := by
    simp only [growthMarginalAt, dif_pos hj]
    exact clause12_growth_marginal_uniform m r hm ⟨j, hj⟩
  unfold growthAttemptQueries
  calc
    (∑ j ∈ Finset.range m, growthMarginalAt m r j * growthCheckedQueries I j)
        = ∑ j ∈ Finset.range m, ((1 - growthRejectProb m ^ r) * (1 / (m : ℝ)))
            * growthCheckedQueries I j := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hmar j (Finset.mem_range.mp hj)]
    _ = ((1 - growthRejectProb m ^ r) * (1 / (m : ℝ))) *
            (∑ j ∈ Finset.range m, growthCheckedQueries I j) := by
              rw [← Finset.mul_sum]
    _ = (1 - growthRejectProb m ^ r) * CheckedMeanQueries I m := by
              unfold CheckedMeanQueries growthCheckedQueries
              rw [div_eq_mul_inv]
              ring

theorem clause12_native_attempt_success_error {I : Type*} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (A : Finset I) (m r : ℕ) (hm : 0 < m) :
    |growthAttemptSuccess A m r - CheckedSuccess A m| ≤ growthRejectProb m ^ r := by
  have h := clause12_native_attempt_success A m r hm
  have h2 := (search_checked_random_attempt hI A m hm)
  have hlo : 0 ≤ CheckedSuccess A m := h2.2.2.1.1
  have hhi : CheckedSuccess A m ≤ 1 := by linarith [h2.2.1, h2.2.2.2]
  rw [h]
  have hq0 : 0 ≤ growthRejectProb m ^ r := by
    have hq : 0 ≤ growthRejectProb m := by
      rw [growthRejectProb, thresholdRejectProb]
      have hNM : m ≤ thresholdWords m := thresholdWords_ge m hm
      have hcast : ((thresholdWords m - m : ℕ) : ℝ) = (thresholdWords m : ℝ) - (m : ℝ) :=
        Nat.cast_sub hNM
      rw [hcast]
      apply div_nonneg
      · exact_mod_cast (by omega)
      · exact (Nat.cast_pos.mpr (thresholdWords_pos m)).le
    exact pow_nonneg hq r
  have hdiff : (1 - growthRejectProb m ^ r) * CheckedSuccess A m - CheckedSuccess A m
      = -(growthRejectProb m ^ r * CheckedSuccess A m) := by ring
  rw [hdiff, abs_neg]
  rw [abs_of_nonneg (mul_nonneg hq0 hlo)]
  calc growthRejectProb m ^ r * CheckedSuccess A m
      ≤ growthRejectProb m ^ r * 1 := mul_le_mul_of_nonneg_left hhi hq0
    _ = growthRejectProb m ^ r := mul_one _

theorem clause12_native_attempt_queries_error (I : Type*) [Fintype I] [DecidableEq I]
    (m r : ℕ) (hm : 0 < m) :
    |growthAttemptQueries I m r - CheckedMeanQueries I m|
      ≤ growthRejectProb m ^ r * CheckedMeanQueries I m := by
  have h := clause12_native_attempt_queries I m r hm
  have hlo : 0 ≤ CheckedMeanQueries I m := by
    unfold CheckedMeanQueries
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro j hj
      exact Nat.cast_nonneg _
    · exact (Nat.cast_pos.mpr (by omega)).le
  have hq0 : 0 ≤ growthRejectProb m ^ r := by
    have hq : 0 ≤ growthRejectProb m := by
      rw [growthRejectProb, thresholdRejectProb]
      have hNM : m ≤ thresholdWords m := thresholdWords_ge m hm
      have hcast : ((thresholdWords m - m : ℕ) : ℝ) = (thresholdWords m : ℝ) - (m : ℝ) :=
        Nat.cast_sub hNM
      rw [hcast]
      apply div_nonneg
      · exact_mod_cast (by omega)
      · exact (Nat.cast_pos.mpr (thresholdWords_pos m)).le
    exact pow_nonneg hq r
  have hdiff : (1 - growthRejectProb m ^ r) * CheckedMeanQueries I m - CheckedMeanQueries I m
      = -(growthRejectProb m ^ r * CheckedMeanQueries I m) := by ring
  rw [h, hdiff, abs_neg]
  rw [abs_of_nonneg (mul_nonneg hq0 hlo)]

theorem clause12_native_window_sandwich (N k : ℕ) (hN : 0 < N) :
    growthRealWindow N k - 1 ≤ (nativeGrowthWindow N k : ℝ) ∧
      (nativeGrowthWindow N k : ℝ) ≤ (ExponentialSizes N k : ℝ) := by
  have hclosed := (search_exponential_schedule N hN).1 k
  have hS : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := clause12_nat_le_real_sqrt N
  have hS1 : Real.sqrt N < (Nat.sqrt N : ℝ) + 1 := clause12_real_sqrt_lt_sqrt_add_one N
  have hmin : min ((6 / 5 : ℝ) ^ k) (Real.sqrt N) - 1
      ≤ min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) := by
    by_cases hcase : (6 / 5 : ℝ) ^ k ≤ (Nat.sqrt N : ℝ)
    · have h1 : min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) = (6 / 5 : ℝ) ^ k := min_eq_left hcase
      have h2 : min ((6 / 5 : ℝ) ^ k) (Real.sqrt N) = (6 / 5 : ℝ) ^ k :=
        min_eq_left (le_trans hcase hS)
      rw [h2, h1]
      linarith
    · have hlt : (Nat.sqrt N : ℝ) < (6 / 5 : ℝ) ^ k := lt_of_not_ge hcase
      have h1 : min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) = (Nat.sqrt N : ℝ) :=
        min_eq_right (le_of_lt hlt)
      have h2 : min ((6 / 5 : ℝ) ^ k) (Real.sqrt N) ≤ Real.sqrt N := min_le_right _ _
      rw [h1]
      linarith
  have hceilu : (nativeGrowthWindow N k : ℝ) ≥ min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) :=
    Nat.le_ceil _
  have hminle : min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ)
      ≤ min ((6 / 5 : ℝ) ^ k) (Real.sqrt N) := min_le_min (le_refl _) hS
  have hceille : nativeGrowthWindow N k
      ≤ Nat.ceil (min ((6 / 5 : ℝ) ^ k) (Real.sqrt N)) := by
    rw [nativeGrowthWindow]
    exact Nat.ceil_le_ceil hminle
  have hceille' : nativeGrowthWindow N k ≤ ExponentialSizes N k := by
    rw [ExponentialSizes, hclosed]
    exact hceille
  refine ⟨?_, ?_⟩
  · rw [growthRealWindow]
    linarith
  · exact_mod_cast hceille'

theorem clause12_native_window_gap (N k : ℕ) (hN : 0 < N) :
    ExponentialSizes N k - 1 ≤ nativeGrowthWindow N k ∧
      nativeGrowthWindow N k ≤ ExponentialSizes N k := by
  have hclosed := (search_exponential_schedule N hN).1 k
  have hmpos : 0 < ExponentialSizes N k := (search_exponential_schedule N hN).2.1 k
  have hceilu : (nativeGrowthWindow N k : ℝ) ≥ min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) :=
    Nat.le_ceil _
  have hwidth0 : 0 ≤ ExponentialWidth N k := by
    rw [hclosed]
    have h1 : (0 : ℝ) ≤ (6 / 5 : ℝ) ^ k := by positivity
    have h2 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
    exact le_min h1 h2
  have hceilv : (ExponentialSizes N k : ℝ) < (ExponentialWidth N k : ℝ) + 1 := by
    rw [ExponentialSizes]
    exact Nat.ceil_lt_add_one hwidth0
  have hS : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := clause12_nat_le_real_sqrt N
  have hS1 : Real.sqrt N < (Nat.sqrt N : ℝ) + 1 := clause12_real_sqrt_lt_sqrt_add_one N
  have hmin : min ((6 / 5 : ℝ) ^ k) (Real.sqrt N) - 1
      ≤ min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) := by
    by_cases hcase : (6 / 5 : ℝ) ^ k ≤ (Nat.sqrt N : ℝ)
    · have h1 : min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) = (6 / 5 : ℝ) ^ k := min_eq_left hcase
      have h2 : min ((6 / 5 : ℝ) ^ k) (Real.sqrt N) = (6 / 5 : ℝ) ^ k :=
        min_eq_left (le_trans hcase hS)
      rw [h2, h1]
      linarith
    · have hlt : (Nat.sqrt N : ℝ) < (6 / 5 : ℝ) ^ k := lt_of_not_ge hcase
      have h1 : min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) = (Nat.sqrt N : ℝ) :=
        min_eq_right (le_of_lt hlt)
      have h2 : min ((6 / 5 : ℝ) ^ k) (Real.sqrt N) ≤ Real.sqrt N := min_le_right _ _
      rw [h1]
      linarith
  have hlow : (nativeGrowthWindow N k : ℝ) > (ExponentialSizes N k : ℝ) - 2 := by
    rw [hclosed] at hceilv
    have hmin' : min ((6 / 5 : ℝ) ^ k) (Real.sqrt N) - 1
        ≤ min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) := hmin
    linarith
  refine ⟨?_, ?_⟩
  · by_cases hone : ExponentialSizes N k = 1
    · rw [hone]
      exact Nat.zero_le _
    · have hone' : 1 < ExponentialSizes N k :=
        lt_of_le_of_ne (Nat.succ_le_of_lt hmpos) (Ne.symm hone)
      have htwo : 2 ≤ ExponentialSizes N k := Nat.succ_le_of_lt hone'
      have hcast : ((ExponentialSizes N k - 2 : ℕ) : ℝ) = (ExponentialSizes N k : ℝ) - 2 :=
        Nat.cast_sub htwo
      rw [← hcast] at hlow
      have hgt : (nativeGrowthWindow N k : ℕ) > ExponentialSizes N k - 2 := by exact_mod_cast hlow
      omega
  · have hminle : min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ)
        ≤ min ((6 / 5 : ℝ) ^ k) (Real.sqrt N) := min_le_min (le_refl _) hS
    have hceille : nativeGrowthWindow N k
        ≤ Nat.ceil (min ((6 / 5 : ℝ) ^ k) (Real.sqrt N)) := by
      rw [nativeGrowthWindow]
      exact Nat.ceil_le_ceil hminle
    have hceille' : nativeGrowthWindow N k ≤ ExponentialSizes N k := by
      rw [ExponentialSizes, hclosed]
      exact hceille
    omega

private theorem clause12_avg_window_gap {g : ℕ → ℝ} (hg0 : ∀ j, 0 ≤ g j) (hg1 : ∀ j, g j ≤ 1)
    {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m') (hgap : m' + 1 = m) :
    |(∑ j ∈ Finset.range m', g j) / (m' : ℝ) - (∑ j ∈ Finset.range m, g j) / (m : ℝ)|
      ≤ 1 / (m : ℝ) := by
  have hm1 : m = m' + 1 := hgap.symm
  have hsplit : (∑ j ∈ Finset.range m, g j) = (∑ j ∈ Finset.range m', g j) + g m' := by
    rw [hm1, Finset.sum_range_succ]
  have hS0 : 0 ≤ ∑ j ∈ Finset.range m', g j :=
    Finset.sum_nonneg fun j hj => hg0 j
  have hS1 : (∑ j ∈ Finset.range m', g j) ≤ (m' : ℝ) := by
    calc (∑ j ∈ Finset.range m', g j) ≤ ∑ _ ∈ Finset.range m', (1 : ℝ) :=
          Finset.sum_le_sum fun j hj => hg1 j
      _ = (m' : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range, mul_one]
  have hpos : (0 : ℝ) < (m : ℝ) * (m' : ℝ) :=
    mul_pos (by exact_mod_cast hm.pos) (by exact_mod_cast hm'.pos)
  have hcomb : (∑ j ∈ Finset.range m', g j) / (m' : ℝ)
      - (∑ j ∈ Finset.range m, g j) / (m : ℝ)
      = ((∑ j ∈ Finset.range m', g j) - g m' * (m' : ℝ)) / ((m : ℝ) * (m' : ℝ)) := by
    rw [hsplit]
    have hmcast : (m : ℝ) = (m' : ℝ) + 1 := by exact_mod_cast hm1
    rw [hmcast]
    field_simp
    ring
  rw [hcomb, abs_le]
  have hmul : (1 / (m : ℝ)) * ((m : ℝ) * (m' : ℝ)) = (m' : ℝ) := by field_simp
  have hmul' : (-(1 / (m : ℝ))) * ((m : ℝ) * (m' : ℝ)) = -(m' : ℝ) := by
    rw [neg_mul, hmul]
  have hgm : g m' * (m' : ℝ) ≤ (m' : ℝ) := by
    calc g m' * (m' : ℝ) ≤ 1 * (m' : ℝ) :=
          mul_le_mul_of_nonneg_right (hg1 m') (Nat.cast_nonneg m')
      _ = (m' : ℝ) := one_mul _
  have hgm0 : 0 ≤ g m' * (m' : ℝ) := mul_nonneg (hg0 m') (Nat.cast_nonneg m')
  constructor
  · rw [le_div_iff₀ hpos]
    rw [hmul']
    linarith
  · rw [div_le_iff₀ hpos]
    rw [hmul]
    linarith

theorem clause12_native_attempt_total_error {I : Type*} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (A : Finset I) (N k r : ℕ) (hN : 0 < N) :
    |growthAttemptSuccess A (nativeGrowthWindow N k) r
        - CheckedSuccess A (ExponentialSizes N k)|
      ≤ growthRejectProb (nativeGrowthWindow N k) ^ r
        + 1 / (ExponentialSizes N k : ℝ) := by
  have hout (j : ℕ) : 0 ≤ ∑ i, CheckedOutputMass A j i
      ∧ (∑ i, CheckedOutputMass A j i) ≤ 1 := by
    have h := (search_checked_attempt hI A j)
    constructor
    · exact Finset.sum_nonneg fun i hi => h.2.2.2.2.1 i
    · linarith [h.2.2.2.1, h.2.2.2.2]
  have hmpos : 0 < ExponentialSizes N k := (search_exponential_schedule N hN).2.1 k
  have hm'pos : 0 < nativeGrowthWindow N k := by
    have hlt : (0 : ℝ) < min ((6 / 5 : ℝ) ^ k) (Nat.sqrt N : ℝ) := by
      have h1 : (0 : ℝ) < (6 / 5 : ℝ) ^ k := by positivity
      have h2 : (0 : ℝ) < (Nat.sqrt N : ℝ) := by
        exact_mod_cast (Nat.sqrt_pos.2 (by omega))
      exact lt_min h1 h2
    rw [nativeGrowthWindow]
    exact Nat.ceil_pos.mpr hlt
  have hsucc := clause12_native_attempt_success A (nativeGrowthWindow N k) r hm'pos
  have hgap := clause12_native_window_gap N k hN
  have hround : |CheckedSuccess A (nativeGrowthWindow N k)
        - CheckedSuccess A (ExponentialSizes N k)| ≤ 1 / (ExponentialSizes N k : ℝ) := by
    by_cases heq : nativeGrowthWindow N k = ExponentialSizes N k
    · rw [heq]
      have hz : CheckedSuccess A (ExponentialSizes N k)
          - CheckedSuccess A (ExponentialSizes N k) = 0 := by ring
      rw [hz, abs_zero]
      positivity
    · have hne : nativeGrowthWindow N k + 1 = ExponentialSizes N k := by
        omega
      rw [CheckedSuccess, CheckedSuccess]
      exact clause12_avg_window_gap (fun j => (hout j).1) (fun j => (hout j).2)
        hmpos hm'pos hne
  have hC'lo : 0 ≤ CheckedSuccess A (nativeGrowthWindow N k) := by
    unfold CheckedSuccess
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro j hj
      exact (hout j).1
    · exact (Nat.cast_pos.mpr hm'pos).le
  have hC'hi : CheckedSuccess A (nativeGrowthWindow N k) ≤ 1 := by
    have h2 := (search_checked_random_attempt hI A (nativeGrowthWindow N k) hm'pos)
    linarith [h2.2.1, h2.2.2.2]
  have hq0 : 0 ≤ growthRejectProb (nativeGrowthWindow N k) ^ r := by
    have hq : 0 ≤ growthRejectProb (nativeGrowthWindow N k) := by
      rw [growthRejectProb, thresholdRejectProb]
      have hNM : nativeGrowthWindow N k ≤ thresholdWords (nativeGrowthWindow N k) :=
        thresholdWords_ge (nativeGrowthWindow N k) hm'pos
      have hcast : ((thresholdWords (nativeGrowthWindow N k)
          - nativeGrowthWindow N k : ℕ) : ℝ)
          = (thresholdWords (nativeGrowthWindow N k) : ℝ)
            - (nativeGrowthWindow N k : ℝ) := Nat.cast_sub hNM
      rw [hcast]
      apply div_nonneg
      · exact_mod_cast (by omega)
      · exact (Nat.cast_pos.mpr (thresholdWords_pos (nativeGrowthWindow N k))).le
    exact pow_nonneg hq r
  rw [hsucc]
  have hsplit : (1 - growthRejectProb (nativeGrowthWindow N k) ^ r)
        * CheckedSuccess A (nativeGrowthWindow N k)
        - CheckedSuccess A (ExponentialSizes N k)
      = -(growthRejectProb (nativeGrowthWindow N k) ^ r
          * CheckedSuccess A (nativeGrowthWindow N k))
        + (CheckedSuccess A (nativeGrowthWindow N k)
          - CheckedSuccess A (ExponentialSizes N k)) := by ring
  rw [hsplit]
  calc |-(growthRejectProb (nativeGrowthWindow N k) ^ r
          * CheckedSuccess A (nativeGrowthWindow N k))
        + (CheckedSuccess A (nativeGrowthWindow N k)
          - CheckedSuccess A (ExponentialSizes N k))|
      ≤ |-(growthRejectProb (nativeGrowthWindow N k) ^ r
          * CheckedSuccess A (nativeGrowthWindow N k))|
        + |CheckedSuccess A (nativeGrowthWindow N k)
          - CheckedSuccess A (ExponentialSizes N k)| := by
          exact abs_add_le _ _
    _ = growthRejectProb (nativeGrowthWindow N k) ^ r
        * CheckedSuccess A (nativeGrowthWindow N k)
        + |CheckedSuccess A (nativeGrowthWindow N k)
          - CheckedSuccess A (ExponentialSizes N k)| := by
          rw [abs_neg, abs_of_nonneg (mul_nonneg hq0 hC'lo)]
    _ ≤ growthRejectProb (nativeGrowthWindow N k) ^ r
        + |CheckedSuccess A (nativeGrowthWindow N k)
          - CheckedSuccess A (ExponentialSizes N k)| := by
          gcongr
          calc growthRejectProb (nativeGrowthWindow N k) ^ r
              * CheckedSuccess A (nativeGrowthWindow N k)
              ≤ growthRejectProb (nativeGrowthWindow N k) ^ r * 1 :=
                mul_le_mul_of_nonneg_left hC'hi hq0
            _ = growthRejectProb (nativeGrowthWindow N k) ^ r := mul_one _
    _ ≤ growthRejectProb (nativeGrowthWindow N k) ^ r
        + 1 / (ExponentialSizes N k : ℝ) := by
          linarith [hround]

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16
open Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification
set_option warningAsError false

theorem thresholdGoal_mem_good_of_norm_sq_eq {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : Submodule ℂ H} [K.HasOrthogonalProjection] (v : H)
    (h : ‖K.starProjection v‖^2 = ‖v‖^2) : v ∈ K := by
  have h1 : ‖K.starProjection v‖ = ‖v‖ := by
    have h0 : 0 ≤ ‖K.starProjection v‖ := norm_nonneg _
    have h0' : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith
  exact (Submodule.mem_iff_norm_starProjection K v).mpr h1

theorem thresholdGoal_general_output_from_norms {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    (v : H × H)
    (htot : ‖v.1‖^2 + ‖v.2‖^2 = 1)
    (hgood : ‖K.starProjection v.1‖^2 + ‖K.starProjection v.2‖^2 = 1) :
    v.1 = K.starProjection v.1 ∧ v.2 = K.starProjection v.2 := by
  have hle1 : ‖K.starProjection v.1‖ ≤ ‖v.1‖ := K.norm_starProjection_apply_le v.1
  have hle2 : ‖K.starProjection v.2‖ ≤ ‖v.2‖ := K.norm_starProjection_apply_le v.2
  have hsq1 : ‖K.starProjection v.1‖ ^ 2 ≤ ‖v.1‖ ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg _) hle1
    nlinarith [h]
  have hsq2 : ‖K.starProjection v.2‖ ^ 2 ≤ ‖v.2‖ ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg _) hle2
    nlinarith [h]
  have heq1 : ‖K.starProjection v.1‖^2 = ‖v.1‖^2 := by linarith
  have heq2 : ‖K.starProjection v.2‖^2 = ‖v.2‖^2 := by linarith
  exact ⟨((Submodule.starProjection_eq_self_iff (K := K) (v := v.1)).mpr
      (thresholdGoal_mem_good_of_norm_sq_eq v.1 heq1)).symm,
    ((Submodule.starProjection_eq_self_iff (K := K) (v := v.2)).mpr
      (thresholdGoal_mem_good_of_norm_sq_eq v.2 heq2)).symm⟩

theorem thresholdGoal_general_output_in_good_subspace {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    (A : H ≃ₗᵢ[ℂ] H) (e : H) (r : ℝ) (m : ℕ) (δ : ℝ) (a : ℝ)
    (hψ : ‖A e‖ = 1)
    (ha : ‖K.starProjection (A e)‖^2 = a)
    (hi : inner ℂ (A e) (K.starProjection (A e)) = (a : ℂ))
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hd0 : 0 < δ) (hd1 : δ < Real.pi/2)
    (hra : r*a = Real.sin δ^2) (hm : (2*(m:ℝ)+1)*δ = Real.pi/2) :
    (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A e K.starProjection r
      (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program m)).1 =
        K.starProjection (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A e K.starProjection r
          (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program m)).1 ∧
    (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A e K.starProjection r
      (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program m)).2 =
        K.starProjection (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A e K.starProjection r
          (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program m)).2 := by
  have hid : K.starProjection (K.starProjection (A e)) = K.starProjection (A e) :=
    (Submodule.starProjection_eq_self_iff (K := K) (v := K.starProjection (A e))).mpr
      (Submodule.starProjection_apply_mem K (A e))
  have hnorms := Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.exact_state A e K.starProjection
    a r δ m hψ hid ha hi hr hr1 hd0 hd1 hra hm
  (try dsimp only at hnorms)
  obtain ⟨h1, h2⟩ := hnorms
  exact thresholdGoal_general_output_from_norms (K := K) _ h1 h2

theorem thresholdGoal_good_projection_eq_frozen {N : ℕ} (S : Finset (Fin N)) :
    promiseGoodProjection S =
      Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ)) (markLabels N S) := by
  rfl

theorem thresholdGoal_good_projection_eq_star {N : ℕ} (S : Finset (Fin N)) :
    promiseGoodProjection S = Submodule.starProjection (promiseMarkedSpace S) := by
  rfl

theorem thresholdGoal_unmarked_basis_orthogonal {N : ℕ} (S : Finset (Fin N)) (i : Fin N)
    (hi : i ∉ S) : finEB N i ∈ (promiseMarkedSpace S)ᗮ := by
  have hgen : finEB N i ∈ (Submodule.span ℂ ((fun j : Fin N => finEB N j) ''
      {j : Fin N | markLabels N S ((fun j : Fin N => (j.val : ℤ)) j) = true}))ᗮ := by
    refine (Submodule.mem_orthogonal' _ _).2 ?_
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, hj, hxj⟩ := (Set.mem_image _ _ _).mp hx
        rw [← hxj]
        have hne : i ≠ j := by
          intro h
          exact hi (h ▸ (promiseGoodLabel_iff S j).mp (by simpa using! hj))
        exact (finEB N).orthonormal.2 hne
    | zero => simp
    | add x y _ _ ihx ihy => rw [inner_add_right, ihx, ihy, add_zero]
    | smul a x _ ih => rw [_root_.inner_smul_right, ih, mul_zero]
  have hK : (promiseMarkedSpace S)ᗮ = (Submodule.span ℂ ((fun j : Fin N => finEB N j) ''
      {j : Fin N | markLabels N S ((fun j : Fin N => (j.val : ℤ)) j) = true}))ᗮ := by
    unfold promiseMarkedSpace
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.triorthogonal_eq_orthogonal]
  rw [hK]
  exact hgen

theorem thresholdGoal_marked_space_coefficients {N : ℕ} (S : Finset (Fin N))
    (x : EuclideanSpace ℂ (Fin N)) (hx : x ∈ promiseMarkedSpace S) (i : Fin N)
    (hi : i ∉ S) : x i = 0 := by
  have horth : inner ℂ (finEB N i) x = 0 :=
    (Submodule.mem_orthogonal' (promiseMarkedSpace S) (finEB N i)).mp
      (thresholdGoal_unmarked_basis_orthogonal S i hi) x hx
  have hsingle : finEB N i = EuclideanSpace.single i (1 : ℂ) := by
    have h : finEB N = (EuclideanSpace.basisFun (Fin N) ℂ).toHilbertBasis := rfl
    rw [h]
    exact (congrFun (OrthonormalBasis.coe_toHilbertBasis
      (EuclideanSpace.basisFun (Fin N) ℂ)) i).trans (by simp)
  rw [hsingle] at horth
  rw [EuclideanSpace.inner_single_left] at horth
  simpa using! horth

theorem thresholdGoal_effective_output_of_mass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (r : ℝ) (prog : List (Fin 6))
    (hnorm : ‖(promiseRun hN S r prog).1‖^2 + ‖(promiseRun hN S r prog).2‖^2 = 1)
    (hmass : promiseGoodMass hN S r prog = 1) :
    (promiseRun hN S r prog).1 = promiseGoodProjection S (promiseRun hN S r prog).1 ∧
      (promiseRun hN S r prog).2 = promiseGoodProjection S (promiseRun hN S r prog).2 := by
  have hgood : ‖promiseGoodProjection S (promiseRun hN S r prog).1‖^2
      + ‖promiseGoodProjection S (promiseRun hN S r prog).2‖^2 = 1 := by
    have hEq : promiseGoodProjection S = Submodule.starProjection (promiseMarkedSpace S) :=
      thresholdGoal_good_projection_eq_star S
    rw [hEq]
    exact hmass
  exact thresholdGoal_general_output_from_norms (K := promiseMarkedSpace S)
    (promiseRun hN S r prog) hnorm hgood

theorem thresholdGoal_known_a_design_effective :
    ∃ (design : ℝ → ℝ × List (Fin 6)),
      ∀ (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) (t₀ : ℕ),
        0 < t₀ → t₀ ≤ N → (S.card = 0 ∨ S.card = t₀) →
        (S.card = t₀ →
          (promiseFinalState hN S design t₀).1 =
              promiseGoodProjection S (promiseFinalState hN S design t₀).1 ∧
          (promiseFinalState hN S design t₀).2 =
              promiseGoodProjection S (promiseFinalState hN S design t₀).2) ∧
        (S.card = 0 →
          promiseGoodMass hN S (design ((t₀ : ℝ)/(N : ℝ))).1
            (design ((t₀ : ℝ)/(N : ℝ))).2 = 0) := by
  obtain ⟨design, c, C, C₂, hc, hC, hC₂, hspec⟩ := bhmt_theorem16_promise_exact
  refine ⟨design, ?_⟩
  intro N hN S t₀ ht₀ ht₀N hpromise
  have h := hspec N hN S t₀ ht₀ ht₀N hpromise
  (try dsimp only at h)
  obtain ⟨_, _, hnorm, hmass, hzero, _, _, _⟩ := h
  refine ⟨?_, ?_⟩
  · intro hcard
    exact thresholdGoal_effective_output_of_mass hN S
      (design ((t₀ : ℝ)/(N : ℝ))).1 (design ((t₀ : ℝ)/(N : ℝ))).2 hnorm (hmass hcard)
  · intro hcard
    exact hzero hcard

theorem thresholdGoal_readout_supported_on_marked {N : ℕ} (S : Finset (Fin N))
    (v : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N))
    (hgood : v.1 = promiseGoodProjection S v.1 ∧ v.2 = promiseGoodProjection S v.2)
    (i : Fin N) (hi : i ∉ S) : promiseReadoutMass v i = 0 := by
  have hmem1 : v.1 ∈ promiseMarkedSpace S :=
    (Submodule.starProjection_eq_self_iff (K := promiseMarkedSpace S) (v := v.1)).mp
      hgood.1.symm
  have hmem2 : v.2 ∈ promiseMarkedSpace S :=
    (Submodule.starProjection_eq_self_iff (K := promiseMarkedSpace S) (v := v.2)).mp
      hgood.2.symm
  have hz1 : v.1 i = 0 := thresholdGoal_marked_space_coefficients S v.1 hmem1 i hi
  have hz2 : v.2 i = 0 := thresholdGoal_marked_space_coefficients S v.2 hmem2 i hi
  simp [promiseReadoutMass, hz1, hz2]

theorem thresholdGoal_readout_total {N : ℕ}
    (v : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)) :
    promiseReadoutTotal v = ‖v.1‖^2 + ‖v.2‖^2 := by
  have h1 : ‖v.1‖^2 = ∑ i, ‖v.1 i‖^2 := EuclideanSpace.norm_sq_eq v.1
  have h2 : ‖v.2‖^2 = ∑ i, ‖v.2 i‖^2 := EuclideanSpace.norm_sq_eq v.2
  simp only [promiseReadoutTotal, promiseReadoutMass]
  calc
    (∑ i, (‖v.1 i‖^2 + ‖v.2 i‖^2)) = (∑ i, ‖v.1 i‖^2) + ∑ i, ‖v.2 i‖^2 :=
      Finset.sum_add_distrib
    _ = ‖v.1‖^2 + ‖v.2‖^2 := by rw [h1, h2]

theorem thresholdGoal_readout_mass_on_marked {N : ℕ} (S : Finset (Fin N))
    (v : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N))
    (hgood : v.1 = promiseGoodProjection S v.1 ∧ v.2 = promiseGoodProjection S v.2)
    (hnorm : ‖v.1‖^2 + ‖v.2‖^2 = 1) :
    ∑ i ∈ S, promiseReadoutMass v i = 1 := by
  have htot : (∑ i, promiseReadoutMass v i) = 1 := by
    have h := thresholdGoal_readout_total v
    rw [hnorm] at h
    exact h
  have hsubset : (∑ i ∈ S, promiseReadoutMass v i) = ∑ i, promiseReadoutMass v i := by
    refine Finset.sum_subset (Finset.subset_univ S) ?_
    intro i hi hnot
    exact thresholdGoal_readout_supported_on_marked S v hgood i hnot
  rw [hsubset]
  exact htot

theorem thresholdGoal_decision_marked {N : ℕ} (S : Finset (Fin N))
    (v : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N))
    (hgood : v.1 = promiseGoodProjection S v.1 ∧ v.2 = promiseGoodProjection S v.2)
    (i : Fin N) (hmass : 0 < promiseReadoutMass v i) :
    promiseDecision S i = true := by
  by_contra hcon
  have hnot : i ∉ S := by
    by_contra hc
    have htrue : promiseDecision S i = true := by simp [promiseDecision, hc]
    exact hcon htrue
  have hz := thresholdGoal_readout_supported_on_marked S v hgood i hnot
  linarith

theorem thresholdGoal_decision_empty {N : ℕ} (S : Finset (Fin N)) (hcard : S.card = 0)
    (i : Fin N) : promiseDecision S i = false := by
  have hempty : S = ∅ := Finset.card_eq_zero.mp hcard
  have hnot : i ∉ S := by
    rw [hempty]
    simp
  simp [promiseDecision, hnot]

theorem thresholdGoal_output_width_ceil {N : ℕ} (hN : 0 < N) :
    promiseOutputWidth N = Nat.ceil (binaryLog N) := by
  rw [promiseOutputWidth, thresholdWidth_eq]

theorem thresholdGoal_output_words_cover {N : ℕ} (hN : 0 < N) :
    N ≤ thresholdWords N := thresholdWords_ge N hN

theorem thresholdGoal_output_word_value {N : ℕ} (hN : 0 < N) (i : Fin N) :
    (promiseOutputWord hN i).val = i.val := rfl

theorem thresholdGoal_output_decode_word {N : ℕ} (hN : 0 < N) (i : Fin N) :
    promiseOutputDecode hN (promiseOutputWord hN i) = i := by
  have hlt : i.val < N := i.isLt
  simp [promiseOutputDecode, promiseOutputWord, hlt]

theorem thresholdGoal_output_bit_cost {N : ℕ} (hN : 0 < N) :
    promiseOutputWidth N = thresholdWidth N := rfl

theorem thresholdGoal_sqrt_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) = 1 / Real.sqrt (b / a) := by
  have hmul : Real.sqrt (a / b) * Real.sqrt (b / a) = 1 := by
    have h1 : a / b * (b / a) = 1 := by field_simp [ne_of_gt ha, ne_of_gt hb]
    rw [← Real.sqrt_mul (le_of_lt (div_pos ha hb)) (b / a), h1]
    norm_num
  have hne : Real.sqrt (b / a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (div_pos hb ha))
  exact (eq_div_iff hne).mpr hmul

theorem thresholdGoal_f_evaluation_ledger {N : ℕ} (hN : 0 < N) (t₀ : ℕ) (ht₀ : 0 < t₀)
    (ht₀N : t₀ ≤ N) :
    ((BHMTTh16.marksCount (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design
      ((t₀ : ℝ)/(N : ℝ))).2 : ℕ) + 1 : ℝ) ≤
      (Real.pi/2 + 2) * Real.sqrt ((N : ℝ)/(t₀ : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have htNr : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have ha0 : (0 : ℝ) < (t₀ : ℝ)/(N : ℝ) := div_pos htNr hNr
  by_cases ha1 : (t₀ : ℝ)/(N : ℝ) = 1
  · have htn : (t₀ : ℝ) = N := by
      have h1 := (div_eq_iff (by exact_mod_cast hN.ne')).mp ha1
      simpa using! h1
    have hdes : Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design ((t₀ : ℝ)/(N : ℝ))
        = (0, [0]) := by
      simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design, ha1]
    rw [hdes]
    have hmc : BHMTTh16.marksCount ([0] : List (Fin 6)) = 0 := by
      simp [BHMTTh16.marksCount]
    rw [hmc]
    have hsqrt : Real.sqrt ((N : ℝ)/(t₀ : ℝ)) = 1 := by
      rw [htn]
      norm_num [hN.ne']
    rw [hsqrt]
    have hpi : (2 : ℝ) ≤ Real.pi/2 + 2 := by linarith [Real.pi_pos]
    linarith
  · have hne : (t₀ : ℝ) ≠ N := by
      intro h
      apply ha1
      rw [h, div_self hNr.ne']
    have hlt : (t₀ : ℝ) < N := lt_of_le_of_ne (by exact_mod_cast ht₀N) hne
    have halt : (t₀ : ℝ)/(N : ℝ) < 1 := (div_lt_one hNr).mpr hlt
    have hdes : Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design ((t₀ : ℝ)/(N : ℝ)) =
        (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.ratio ((t₀ : ℝ)/(N : ℝ)),
         Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program
           (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.iterations ((t₀ : ℝ)/(N : ℝ)))) := by
      simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design, ha1]
    rw [hdes]
    set m := Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.iterations ((t₀ : ℝ)/(N : ℝ)) with hm
    have hmcount := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.promise_program_marks m
    rw [hmcount]
    have hp := Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.parameters
      ((t₀ : ℝ)/(N : ℝ)) ha0 halt
    obtain ⟨_, _, _, _, _, _, _, hbound⟩ := hp
    have hmn : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hcast : ((m : ℕ) + 1 : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    calc
      ((m : ℕ) + 1 : ℝ) ≤ 2*(m : ℝ) + 1 := by
        rw [hcast]
        nlinarith
      _ ≤ (Real.pi/2+2) / Real.sqrt ((t₀ : ℝ)/(N : ℝ)) := hbound
      _ = (Real.pi/2+2) * Real.sqrt ((N : ℝ)/(t₀ : ℝ)) := by
        rw [thresholdGoal_sqrt_ratio hNr htNr]
        ring

theorem thresholdGoal_preparation_calls_ledger {N : ℕ} (hN : 0 < N) (t₀ : ℕ) (ht₀ : 0 < t₀)
    (ht₀N : t₀ ≤ N) :
    (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design
      ((t₀ : ℝ)/(N : ℝ))).2 : ℝ) ≤
      (Real.pi/2 + 2) * Real.sqrt ((N : ℝ)/(t₀ : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have htNr : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have ha0 : (0 : ℝ) < (t₀ : ℝ)/(N : ℝ) := div_pos htNr hNr
  by_cases ha1 : (t₀ : ℝ)/(N : ℝ) = 1
  · have htn : (t₀ : ℝ) = N := by
      have h1 := (div_eq_iff (by exact_mod_cast hN.ne')).mp ha1
      simpa using! h1
    have hdes : Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design ((t₀ : ℝ)/(N : ℝ))
        = (0, [0]) := by
      simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design, ha1]
    rw [hdes]
    have hc : Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls ([0] : List (Fin 6)) = 1 := by
      simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls]
    rw [hc]
    have hsqrt : Real.sqrt ((N : ℝ)/(t₀ : ℝ)) = 1 := by
      rw [htn]
      norm_num [hN.ne']
    rw [hsqrt]
    have hpi : (1 : ℝ) ≤ Real.pi/2 + 2 := by linarith [Real.pi_pos]
    linarith
  · have hne : (t₀ : ℝ) ≠ N := by
      intro h
      apply ha1
      rw [h, div_self hNr.ne']
    have hlt : (t₀ : ℝ) < N := lt_of_le_of_ne (by exact_mod_cast ht₀N) hne
    have halt : (t₀ : ℝ)/(N : ℝ) < 1 := (div_lt_one hNr).mpr hlt
    have hdes : Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design ((t₀ : ℝ)/(N : ℝ)) =
        (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.ratio ((t₀ : ℝ)/(N : ℝ)),
         Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program
           (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.iterations ((t₀ : ℝ)/(N : ℝ)))) := by
      simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design, ha1]
    rw [hdes]
    set m := Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.iterations ((t₀ : ℝ)/(N : ℝ)) with hm
    have hc :=
        Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program_calls m
    have hp := Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.parameters
      ((t₀ : ℝ)/(N : ℝ)) ha0 halt
    obtain ⟨_, _, _, _, _, _, _, hbound⟩ := hp
    have hcast : ((Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program m) : ℕ) : ℝ)
        = 2*(m : ℝ) + 1 := by rw [hc]; push_cast; ring
    calc
      (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program m) : ℝ)
          = 2*(m : ℝ) + 1 := hcast
      _ ≤ (Real.pi/2+2) / Real.sqrt ((t₀ : ℝ)/(N : ℝ)) := hbound
      _ = (Real.pi/2+2) * Real.sqrt ((N : ℝ)/(t₀ : ℝ)) := by
        rw [thresholdGoal_sqrt_ratio hNr htNr]
        ring

theorem thresholdGoal_endpoint :
    ∃ (design : ℝ → ℝ × List (Fin 6)) (c C C₂ : ℝ),
      0 < c ∧ 0 < C ∧ 0 < C₂ ∧
      ∀ (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) (t₀ : ℕ),
        0 < t₀ → t₀ ≤ N → (S.card = 0 ∨ S.card = t₀) →
        (0 ≤ (design ((t₀ : ℝ)/(N : ℝ))).1 ∧
          (design ((t₀ : ℝ)/(N : ℝ))).1 ≤ 1 ∧
          ‖(promiseFinalState hN S design t₀).1‖^2
            + ‖(promiseFinalState hN S design t₀).2‖^2 = 1 ∧
          (S.card = t₀ →
            (promiseFinalState hN S design t₀).1 =
                promiseGoodProjection S (promiseFinalState hN S design t₀).1 ∧
            (promiseFinalState hN S design t₀).2 =
                promiseGoodProjection S (promiseFinalState hN S design t₀).2) ∧
          (S.card = 0 → promiseGoodMass hN S (design ((t₀ : ℝ)/(N : ℝ))).1
            (design ((t₀ : ℝ)/(N : ℝ))).2 = 0) ∧
          c/Real.sqrt ((t₀ : ℝ)/(N : ℝ)) ≤
            (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (design ((t₀ : ℝ)/(N : ℝ))).2 : ℝ) ∧
          (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (design ((t₀ : ℝ)/(N : ℝ))).2 : ℝ) ≤
            C/Real.sqrt ((t₀ : ℝ)/(N : ℝ)) ∧
          ((BHMTTh16.marksCount (design ((t₀ : ℝ)/(N : ℝ))).2 : ℕ) + 1 : ℝ) ≤
            C₂/Real.sqrt ((t₀ : ℝ)/(N : ℝ))) := by
  obtain ⟨design, c, C, C₂, hc, hC, hC₂, hspec⟩ := bhmt_theorem16_promise_exact
  refine ⟨design, c, C, C₂, hc, hC, hC₂, ?_⟩
  intro N hN S t₀ ht₀ ht₀N hpromise
  have h := hspec N hN S t₀ ht₀ ht₀N hpromise
  (try dsimp only at h)
  obtain ⟨hd0, hd1, hnorm, hmass, hzero, hlo, hhi, hmarks⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hd0
  · exact hd1
  · exact hnorm
  · intro hcard
    exact thresholdGoal_effective_output_of_mass hN S
      (design ((t₀ : ℝ)/(N : ℝ))).1 (design ((t₀ : ℝ)/(N : ℝ))).2 hnorm (hmass hcard)
  · exact hzero
  · exact hlo
  · exact hhi
  · exact hmarks

theorem clause40_printed_timeout_eq (N : ℕ) : sourcePrintedTimeout N = sourceTimeout N := by
  unfold sourcePrintedTimeout sourceTimeout
  rfl

theorem clause40_printed_timeout_eq_twice_mean (N : ℕ) :
    sourcePrintedTimeout N = 2 * sourceMeanBudget N := by
  rw [clause40_printed_timeout_eq, sourceTimeout_eq_twice]

set_option maxHeartbeats 1000000 in

theorem clause40_source_cutoff_attainment_half_on {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ clause40AttainmentMassOn ranked hN (sourceTimeout N) := by
  obtain ⟨q, hq, _, hqb⟩ := bbht_source_attainment_moment ranked hN
  obtain ⟨p, hp, hhalf, _⟩ := nonnegative_clock_half_mass
    (mass := (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked))
    (clock := fun x : Fin N × List (SearchTrace N) =>
      (clause40SourceLaw ranked hN).runClock x.2)
    (hmass := ((clause40SourceLaw ranked hN).initialMass_normalized (clause40SourceSkip ranked) hN).1)
    (hmnn := ((clause40SourceLaw ranked hN).initialMass_normalized (clause40SourceSkip ranked) hN).2)
    (hcnn := fun x : Fin N × List (SearchTrace N) =>
      (clause40SourceLaw ranked hN).runClock_nonneg x.2)
    q (sourceMeanBudget N) hq hqb (sourceMeanBudget_pos N hN)
  rw [← sourceTimeout_eq_twice N] at hp
  have heq : clause40AttainmentMassOn ranked hN (sourceTimeout N) = p := by
    unfold clause40AttainmentMassOn
    exact hp.tsum_eq
  rw [heq]
  exact hhalf

theorem clause40_source_cutoff_attainment_half {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ clause40AttainmentMass T hN (sourceTimeout N) :=
  clause40_source_cutoff_attainment_half_on (SortedRankedTable.ofTable T) hN

theorem clause40_one_element_mass {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable 1 α) (hN : 0 < 1) (x : Fin 1 × List (SearchTrace 1)) :
    (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked) x =
      if x.2 = [] then (1 : ℝ) else 0 := by
  have hnext (y : Fin 1) : (clause40SourceSkip ranked).next y = 0 := by
    have hle := SortedRankedTable.lowerCut_le ranked y
    have hval : (ranked.lowerCut y).val ≤ y.val := Fin.mk_le_mk.mp hle
    have hrw : (clause40SourceSkip ranked).next y = (ranked.lowerCut y).val := rfl
    rw [hrw]
    omega
  have hrun : ∀ xs : List (SearchTrace 1),
      (clause40SourceLaw ranked hN).runMass (clause40SourceSkip ranked) 0 xs =
        if xs = [] then 1 else 0 := by
    intro xs
    cases xs with
    | nil => simp [RankedCallLaw.runMass]
    | cons y ys => simp [RankedCallLaw.runMass]
  simp only [RankedCallLaw.initialMass]
  rw [hnext x.1, hrun x.2]
  simp

theorem clause40_attainment_mass_one {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable 1 α) (hN : 0 < 1) (cutoff : ℝ) (hc : 0 ≤ cutoff) :
    clause40AttainmentMassOn ranked hN cutoff = 1 := by
  have hgood (x : Fin 1 × List (SearchTrace 1)) :
      (if (clause40SourceLaw ranked hN).runClock x.2 ≤ cutoff then
        (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked) x else 0) =
      (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked) x := by
    by_cases h : (clause40SourceLaw ranked hN).runClock x.2 ≤ cutoff
    · simp [h]
    · have hz : (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked) x = 0 := by
        rw [clause40_one_element_mass ranked hN x]
        split_ifs with hxs
        · have hclk : (clause40SourceLaw ranked hN).runClock ([] : List (SearchTrace 1)) = 0 := rfl
          rw [hxs, hclk] at h
          linarith
        · rfl
      simp [h, hz]
  have hsum := (clause40SourceLaw ranked hN).initialMass_normalized (clause40SourceSkip ranked) hN
  have hconv : HasSum (fun x : Fin 1 × List (SearchTrace 1) =>
      if (clause40SourceLaw ranked hN).runClock x.2 ≤ cutoff then
        (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked) x else 0) 1 := by
    rw [← show (fun x : Fin 1 × List (SearchTrace 1) =>
        (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked) x) =
        (fun x : Fin 1 × List (SearchTrace 1) =>
          if (clause40SourceLaw ranked hN).runClock x.2 ≤ cutoff then
            (clause40SourceLaw ranked hN).initialMass (clause40SourceSkip ranked) x else 0)
        from funext fun x => (hgood x).symm]
    exact hsum.1
  unfold clause40AttainmentMassOn
  exact hconv.tsum_eq

theorem clause40_native_cutoff_bounds (N : ℕ) :
    sourceTimeout N ≤ (sourceNativeCutoff N : ℝ) ∧
      (sourceNativeCutoff N : ℝ) < sourceTimeout N + 1 := by
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    by_cases h : N = 0
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h))
  have hnonneg : 0 ≤ sourcePrintedTimeout N := by
    unfold sourcePrintedTimeout
    have h1 : 0 ≤ (45 / 2 : ℝ) * Real.sqrt (N : ℝ) := by positivity
    have h2 : 0 ≤ (7 / 5 : ℝ) * (binaryLog N) ^ 2 := by positivity
    linarith
  rw [← clause40_printed_timeout_eq]
  unfold sourceNativeCutoff
  constructor
  · exact Nat.le_ceil _
  · exact Nat.ceil_lt_add_one hnonneg

theorem clause40_init_charge_rounding (N : ℕ) (hN : 0 < N) :
    binaryLog N ≤ (initCharge N : ℝ) ∧ (initCharge N : ℝ) < binaryLog N + 1 := by
  unfold initCharge
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt h))
  constructor
  · exact Nat.le_ceil _
  · exact Nat.ceil_lt_add_one (by
      unfold binaryLog
      exact div_nonneg hlog (Real.log_pos (by norm_num)).le)

theorem clause40_native_clock_bounds {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) (hN : 0 < N) (xs : List (SearchTrace N)) :
    (clause40SourceLaw ranked hN).runClock xs ≤ sourceNativeClock N xs ∧
      sourceNativeClock N xs ≤ (clause40SourceLaw ranked hN).runClock xs + xs.length := by
  have hround := clause40_init_charge_rounding N hN
  have hdur (x : SearchTrace N) :
      (clause40SourceLaw ranked hN).duration x =
        (Qatlib.Concepts.AmplitudeSearch.InterruptMin.TerminalCost
          (Qatlib.Concepts.SearchStopping.UnknownCount.ExponentialSizes N) x : ℝ) + binaryLog N := rfl
  induction xs with
  | nil =>
    simp only [RankedCallLaw.runClock, sourceNativeClock, List.map_nil, List.sum_nil,
      List.length_nil]
    constructor <;> linarith
  | cons x xs ih =>
    obtain ⟨hlo, hhi⟩ := ih
    simp only [RankedCallLaw.runClock, sourceNativeClock, List.map_cons, List.sum_cons,
      List.length_cons] at hlo hhi ⊢
    push_cast
    rw [hdur]
    constructor <;> linarith [hround.1, hround.2.le]

theorem clause40_run_length_bound {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) (hN : 0 < N) (i : Fin N) (xs : List (SearchTrace N))
    (hm : 0 < (clause40SourceLaw ranked hN).runMass (clause40SourceSkip ranked)
      ((clause40SourceSkip ranked).next i) xs) :
    xs.length ≤ N := by
  have hnext : (clause40SourceSkip ranked).next i < N :=
    lt_of_le_of_lt (RankSkip.le_rank _ _) i.isLt
  obtain ⟨_, hlen⟩ :=
    (clause40SourceLaw ranked hN).runMass_terminates (clause40SourceSkip ranked) _ hnext xs hm
  omega

theorem clause40_native_budget_sufficient {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) (hN : 0 < N) (i : Fin N) (xs : List (SearchTrace N))
    (hm : 0 < (clause40SourceLaw ranked hN).runMass (clause40SourceSkip ranked)
      ((clause40SourceSkip ranked).next i) xs)
    (hc : (clause40SourceLaw ranked hN).runClock xs ≤ sourceTimeout N) :
    sourceNativeClock N xs ≤ (sourceNativeBudget N : ℝ) := by
  obtain ⟨hlo, hhi⟩ := clause40_native_clock_bounds ranked hN xs
  have hlen := clause40_run_length_bound ranked hN i xs hm
  have hlen' : (xs.length : ℝ) ≤ (N : ℝ) := by exact_mod_cast hlen
  have hcut : sourceTimeout N ≤ (sourceNativeCutoff N : ℝ) := (clause40_native_cutoff_bounds N).1
  have hnat : (sourceNativeBudget N : ℝ) =
      (sourceNativeCutoff N : ℝ) + (N : ℝ) := by
    simp only [sourceNativeBudget, Nat.cast_add]
  rw [hnat]
  linarith

theorem clause40_same_one_call_mass {N : ℕ} {α : Type*} [LinearOrder α]
    (ranked : SortedRankedTable N α) (hN : 0 < N) (t : ℕ) (x : SearchTrace N) :
    (clause40SourceLaw ranked hN).mass t x =
      (chargedBBHTLaw ranked.indexOfRank hN).mass t x := rfl

theorem clause40_charged_budget_four_fold (N : ℕ) :
    chargedBudget N = Nat.ceil (4 * sourceTimeout N) := chargedBudget_eq_four_sourceTimeout N

theorem clause40_charged_mean_four_fold (N : ℕ) :
    chargedMeanBudget N = 4 * sourceMeanBudget N := rfl

theorem clause40_source_cutoff_below_charged_budget (N : ℕ) (hN : 0 < N) :
    sourceTimeout N < (chargedBudget N : ℝ) := by
  have hpos : 0 < sourceTimeout N := by
    rw [sourceTimeout_eq_twice N]
    exact mul_pos (by norm_num) (sourceMeanBudget_pos N hN)
  have hceil : (4 : ℝ) * sourceTimeout N ≤ (chargedBudget N : ℝ) := by
    rw [clause40_charged_budget_four_fold]
    exact Nat.le_ceil _
  linarith

theorem clause40_source_cutoff_not_charged_cutoff (N : ℕ) (hN : 0 < N) :
    sourceTimeout N ≠ (chargedBudget N : ℝ) := by
  intro h
  have hceil : (4 : ℝ) * sourceTimeout N ≤ (chargedBudget N : ℝ) := by
    rw [clause40_charged_budget_four_fold]
    exact Nat.le_ceil _
  have hpos : 0 < sourceTimeout N := by
    rw [sourceTimeout_eq_twice N]
    exact mul_pos (by norm_num) (sourceMeanBudget_pos N hN)
  linarith

theorem clause40_tied_marked_is_strict_value {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (y : Fin N) :
    rankMarked T.indexOfRank (T.lowerCut y).val =
      Finset.univ.filter (fun i => T.value i < T.value (T.indexOfRank y)) :=
  rankMarked_eq_strict_values T y

def clause40TiedTable : Fin 3 → ℕ := fun i => if i.val = 2 then 1 else 0

theorem clause40_tied_table_minima :
    (∀ j, clause40TiedTable 0 ≤ clause40TiedTable j) ∧
      (∀ j, clause40TiedTable 1 ≤ clause40TiedTable j) ∧
      ¬ (∀ j, clause40TiedTable 2 ≤ clause40TiedTable j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp [clause40TiedTable]
  · intro j
    fin_cases j <;> simp [clause40TiedTable]
  · intro h
    have h2 := h ⟨0, by norm_num⟩
    simp [clause40TiedTable] at h2

theorem clause40_tied_table_cutoff_attainment_half (hN : 0 < 3) :
    (1 / 2 : ℝ) ≤ clause40AttainmentMass clause40TiedTable hN (sourceTimeout 3) := by
  exact clause40_source_cutoff_attainment_half clause40TiedTable hN

private theorem clause41_event_total {β : Type*} (p : PMF β) (E : β → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => ¬ E x) = 1 := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
  calc
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun _ => 1) := by
      congr 1
      funext x
      by_cases hx : E x <;> simp [hx]
    _ = 1 := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const p 1

private theorem clause41_event_le_one {β : Type*} (p : PMF β) (E : β → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E ≤ 1 := by
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => ¬ E x) := le_self_add
    _ = 1 := clause41_event_total p E

theorem clause41_independent_failure_step {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) :
    clause41IndependentFailure T hN budget (c + 1) =
      clause41IndependentFailure T hN budget c * clause41SingleFailure T hN budget := by
  have hpmf : clause41IndependentPMF T hN budget (c + 1) =
      (clause41IndependentPMF T hN budget c).bind fun p =>
        (chargedInitialPMF T hN budget).bind fun f =>
          PMF.pure (amplifiedCombine T p.1 f.1, p.2 + f.2) := rfl
  unfold clause41IndependentFailure clause41SingleFailure
  rw [hpmf]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  simp_rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
    amplifiedCombine_minimum_iff, not_or]
  have he (p : Fin N × ℕ) :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (chargedInitialPMF T hN budget)
        (fun f => if (¬∀ j, T p.1 ≤ T j) ∧ (¬∀ j, T f.1 ≤ T j) then 1 else 0) =
      (if (¬∀ j, T p.1 ≤ T j) then (1 : ℝ≥0∞) else 0) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (chargedInitialPMF T hN budget)
          (fun f => if (¬∀ j, T f.1 ≤ T j) then 1 else 0) := by
    by_cases hp : ∀ j, T p.1 ≤ T j <;> simp [hp]
  simp_rw [he]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
  rw [← ENNReal.tsum_mul_right]
  congr 1
  funext p
  by_cases hp : ∀ j, T p.1 ≤ T j <;> simp [hp]

theorem clause41_independent_failure_exact {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) :
    clause41IndependentFailure T hN budget c =
      clause41IndependentFailure T hN budget 0 * (clause41SingleFailure T hN budget) ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [clause41_independent_failure_step, ih, pow_succ]
    ring

theorem clause41_independent_success_exact {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) :
    (clause41IndependentSuccess T hN budget c).toReal =
      1 - (clause41IndependentFailure T hN budget 0).toReal *
            ((clause41SingleFailure T hN budget).toReal) ^ c := by
  have htot : clause41IndependentSuccess T hN budget c +
      clause41IndependentFailure T hN budget c = 1 := by
    unfold clause41IndependentSuccess clause41IndependentFailure
    exact clause41_event_total (clause41IndependentPMF T hN budget c) (fun x => ∀ j, T x.1 ≤ T j)
  have hsne : clause41IndependentSuccess T hN budget c ≠ ∞ := by
    have h := clause41_event_le_one (clause41IndependentPMF T hN budget c)
      (fun x => ∀ j, T x.1 ≤ T j)
    exact ne_of_lt (h.trans_lt (by simp))
  have hfne : clause41IndependentFailure T hN budget c ≠ ∞ := by
    have h := clause41_event_le_one (clause41IndependentPMF T hN budget c)
      (fun x => ¬∀ j, T x.1 ≤ T j)
    exact ne_of_lt (h.trans_lt (by simp))
  have hreals := congrArg ENNReal.toReal htot
  rw [ENNReal.toReal_add hsne hfne, ENNReal.toReal_one] at hreals
  have hf0 : clause41IndependentFailure T hN budget 0 ≤ 1 :=
    clause41_event_le_one (clause41IndependentPMF T hN budget 0) (fun x => ¬∀ j, T x.1 ≤ T j)
  have hsf : clause41SingleFailure T hN budget ≤ 1 :=
    clause41_event_le_one (chargedInitialPMF T hN budget) (fun x => ¬∀ j, T x.1 ≤ T j)
  have hsp : (clause41SingleFailure T hN budget) ^ c ≤ 1 :=
    pow_le_one₀ (bot_le) hsf
  have hfail_ne : clause41IndependentFailure T hN budget 0 ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hf0 (by simp))
  have hsp_ne : (clause41SingleFailure T hN budget) ^ c ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hsp (by simp))
  have hsf_ne : clause41SingleFailure T hN budget ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hsf (by simp))
  have htoR : (clause41IndependentFailure T hN budget c).toReal =
      (clause41IndependentFailure T hN budget 0).toReal *
        ((clause41SingleFailure T hN budget).toReal) ^ c := by
    rw [clause41_independent_failure_exact]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [htoR] at hreals
  linarith

theorem clause41_no_progress_success {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α)
    (hN : 0 < N) (budget : ℕ) (hbudget : budget < initCharge N) :
    clause41SingleSuccess T hN budget =
      ENNReal.ofReal ((∑ i : Fin N, if ∀ j, T i ≤ T j then (1 : ℝ) else 0) / (N : ℝ)) := by
  unfold clause41SingleSuccess
  rw [chargedInitialPMF_success]
  unfold chargedInitialSuccess
  have hstep : ∀ current : Fin N,
      minimumBudgetSuccessWithInit T (initCharge N) budget current =
        (if ∀ j, T current ≤ T j then (1 : ℝ) else 0) := by
    intro current
    unfold minimumBudgetSuccessWithInit
    have hpay : (fun i _ => if ∀ j, T i ≤ T j then (1 : ℝ) else 0) current budget =
        (if ∀ j, T current ≤ T j then (1 : ℝ) else 0) := rfl
    by_cases hsingle : N = 1
    · rw [minimumBudgetEvalWithInit, if_pos hsingle]
    · rw [minimumBudgetEvalWithInit, if_neg hsingle]
      by_cases hpaid : initCharge N ≤ budget
      · omega
      · rw [if_neg hpaid]
  simp_rw [hstep]

theorem clause41_placeholder_failure {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α)
    (hN : 0 < N) (budget : ℕ) (hnone : ¬ ∀ j, T (clause41Placeholder hN) ≤ T j) :
    (clause41IndependentFailure T hN budget 0).toReal = 1 := by
  unfold clause41IndependentFailure
  rw [show clause41IndependentPMF T hN budget 0 = PMF.pure (clause41Placeholder hN, 0) from rfl]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
  rw [show (fun x => ¬ ∀ (j : Fin N), T x.1 ≤ T j) (clause41Placeholder hN, 0) =
      (¬ ∀ (j : Fin N), T (clause41Placeholder hN) ≤ T j) from rfl]
  rw [if_pos hnone]
  simp

theorem clause41_counterexample_two_runs {α : Type*} [LinearOrder α] (T : Fin 2 → α)
    (hN : 0 < 2) (hmin : ∀ j, T 1 ≤ T j) (hnone : ¬ ∀ j, T (clause41Placeholder hN) ≤ T j) :
    (clause41SingleSuccess T hN 0).toReal = 1 / 2 ∧
      (clause41IndependentSuccess T hN 0 2).toReal = 3 / 4 := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hbin : binaryLog 2 = 1 := by
    unfold binaryLog
    exact div_self hlog2
  have hinit : (1 : ℝ) ≤ initCharge 2 := by
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hbin' : binaryLog (2 : ℝ) = 1 := by
      unfold binaryLog
      exact div_self hlog2
    simp only [initCharge, Nat.cast_ofNat, hbin']
    exact Nat.le_ceil _
  have hinitN : 1 ≤ initCharge 2 := by exact_mod_cast hinit
  have hinitpos : 0 < initCharge 2 := by omega
  have hzero : (0 : Fin 2) = clause41Placeholder hN := rfl
  have hsum : (∑ i : Fin 2, if ∀ j, T i ≤ T j then (1 : ℝ) else 0) = 1 := by
    rw [Fin.sum_univ_two, hzero]
    have h0 : (if ∀ j, T (clause41Placeholder hN) ≤ T j then (1 : ℝ) else 0) = 0 := if_neg hnone
    have h1 : (if ∀ j, T 1 ≤ T j then (1 : ℝ) else 0) = 1 := if_pos hmin
    rw [h0, h1]
    norm_num
  have hsucc : (clause41SingleSuccess T hN 0).toReal = 1 / 2 := by
    rw [clause41_no_progress_success T hN 0 (by omega), hsum]
    rw [ENNReal.toReal_ofReal (by positivity)]
    norm_num
  have hsfail : (clause41SingleFailure T hN 0).toReal = 1 / 2 := by
    have htot : clause41SingleSuccess T hN 0 + clause41SingleFailure T hN 0 = 1 := by
      unfold clause41SingleSuccess clause41SingleFailure
      exact clause41_event_total (chargedInitialPMF T hN 0) (fun x => ∀ j, T x.1 ≤ T j)
    have hsne : clause41SingleSuccess T hN 0 ≠ ∞ := by
      have h := clause41_event_le_one (chargedInitialPMF T hN 0) (fun x => ∀ j, T x.1 ≤ T j)
      exact ne_of_lt (h.trans_lt (by simp))
    have hfne : clause41SingleFailure T hN 0 ≠ ∞ := by
      have h := clause41_event_le_one (chargedInitialPMF T hN 0) (fun x => ¬∀ j, T x.1 ≤ T j)
      exact ne_of_lt (h.trans_lt (by simp))
    have hr := congrArg ENNReal.toReal htot
    rw [ENNReal.toReal_add hsne hfne, ENNReal.toReal_one] at hr
    linarith
  have hifail : (clause41IndependentFailure T hN 0 2).toReal = 1 / 4 := by
    rw [clause41_independent_failure_exact]
    have hf0 : clause41IndependentFailure T hN 0 0 ≤ 1 :=
      clause41_event_le_one (clause41IndependentPMF T hN 0 0) (fun x => ¬∀ j, T x.1 ≤ T j)
    have hsf : clause41SingleFailure T hN 0 ≤ 1 :=
      clause41_event_le_one (chargedInitialPMF T hN 0) (fun x => ¬∀ j, T x.1 ≤ T j)
    have hsp : (clause41SingleFailure T hN 0) ^ 2 ≤ 1 := pow_le_one₀ (bot_le) hsf
    have hf0ne : clause41IndependentFailure T hN 0 0 ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt hf0 (by simp))
    have hspne : (clause41SingleFailure T hN 0) ^ 2 ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt hsp (by simp))
    have hsfne : clause41SingleFailure T hN 0 ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt hsf (by simp))
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
    rw [clause41_placeholder_failure T hN 0 hnone, hsfail]
    norm_num
  have hsucc2 : (clause41IndependentSuccess T hN 0 2).toReal = 3 / 4 := by
    rw [clause41_independent_success_exact]
    rw [clause41_placeholder_failure T hN 0 hnone, hsfail]
    norm_num
  exact ⟨hsucc, hsucc2⟩

theorem clause41_source_sentence_false_at_small_budget {α : Type*} [LinearOrder α]
    (T : Fin 2 → α) (hN : 0 < 2) (hmin : ∀ j, T 1 ≤ T j)
    (hnone : ¬ ∀ j, T (clause41Placeholder hN) ≤ T j) :
    (clause41SingleSuccess T hN (2 * 0)).toReal <
      (clause41IndependentSuccess T hN 0 2).toReal := by
  obtain ⟨h1, h2⟩ := clause41_counterexample_two_runs T hN hmin hnone
  have hzero : (2 * 0 : ℕ) = 0 := rfl
  rw [hzero]
  linarith

theorem clause41_source_sentence_holds_iff {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (c : ℕ) :
    (clause41SingleSuccess T hN (c * budget)).toReal ≥
        (clause41IndependentSuccess T hN budget c).toReal ↔
      (clause41SingleSuccess T hN (c * budget)).toReal ≥
        1 - (clause41IndependentFailure T hN budget 0).toReal *
              ((clause41SingleFailure T hN budget).toReal) ^ c := by
  rw [clause41_independent_success_exact]

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
