/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchEstimation
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchStopping
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AePaddingOutputTransport

open Qatlib
open Qatlib
open Qatlib

open scoped Classical
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem applyGate_aeControlledGate_clean_flag (M : ℕ) (U : Matrix I I ℂ)
    {ψ : QState (Fin M × (Bool × I))} (hclean : ∀ z i, ψ (z, (true, i)) = 0) :
    ApplyGate (aeControlledGate M U) ψ = ψ := by
  funext p
  obtain ⟨x, b, i⟩ := p
  rw [aeControlledGate, phaseControlledOracle_apply]
  cases b <;> simp [ApplyGate, Matrix.mulVec, dotProduct, Matrix.one_apply, hclean]

theorem ae_padded_output_state_eq (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    Run (aeControlledGate M (preparedMark S)) (aePaddedAECircuit M A j)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))) =
      Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))) := by
  have hclean : ∀ z i, (Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))))
      (z, (true, i)) = 0 :=
    (prepared_ae_expanded_access_and_output M hM A j S hA).2.2.2.2.2
  rw [aePaddedAECircuit, run_append]
  simp only [run_query, run_nil]
  exact applyGate_aeControlledGate_clean_flag M (preparedMark S) hclean

noncomputable def aePaddedLaw (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) : FinDist (Fin M) where
  prob z := MeasureProb
    (Run (aeControlledGate M (preparedMark S)) (aePaddedAECircuit M A j)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))))
    (Finset.univ.filter (fun p => p.1 = z))
  nonneg z := measureProb_nonneg _ _
  sum_one := by
    have hr := ae_padded_output_state_eq M A j S hM hA
    have hsum : ∑ z : Fin M, MeasureProb
        (Run (aeControlledGate M (preparedMark S)) (aePaddedAECircuit M A j)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))))
        (Finset.univ.filter (fun p => p.1 = z)) = ∑ z : Fin M, MeasureProb
        (Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))))
        (Finset.univ.filter (fun p => p.1 = z)) :=
      Finset.sum_congr rfl fun z _ => by rw [hr]
    rw [hsum]
    exact (aeLaw M A j S hA hM).sum_one

theorem aePaddedLaw_prob (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) (z : Fin M) :
    (aePaddedLaw M A j S hA hM).prob z = (aeLaw M A j S hA hM).prob z := by
  show MeasureProb (Run (aeControlledGate M (preparedMark S)) (aePaddedAECircuit M A j)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))))
      (Finset.univ.filter (fun p => p.1 = z)) = _
  rw [ae_padded_output_state_eq M A j S hM hA]
  rfl

theorem aePaddedLaw_eq_aeLaw (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) :
    aePaddedLaw M A j S hA hM = aeLaw M A j S hA hM := by
  cases hP : aePaddedLaw M A j S hA hM with
  | mk p1 h1n h1s =>
    cases hL : aeLaw M A j S hA hM with
    | mk p2 h2n h2s =>
      have hprob : p1 = p2 := by
        funext z
        have h := aePaddedLaw_prob M A j S hA hM z
        rw [hP, hL] at h
        simpa using! h
      subst hprob
      rfl

theorem padded_query_exact_M (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (j : I) :
    QueryCount (aePaddedAECircuit M A j) = M ∧
      GateCount (aePaddedAECircuit M A j) = 5 * (M - 1) + 3 :=
  ⟨ae_padded_query_count M hM A j, ae_padded_gate_count M hM A j⟩

theorem padded_k2_window_strict (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) (hk : 2 ≤ k) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |aeEstimate M z - MeasureProb (preparedAAState A j) S| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt (MeasureProb (preparedAAState A j) S*
            (1-MeasureProb (preparedAAState A j) S))/(M : ℝ) +
            (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
      (aePaddedLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1)) := by
  simpa only [aePaddedLaw_prob] using! (clause83_endpoint (I := I)).2.1 M A j S hM hA k hk

theorem padded_odd_M_window_strict (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) (hk : 2 ≤ k)
    (hodd : M % 2 = 1) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |aeEstimate M z - MeasureProb (preparedAAState A j) S| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt (MeasureProb (preparedAAState A j) S*
            (1-MeasureProb (preparedAAState A j) S))/(M : ℝ) +
            (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
      (aePaddedLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1)) := by
  simpa only [aePaddedLaw_prob] using!
      (clause83_endpoint (I := I)).2.2.2.2.2 M A j S hM hA k hk hodd

theorem padded_k1_window_eight_pi_sq (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |aeEstimate M z - MeasureProb (preparedAAState A j) S| ≤
          2*Real.pi*Real.sqrt (MeasureProb (preparedAAState A j) S*
            (1-MeasureProb (preparedAAState A j) S))/(M : ℝ) +
            Real.pi^2/(M : ℝ)^2),
      (aePaddedLaw M A j S hA hM).prob z ≥ 8/Real.pi^2 := by
  simpa only [aePaddedLaw_prob] using!
    (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).1

theorem padded_endpoint_zero (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j) S = 0) :
    (aePaddedLaw M A j S hA hM).prob (⟨0, by omega⟩ : Fin M) = 1 := by
  rw [aePaddedLaw_prob]
  exact (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).2.1 ha

theorem padded_endpoint_one_even (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hdiv : 2 ∣ M)
    (ha : MeasureProb (preparedAAState A j) S = 1) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M => aeEstimate M z = 1),
      (aePaddedLaw M A j S hA hM).prob z = 1 := by
  simpa only [aePaddedLaw_prob] using!
    (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).2.2 ha hdiv

theorem count_padded_k2_window_strict (N M : ℕ) (S : Finset (Fin N)) (hN : 0 < N)
    (hM : 2 ≤ M) (k : ℕ) (hk : 2 ≤ k) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ) +
            Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2),
      (aePaddedLaw M (QFTMatrix N) (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z >
        1 - 1 / (2 * ((k : ℝ) - 1)) ∧
    QueryCount (aePaddedAECircuit (I := Fin N) M (QFTMatrix N) ⟨0, hN⟩) = M ∧
    GateCount (aePaddedAECircuit (I := Fin N) M (QFTMatrix N) ⟨0, hN⟩) = 5 * (M - 1) + 3 := by
  refine ⟨?_, ae_padded_query_count M (by omega) (QFTMatrix N) ⟨0, hN⟩,
    ae_padded_gate_count M (by omega) (QFTMatrix N) ⟨0, hN⟩⟩
  simpa only [aePaddedLaw_prob] using! (clause83_endpoint (I := Fin 1)).2.2.1 N M S hN hM k hk

private theorem count_n1_a_eq_card (S : Finset (Fin 1)) :
    MeasureProb (preparedAAState (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1)) S = (S.card : ℝ) := by
  have hzero : ∀ x : Fin 1, x.val = 0 := fun x => by have := x.isLt; omega
  have hxe : ∀ x : Fin 1, x = (⟨0, by norm_num⟩ : Fin 1) := fun x => Fin.ext (hzero x)
  by_cases hS : S = ∅
  · subst hS
    simp [MeasureProb]
  · have hfull : S = Finset.univ := by
      refine Finset.eq_univ_of_forall fun x => ?_
      by_contra hx
      obtain ⟨y, hy⟩ := S.eq_empty_or_nonempty.resolve_left hS
      exact hx ((hxe x) ▸ ((hxe y) ▸ hy))
    subst hfull
    have hone : preparedAAState (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1)
        (0 : Fin 1) = 1 := by
      simp [preparedAAState, ApplyGate, Qatlib.Foundations.PureStateMath.Ket, QFTMatrix,
        Matrix.mulVec, dotProduct]
    have hmp : MeasureProb (preparedAAState (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1))
        (Finset.univ : Finset (Fin 1)) = 1 := by
      simp only [MeasureProb, BornProb, Fin.sum_univ_one]
      rw [hone]
      norm_num
    rw [hmp]
    simp

theorem count_n1_boundary (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin 1)) :

    (S.card = 0 ∨ S.card = 1) ∧

    (∀ k : ℕ, 2 ≤ k →
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          |(1 : ℝ)*aeEstimate M z - (S.card : ℝ)| ≤
            2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((1 : ℝ)-S.card))/(M : ℝ) +
              Real.pi^2*(k : ℝ)^2*(1 : ℝ)/(M : ℝ)^2),
        (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
          (qftMatrix_unitary (by norm_num)) hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1))) ∧

    (S.card = 0 →
      (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
        (qftMatrix_unitary (by norm_num)) hM).prob (⟨0, by omega⟩ : Fin M) = 1) ∧

    (S.card = 1 → 2 ∣ M → ∀ k : ℕ, 1 ≤ k →
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          |(1 : ℝ)*aeEstimate M z - (1 : ℝ)| ≤
            2*Real.pi*(k : ℝ)*Real.sqrt ((1 : ℝ)*((1 : ℝ)-(1 : ℝ)))/(M : ℝ) +
              Real.pi^2*(k : ℝ)^2*(1 : ℝ)/(M : ℝ)^2),
        (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
          (qftMatrix_unitary (by norm_num)) hM).prob z = 1) ∧

    (MeasureProb (preparedAAState (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1)) S = (S.card : ℝ) ∧
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          |aeEstimate M z - (S.card : ℝ)| ≤
            2*Real.pi*Real.sqrt ((S.card : ℝ)*((1 : ℝ)-(S.card : ℝ)))/(M : ℝ) +
              Real.pi^2/(M : ℝ)^2),
        (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
          (qftMatrix_unitary (by norm_num)) hM).prob z ≥ 8/Real.pi^2) := by
  have hA : (QFTMatrix 1 : Matrix (Fin 1) (Fin 1) ℂ) ∈
      Matrix.unitaryGroup (Fin 1) ℂ := qftMatrix_unitary (by norm_num)
  have hcard : S.card ≤ 1 := by
    have hsub : S.card ≤ (Finset.univ : Finset (Fin 1)).card :=
      Finset.card_le_card (Finset.subset_univ S)
    rwa [Finset.card_univ, Fintype.card_fin] at hsub
  refine ⟨by omega, fun k hk => by
        have h := (count_padded_k2_window_strict 1 M S (by norm_num) hM k hk).1
        simpa only [Nat.cast_one] using! h,
    ?_, ?_, ?_⟩
  · intro hcard0
    have hS0 : S = ∅ := Finset.card_eq_zero.mp hcard0
    subst hS0
    exact padded_endpoint_zero M (QFTMatrix 1) ⟨0, by norm_num⟩ ∅ hM hA
      (by simp [MeasureProb])
  · intro hcard1 hdiv k _hk
    have ha1 : MeasureProb (preparedAAState (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1)) S = 1 := by
      rw [count_n1_a_eq_card, hcard1]
      norm_cast
    have hcarrier := padded_endpoint_one_even M (QFTMatrix 1) ⟨0, by norm_num⟩ S hM hA hdiv ha1
    have hsub : Finset.univ.filter (fun z : Fin M => aeEstimate M z = 1) ⊆
        Finset.univ.filter (fun z : Fin M =>
          |(1 : ℝ)*aeEstimate M z - (1 : ℝ)| ≤
            2*Real.pi*(k : ℝ)*Real.sqrt ((1 : ℝ)*((1 : ℝ)-(1 : ℝ)))/(M : ℝ) +
              Real.pi^2*(k : ℝ)^2*(1 : ℝ)/(M : ℝ)^2) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [hz, one_mul, sub_self, abs_zero]
      positivity
    refine le_antisymm ?_ ?_
    · calc ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
            |(1 : ℝ)*aeEstimate M z - (1 : ℝ)| ≤
              2*Real.pi*(k : ℝ)*Real.sqrt ((1 : ℝ)*((1 : ℝ)-(1 : ℝ)))/(M : ℝ) +
                Real.pi^2*(k : ℝ)^2*(1 : ℝ)/(M : ℝ)^2),
          (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
            (qftMatrix_unitary (by norm_num)) hM).prob z
          ≤ ∑ z ∈ Finset.univ, (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
            (qftMatrix_unitary (by norm_num)) hM).prob z :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun z _ _ => (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
                (qftMatrix_unitary (by norm_num)) hM).nonneg z)
        _ = 1 := (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
          (qftMatrix_unitary (by norm_num)) hM).sum_one
    · calc (1 : ℝ) = ∑ z ∈ Finset.univ.filter (fun z : Fin M => aeEstimate M z = 1),
            (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
              (qftMatrix_unitary (by norm_num)) hM).prob z := hcarrier.symm
        _ ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
              |(1 : ℝ)*aeEstimate M z - (1 : ℝ)| ≤
                2*Real.pi*(k : ℝ)*Real.sqrt ((1 : ℝ)*((1 : ℝ)-(1 : ℝ)))/(M : ℝ) +
                  Real.pi^2*(k : ℝ)^2*(1 : ℝ)/(M : ℝ)^2),
            (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
              (qftMatrix_unitary (by norm_num)) hM).prob z :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun z _ _ => (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
              (qftMatrix_unitary (by norm_num)) hM).nonneg z)
  · refine ⟨count_n1_a_eq_card S, ?_⟩
    have hsrc := padded_k1_window_eight_pi_sq M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
      hM hA
    have ha := count_n1_a_eq_card S
    rw [← ha]
    exact hsrc

set_option linter.unusedVariables false in

theorem frontier1 :

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ),
      Run (aeControlledGate M (preparedMark S)) (aePaddedAECircuit M A j)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))) =
        Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j)))) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (z : Fin M),
      (aePaddedLaw M A j S hA hM).prob z = (aeLaw M A j S hA hM).prob z) ∧

    (∀ (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (j : I),
      QueryCount (aePaddedAECircuit M A j) = M ∧
        GateCount (aePaddedAECircuit M A j) = 5 * (M - 1) + 3) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) (hk : 2 ≤ k),
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          |aeEstimate M z - MeasureProb (preparedAAState A j) S| ≤
            2*Real.pi*(k : ℝ)*Real.sqrt (MeasureProb (preparedAAState A j) S*
              (1-MeasureProb (preparedAAState A j) S))/(M : ℝ) +
              (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
        (aePaddedLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1))) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ),
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          |aeEstimate M z - MeasureProb (preparedAAState A j) S| ≤
            2*Real.pi*Real.sqrt (MeasureProb (preparedAAState A j) S*
              (1-MeasureProb (preparedAAState A j) S))/(M : ℝ) +
              Real.pi^2/(M : ℝ)^2),
        (aePaddedLaw M A j S hA hM).prob z ≥ 8/Real.pi^2) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ),
      MeasureProb (preparedAAState A j) S = 0 →
        (aePaddedLaw M A j S hA hM).prob (⟨0, by omega⟩ : Fin M) = 1) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ),
      MeasureProb (preparedAAState A j) S = 1 → 2 ∣ M →
        ∑ z ∈ Finset.univ.filter (fun z : Fin M => aeEstimate M z = 1),
          (aePaddedLaw M A j S hA hM).prob z = 1) ∧

    (∀ (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (hM : 2 ≤ M)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) (hk : 2 ≤ k),
      M % 2 = 1 →
        ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
            |aeEstimate M z - MeasureProb (preparedAAState A j) S| ≤
              2*Real.pi*(k : ℝ)*Real.sqrt (MeasureProb (preparedAAState A j) S*
                (1-MeasureProb (preparedAAState A j) S))/(M : ℝ) +
                (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
          (aePaddedLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1))) ∧

    (∀ (N M : ℕ) (S : Finset (Fin N)) (hN : 0 < N) (hM : 2 ≤ M) (k : ℕ) (hk : 2 ≤ k),
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| ≤
            2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ) +
              Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2),
        (aePaddedLaw M (QFTMatrix N) (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z >
          1 - 1 / (2 * ((k : ℝ) - 1)) ∧
      QueryCount (aePaddedAECircuit (I := Fin N) M (QFTMatrix N) ⟨0, hN⟩) = M ∧
      GateCount (aePaddedAECircuit (I := Fin N) M (QFTMatrix N) ⟨0, hN⟩) = 5 * (M - 1) + 3) ∧

    (∀ (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin 1)),
      (S.card = 0 ∨ S.card = 1) ∧
      (∀ k : ℕ, 2 ≤ k →
        ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
            |(1 : ℝ)*aeEstimate M z - (S.card : ℝ)| ≤
              2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((1 : ℝ)-S.card))/(M : ℝ) +
                Real.pi^2*(k : ℝ)^2*(1 : ℝ)/(M : ℝ)^2),
          (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
            (qftMatrix_unitary (by norm_num)) hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1))) ∧
      (S.card = 0 →
        (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
          (qftMatrix_unitary (by norm_num)) hM).prob (⟨0, by omega⟩ : Fin M) = 1) ∧
      (S.card = 1 → 2 ∣ M → ∀ k : ℕ, 1 ≤ k →
        ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
            |(1 : ℝ)*aeEstimate M z - (1 : ℝ)| ≤
              2*Real.pi*(k : ℝ)*Real.sqrt ((1 : ℝ)*((1 : ℝ)-(1 : ℝ)))/(M : ℝ) +
                Real.pi^2*(k : ℝ)^2*(1 : ℝ)/(M : ℝ)^2),
          (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
            (qftMatrix_unitary (by norm_num)) hM).prob z = 1) ∧
      (MeasureProb (preparedAAState (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1)) S =
          (S.card : ℝ) ∧
        ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
            |aeEstimate M z - (S.card : ℝ)| ≤
              2*Real.pi*Real.sqrt ((S.card : ℝ)*((1 : ℝ)-(S.card : ℝ)))/(M : ℝ) +
                Real.pi^2/(M : ℝ)^2),
          (aePaddedLaw M (QFTMatrix 1) (⟨0, by norm_num⟩ : Fin 1) S
            (qftMatrix_unitary (by norm_num)) hM).prob z ≥ 8/Real.pi^2)) := by
  refine ⟨fun M A j S hM hA => ae_padded_output_state_eq M A j S hM hA,
    fun M A j S hM hA z => aePaddedLaw_prob M A j S hA hM z,
    fun M hM A j => padded_query_exact_M M hM A j,
    fun M A j S hM hA k hk => padded_k2_window_strict M A j S hM hA k hk,
    fun M A j S hM hA => padded_k1_window_eight_pi_sq M A j S hM hA,
    fun M A j S hM hA ha => padded_endpoint_zero M A j S hM hA ha,
    fun M A j S hM hA ha hdiv => padded_endpoint_one_even M A j S hM hA hdiv ha,
    fun M A j S hM hA k hk hodd => padded_odd_M_window_strict M A j S hM hA k hk hodd,
    fun N M S hN hM k hk => count_padded_k2_window_strict N M S hN hM k hk,
    fun M hM S => count_n1_boundary M hM S⟩

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AePaddingOutputTransport
