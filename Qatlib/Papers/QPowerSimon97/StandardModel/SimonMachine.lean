/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.StandardModel.SimonMachineDefs
import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionAssembly
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QPowerSimon97.StandardDefs

open Qatlib
open scoped Classical BigOperators ENNReal

lemma pairwise_range : ∀ n : ℕ, (List.range n).Pairwise (· < ·) := by
  intro n
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
      rw [List.range_succ, List.pairwise_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      simp only [List.mem_range] at ha
      omega

lemma find?_first {α : Type} {p : α → Bool} {l : List α} {b : α}
    (h : l.find? p = some b) :
    ∃ as bs, l = as ++ b :: bs ∧ ∀ a ∈ as, p a = false := by
  rw [List.find?_eq_some_iff_append] at h
  obtain ⟨hpb, ⟨as, bs, has, hfa⟩⟩ := h
  refine ⟨as, bs, has, ?_⟩
  intro a ha
  cases ha' : p a with
  | false => rfl
  | true =>
      have hcontra := hfa a ha
      rw [ha'] at hcontra
      simp at hcontra

theorem simonOracleSpend_first {n m : ℕ} (M : SimonOracleMachine n m) (x : BooleanVec n)
    (Tf : ℕ) (h : simonOracleHaltedB M x (simonOracleSpend M x Tf) = true) :
    ∀ j, j < simonOracleSpend M x Tf → j ≤ Tf → simonOracleHaltedB M x j = false := by
  classical
  have hkey : ∀ j, j < simonOracleSpend M x Tf → j ≤ Tf →
      simonOracleHaltedB M x j = false := by
    intro j hj hj'
    by_cases hz : (List.range (Tf + 1)).find? (simonOracleHaltedB M x) = none
    · have hne := hz
      simp only [List.find?_eq_none, Bool.not_eq_true] at hne
      have hmem : j ∈ List.range (Tf + 1) := by
        simp only [List.mem_range]
        omega
      exact hne j hmem
    · obtain ⟨b, hbfind⟩ := Option.ne_none_iff_exists'.mp hz
      have hjb : j < b := by simpa only [simonOracleSpend, hbfind, Option.getD_some] using! hj
      obtain ⟨as, bs, has, hfa⟩ := find?_first hbfind
      have hpair : (List.range (Tf + 1)).Pairwise (· < ·) := pairwise_range _
      rw [has] at hpair
      have happ := List.pairwise_append.mp hpair
      have htail : ∀ c ∈ bs, b < c := by
        obtain ⟨h, -⟩ := List.pairwise_cons.mp happ.2.1
        exact h
      have hjmem : j ∈ as ++ b :: bs := by
        rw [← has]
        simp only [List.mem_range]
        omega
      rcases List.mem_append.mp hjmem with hjas | hjbs
      · exact hfa j hjas
      · rcases List.mem_cons.mp hjbs with hjbc | hjbs'
        · subst hjbc
          omega
        · have hlt := htail j hjbs'
          omega
  intro j hj hj'
  exact hkey j hj hj'

theorem simonOracleSpend_le {n m : ℕ} {f : BooleanVec n → BooleanVec m}
    {M : SimonOracleMachine n m} {Tf : ℕ} (h : SimonOracleRealizes f M Tf)
    (x : BooleanVec n) : simonOracleSpend M x Tf ≤ Tf :=
  (h x).2.2

theorem simonOracleOutput_eq {n m : ℕ} {f : BooleanVec n → BooleanVec m}
    {M : SimonOracleMachine n m} {Tf : ℕ} (h : SimonOracleRealizes f M Tf)
    (x : BooleanVec n) : simonOracleOutput M x (simonOracleSpend M x Tf) = f x :=
  (h x).2.1

theorem simonComparePrefix_spec {m : ℕ} (a b : Reg m) :
    ∀ l : List (Fin m),
      simonComparePrefix a b l = (l.all (fun j => decide (a j = b j)), l.length) := by
  intro l
  induction l with
  | nil => rfl
  | cons j rest ih =>
      simp only [simonComparePrefix, ih]
      apply Prod.ext
      · simp only [List.all]
        exact Bool.and_comm _ _
      · simp only [List.length_cons]

theorem simonCompareCounted_spec {m : ℕ} (a b : Reg m) :
    simonCompareCounted a b = (simonCompare a b, m) := by
  rw [simonCompareCounted, simonComparePrefix_spec, List.length_finRange]
  rfl

theorem simonAttemptDecoder_le {n : ℕ} (xs : SimonRetryRecord n) :
    (decodeSimonWithCost (simonRecordBits xs)).2 ≤ simonBlockOpsBound n := by
  rw [simonBlockOpsBound]
  exact (boolean_gaussian_actual_operation_bound (simonRecordBits xs)).2.1

theorem simonAttemptSerialize_eq {n : ℕ} (xs : SimonRetryRecord n) :
    simonSerializeSteps (simonRecordBits xs) = (n + 1) * n := by
  simp [simonSerializeSteps]

theorem simonAttemptBitCost_le {n m : ℕ} {f : BooleanVec n → BooleanVec m}
    {M : SimonOracleMachine n m} {Tf : ℕ} (h : SimonOracleRealizes f M Tf)
    (xs : SimonRetryRecord n) :
    simonAttemptBitCost M Tf xs ≤ 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n := by
  have hser := simonAttemptSerialize_eq xs
  have hdec := simonAttemptDecoder_le xs
  have hsp (q : BooleanVec n) : simonOracleSpend M q Tf ≤ Tf := simonOracleSpend_le h q
  have hlocal : simonAttemptLocalWork xs
      = (n + 1) * n + (decodeSimonWithCost (simonRecordBits xs)).2 := by
    simp only [simonAttemptLocalWork, hser]
  have hser' : (n + 1) * n + (decodeSimonWithCost (simonRecordBits xs)).2
      ≤ (n + 1) * n + simonBlockOpsBound n := Nat.add_le_add_left hdec _
  have hroom : (n + 1) * n + simonBlockOpsBound n
      ≤ 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n := by
    have hA : (n + 1) * n ≤ 2 * Tf + m + (n + 1) * n := by
      calc
        (n + 1) * n ≤ (n + 1) * n + (2 * Tf + m) := Nat.le_add_right _ _
        _ = 2 * Tf + m + (n + 1) * n := Nat.add_comm _ _
        _ ≤ 2 * Tf + m + (n + 1) * n := Nat.le_refl _
    have hB := Nat.add_le_add_right hA (simonBlockOpsBound n)
    simpa [Nat.add_assoc] using! hB
  unfold simonAttemptBitCost simonAttemptCandidate
  cases hc : decodeSimonSecret (simonRecordBits xs) with
  | none =>
      rw [hlocal]
      exact Nat.le_trans hser' hroom
  | some t =>
      rw [hlocal]
      have h1 := hsp (regBooleanEquiv n t)
      have h2 := hsp 0
      have h3 : simonOracleSpend M (regBooleanEquiv n t) Tf + simonOracleSpend M 0 Tf
          ≤ Tf + Tf := by
        have hA := Nat.add_le_add_right h1 (simonOracleSpend M 0 Tf)
        have hB0 : simonOracleSpend M 0 Tf ≤ Tf := h2
        have hB := Nat.add_le_add_right hB0 Tf
        have hB' : simonOracleSpend M 0 Tf + Tf = Tf + simonOracleSpend M 0 Tf := Nat.add_comm _ _
        rw [hB'] at hB
        exact hA.trans hB
      have h5 : (n + 1) * n + (decodeSimonWithCost (simonRecordBits xs)).2
            + simonOracleSpend M (regBooleanEquiv n t) Tf + simonOracleSpend M 0 Tf + m
          ≤ (n + 1) * n + simonBlockOpsBound n + Tf + Tf + m := by
        calc
          (n + 1) * n + (decodeSimonWithCost (simonRecordBits xs)).2
              + simonOracleSpend M (regBooleanEquiv n t) Tf + simonOracleSpend M 0 Tf + m
              ≤ (n + 1) * n + simonBlockOpsBound n
                  + simonOracleSpend M (regBooleanEquiv n t) Tf + simonOracleSpend M 0 Tf + m :=
            by
              have hstep := Nat.add_le_add_right hser'
                (simonOracleSpend M (regBooleanEquiv n t) Tf + simonOracleSpend M 0 Tf + m)
              simpa [Nat.add_assoc] using! hstep
          _ ≤ (n + 1) * n + simonBlockOpsBound n + Tf + Tf + m := by
            have := Nat.add_le_add_right h3 m
            simpa [Nat.add_assoc] using! this
      have hfinal : (n + 1) * n + simonBlockOpsBound n + Tf + Tf + m
          = 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n := by
        rw [Nat.two_mul]
        ac_rfl
      rw [← hfinal]
      exact h5

theorem simonHistoryBitCost_le {n m : ℕ} {f : BooleanVec n → BooleanVec m}
    {M : SimonOracleMachine n m} {Tf : ℕ} (h : SimonOracleRealizes f M Tf)
    (xs : List (SimonRetryRecord n)) :
    (xs.map (simonAttemptBitCost M Tf)).sum ≤
      xs.length * (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hx := simonAttemptBitCost_le h x
      have hrest := ih
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h1 : simonAttemptBitCost M Tf x + (rest.map (simonAttemptBitCost M Tf)).sum
          ≤ rest.length * (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
            + (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) := by
        have hstep := Nat.add_le_add hx hrest
        have hcomm : (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
            + rest.length * (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
            = rest.length * (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
              + (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) := Nat.add_comm _ _
        rw [hcomm] at hstep
        exact hstep
      have hsl : (rest.length + 1) * (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
          = rest.length * (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
            + (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) := by
        rw [Nat.succ_mul]
      rw [hsl]
      exact h1

theorem simonHistoryUnifiedCost_le {n m : ℕ} {f : BooleanVec n → BooleanVec m}
    {M : SimonOracleMachine n m} {Tf : ℕ} (h : SimonOracleRealizes f M Tf)
    (xs : List (SimonRetryRecord n)) :
    (xs.map (simonAttemptUnifiedCost M Tf)).sum ≤
      xs.length * (simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
        + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hx := simonAttemptBitCost_le h x
      have hrest := ih
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hstep : simonAttemptUnifiedCost M Tf x
            + (rest.map (simonAttemptUnifiedCost M Tf)).sum
          ≤ (simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
              + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
            + rest.length * (simonAttemptQuantumSteps (n := n).1
              + simonAttemptQuantumSteps (n := n).2.1
              + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) := by
        have h1 : simonAttemptUnifiedCost M Tf x
            ≤ simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
              + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n := by
          simp only [simonAttemptUnifiedCost]
          have hq : simonAttemptQuantumSteps (n := n).1 ≤ simonAttemptQuantumSteps (n := n).1 :=
            le_refl _
          have hg : simonAttemptQuantumSteps (n := n).2.1 ≤ simonAttemptQuantumSteps (n := n).2.1 :=
            le_refl _
          have hsum := Nat.add_le_add (Nat.add_le_add hq hg) hx
          omega
        exact Nat.add_le_add h1 hrest
      have hcomm : (simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
              + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
            + rest.length * (simonAttemptQuantumSteps (n := n).1
              + simonAttemptQuantumSteps (n := n).2.1
              + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
            = rest.length * (simonAttemptQuantumSteps (n := n).1
              + simonAttemptQuantumSteps (n := n).2.1
              + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
              + (simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
                + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) := Nat.add_comm _ _
      rw [hcomm] at hstep
      have hsl : (rest.length + 1)
            * (simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
              + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
          = rest.length * (simonAttemptQuantumSteps (n := n).1
              + simonAttemptQuantumSteps (n := n).2.1
              + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)
            + (simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
              + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) := by
        rw [Nat.succ_mul]
      rw [hsl]
      exact hstep

theorem simon_verified_path_expected_attempts {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (s : Reg n) (hf : BooleanSimonPromise f (regBooleanEquiv n s)) (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
        (fun hh => (hh.2.length : ℝ≥0∞)) ≤ 2 := by
  classical
  have htime := (simon_verified_unbounded_expected_queries_and_cutoff n (BooleanVec m) f s hf).2.1
  have hround : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
        (fun hh => (hh.2.length : ℝ≥0∞)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) := by
    rw [← simon_verified_history_coupling, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    rfl
  have hfinite : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) ≤ 2 := by
    rw [(general_unbounded_actual_expected_time Unit (Reg n)
      (simonVerifiedRetryKernel f) (Sum.inr ())).2.2 T]
    exact (ENNReal.sum_le_tsum (Finset.range T)).trans htime
  rw [hround]
  exact hfinite

theorem simon_verified_path_expected_bit_time {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (s : Reg n) (hf : BooleanSimonPromise f (regBooleanEquiv n s))
    (M : SimonOracleMachine n m) (Tf : ℕ) (T : ℕ)
    (h : SimonOracleRealizes f M Tf) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (PMF.map (fun hh => (hh.1, simonHistoryBitCost M Tf hh)) (simonVerifiedHistory f T))
      ≤ 2 * (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) := by
  classical
  have hround : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
        (fun hh => (hh.2.length : ℝ≥0∞)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) := by
    rw [← simon_verified_history_coupling, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    rfl
  have hfinite : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) ≤ 2 := by
    rw [(general_unbounded_actual_expected_time Unit (Reg n)
      (simonVerifiedRetryKernel f) (Sum.inr ())).2.2 T]
    exact (ENNReal.sum_le_tsum (Finset.range T)).trans
      ((simon_verified_unbounded_expected_queries_and_cutoff n (BooleanVec m) f s hf).2.1)
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
        (fun hh => ((2 * Tf + m + (n + 1) * n + simonBlockOpsBound n : ℕ) * (hh.2.length : ℝ≥0∞))) := by
      apply ENNReal.tsum_le_tsum
      intro hh
      apply mul_le_mul_right
      change (simonHistoryBitCost M Tf hh : ℝ≥0∞) ≤
        ((2 * Tf + m + (n + 1) * n + simonBlockOpsBound n : ℕ) : ℝ≥0∞) * (hh.2.length : ℝ≥0∞)
      rw [← Nat.cast_mul]
      exact_mod_cast (by
        rw [simonHistoryBitCost]
        have hle := simonHistoryBitCost_le h hh.2
        rwa [Nat.mul_comm] at hle)
    _ = ((2 * Tf + m + (n + 1) * n + simonBlockOpsBound n : ℕ) : ℝ≥0∞) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
          (fun hh => (hh.2.length : ℝ≥0∞)) := by
      unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro hh
      (try dsimp only)
      ac_rfl
    _ ≤ ((2 * Tf + m + (n + 1) * n + simonBlockOpsBound n : ℕ) : ℝ≥0∞) * 2 :=
      mul_le_mul_right (hround ▸ hfinite) _
    _ = _ := by push_cast; rw [mul_comm]

theorem simon_verified_path_expected_quantum_queries {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (s : Reg n) (hf : BooleanSimonPromise f (regBooleanEquiv n s)) (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (PMF.map (fun hh => (hh.1, (simonHistoryQuantumSteps hh).1)) (simonVerifiedHistory f T))
      ≤ 2 * simonAttemptQuantumSteps (n := n).1 := by
  classical
  have hround : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
        (fun hh => (hh.2.length : ℝ≥0∞)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) := by
    rw [← simon_verified_history_coupling, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    rfl
  have hfinite : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) ≤ 2 := by
    rw [(general_unbounded_actual_expected_time Unit (Reg n)
      (simonVerifiedRetryKernel f) (Sum.inr ())).2.2 T]
    exact (ENNReal.sum_le_tsum (Finset.range T)).trans
      ((simon_verified_unbounded_expected_queries_and_cutoff n (BooleanVec m) f s hf).2.1)
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
        (fun hh => (simonAttemptQuantumSteps (n := n).1 : ℝ≥0∞) * (hh.2.length : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro hh
      apply mul_le_mul_right
      change ((simonHistoryQuantumSteps hh).1 : ℝ≥0∞) ≤
        (simonAttemptQuantumSteps (n := n).1 : ℝ≥0∞) * (hh.2.length : ℝ≥0∞)
      simp only [simonHistoryQuantumSteps]
      have h1 : ((hh.2.length * simonAttemptQuantumSteps (n := n).1 : ℕ) : ℝ≥0∞)
          = ((↑hh.2.length : ℝ≥0∞) * (↑(simonAttemptQuantumSteps (n := n).1) : ℝ≥0∞)) := by
        rw [Nat.cast_mul]
      rw [h1]
      exact le_of_eq (by ac_rfl)
    _ = (simonAttemptQuantumSteps (n := n).1 : ℝ≥0∞) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
          (fun hh => (hh.2.length : ℝ≥0∞)) := by
      unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro hh
      (try dsimp only)
      ac_rfl
    _ ≤ (simonAttemptQuantumSteps (n := n).1 : ℝ≥0∞) * 2 :=
      mul_le_mul_right (hround ▸ hfinite) _
    _ = _ := by push_cast; rw [mul_comm]

theorem simon_verified_path_expected_unified_cost {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (s : Reg n) (hf : BooleanSimonPromise f (regBooleanEquiv n s))
    (M : SimonOracleMachine n m) (Tf : ℕ) (T : ℕ)
    (h : SimonOracleRealizes f M Tf) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (PMF.map (fun hh => (hh.1, simonHistoryUnifiedCost M Tf hh)) (simonVerifiedHistory f T))
      ≤ simonStandardModelG n m Tf := by
  classical
  have hquantum :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
          (PMF.map (fun hh => (hh.1, (simonHistoryQuantumSteps hh).1)) (simonVerifiedHistory f T))
        ≤ 2 * simonAttemptQuantumSteps (n := n).1 :=
    simon_verified_path_expected_quantum_queries f s hf T
  have hbit :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
          (PMF.map (fun hh => (hh.1, simonHistoryBitCost M Tf hh)) (simonVerifiedHistory f T))
        ≤ 2 * (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) :=
    simon_verified_path_expected_bit_time f s hf M Tf T h
  have hround : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
        (fun hh => (hh.2.length : ℝ≥0∞)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) := by
    rw [← simon_verified_history_coupling, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    rfl
  have hfinite : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) ≤ 2 := by
    rw [(general_unbounded_actual_expected_time Unit (Reg n)
      (simonVerifiedRetryKernel f) (Sum.inr ())).2.2 T]
    exact (ENNReal.sum_le_tsum (Finset.range T)).trans
      ((simon_verified_unbounded_expected_queries_and_cutoff n (BooleanVec m) f s hf).2.1)
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
        (fun hh => ((simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
          + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n : ℕ) * (hh.2.length : ℝ≥0∞))) := by
      apply ENNReal.tsum_le_tsum
      intro hh
      apply mul_le_mul_right
      change (simonHistoryUnifiedCost M Tf hh : ℝ≥0∞) ≤
        ((simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
          + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n : ℕ) : ℝ≥0∞) * (hh.2.length : ℝ≥0∞)
      rw [← Nat.cast_mul]
      exact_mod_cast (by
        rw [simonHistoryUnifiedCost]
        have hle := simonHistoryUnifiedCost_le h hh.2
        rwa [Nat.mul_comm] at hle)
    _ = ((simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
          + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n : ℕ) : ℝ≥0∞) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
          (fun hh => (hh.2.length : ℝ≥0∞)) := by
      unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro hh
      (try dsimp only)
      ac_rfl
    _ ≤ ((simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
          + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n : ℕ) : ℝ≥0∞) * 2 :=
      mul_le_mul_right (hround ▸ hfinite) _
    _ = _ := by
      unfold simonStandardModelG
      push_cast
      rw [mul_comm]

theorem simon_amplified_bit_cost_le {n : ℕ} (k r : ℕ) (M : SimonOracleMachine n n)
    (Tf : ℕ) (f : BooleanVec n → BooleanVec n) (h : SimonOracleRealizes f M Tf) :
    ∀ rs : Fin r → (Fin (n + k) → AddChar (BooleanVec n) ℂ),
      simonAmplifiedBitCost M Tf rs
        ≤ r * ((n + k) * n + simonEliminationBound n (n + k) + 2 * Tf + n) := by
  classical
  have hrun : ∀ (rows : Fin (n + k) → AddChar (BooleanVec n) ℂ),
      simonAmplifiedRunCost M Tf rows
        ≤ (n + k) * n + simonEliminationBound n (n + k) + 2 * Tf + n := by
    intro rows
    have hser : simonSerializeSteps (simonRecordBits rows) = (n + k) * n := by
      simp [simonSerializeSteps]
    have hdec : (decodeSimonWithCost (simonRecordBits rows)).2
        ≤ simonEliminationBound n (n + k) := by
      rw [simonEliminationBound]
      exact (boolean_gaussian_actual_operation_bound (simonRecordBits rows)).2.1
    have hsp (q : BooleanVec n) : simonOracleSpend M q Tf ≤ Tf := simonOracleSpend_le h q
    have hcore : (n + k) * n + (decodeSimonWithCost (simonRecordBits rows)).2
        ≤ (n + k) * n + simonEliminationBound n (n + k) :=
      Nat.add_le_add_left hdec _
    unfold simonAmplifiedRunCost
    by_cases hc : decodeSimonSecret (simonRecordBits rows) = none
    · rw [hc, hser]
      have hstep := Nat.le_trans hcore
        (Nat.le_add_right ((n + k) * n + simonEliminationBound n (n + k)) (2 * Tf + n))
      simpa [Nat.add_assoc] using! hstep
    · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hc
      simp only [ht, hser]
      have h1 := hsp (regBooleanEquiv n t)
      have h2 := hsp 0
      have h3 : simonOracleSpend M (regBooleanEquiv n t) Tf + simonOracleSpend M 0 Tf
          ≤ Tf + Tf := by
        have hA := Nat.add_le_add_right h1 (simonOracleSpend M 0 Tf)
        have hB0 : simonOracleSpend M 0 Tf ≤ Tf := h2
        have hB := Nat.add_le_add_right hB0 Tf
        have hB' : simonOracleSpend M 0 Tf + Tf = Tf + simonOracleSpend M 0 Tf :=
          Nat.add_comm _ _
        rw [hB'] at hB
        exact hA.trans hB
      have hstep : (n + k) * n + (decodeSimonWithCost (simonRecordBits rows)).2
            + (simonOracleSpend M (regBooleanEquiv n t) Tf + simonOracleSpend M 0 Tf + n)
          ≤ (n + k) * n + simonEliminationBound n (n + k) + Tf + Tf + n := by
        have hA := Nat.add_le_add_right hcore
          (simonOracleSpend M (regBooleanEquiv n t) Tf + simonOracleSpend M 0 Tf + n)
        have hB := Nat.add_le_add_right h3 n
        have hB' := Nat.add_le_add_left hB
          ((n + k) * n + simonEliminationBound n (n + k))
        simpa [Nat.add_assoc] using! hA.trans hB'
      have hfinal : (n + k) * n + simonEliminationBound n (n + k) + 2 * Tf + n
          = (n + k) * n + simonEliminationBound n (n + k) + Tf + Tf + n := by
        rw [Nat.two_mul]
        ac_rfl
      rw [hfinal]
      simpa [Nat.add_assoc] using! hstep
  intro rs
  unfold simonAmplifiedBitCost
  calc
    (Finset.univ : Finset (Fin r)).sum (fun i => simonAmplifiedRunCost M Tf (rs i))
        ≤ (Finset.univ : Finset (Fin r)).sum
            (fun _ => (n + k) * n + simonEliminationBound n (n + k) + 2 * Tf + n) :=
      Finset.sum_le_sum fun i _ => hrun (rs i)
    _ = r * ((n + k) * n + simonEliminationBound n (n + k) + 2 * Tf + n) := by
      simp [Finset.sum_const, Finset.card_univ]

theorem simon_sequential_peak_space {n : ℕ} (f : BooleanVec n → BooleanVec n) (m r : ℕ) :
    (simonSequentialAmplified f m r).2 = if r = 0 then 0 else 1 := by
  have haux : ∀ (i : ℕ), (simonSequentialAmplifiedAux f m i).2 = if i = 0 then 0 else 1 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
        rw [simonSequentialAmplifiedAux]
        simp only [max_eq_left, ih]
        by_cases hi : i = 0
        · simp [hi]
        · simp [hi]
  rw [simonSequentialAmplified]
  exact haux r

theorem clause4_endpoint : Clause4StandardModelBridge := by
  intro n m f s hf M Tf h T
  exact ⟨simon_verified_path_expected_attempts f s hf T,
    simon_verified_path_expected_bit_time f s hf M Tf T h,
    simon_verified_path_expected_quantum_queries f s hf T,
    simon_verified_path_expected_unified_cost f s hf M Tf T h⟩

theorem clause5_endpoint : Clause5MachineSeparation := by
  refine ⟨clause5_complete.1, ?_, ?_, ?_⟩
  · intro n k r M Tf f h
    exact simon_amplified_bit_cost_le k r M Tf f h
  · intro n m r f
    exact simon_sequential_peak_space f m r
  · trivial

end Qatlib.Papers.QPowerSimon97.StandardDefs
