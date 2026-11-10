/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.StandardModel.SimonRetryDefs
import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionAssembly
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Concepts.PauliClifford.ExactRank

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QPowerSimon97.StandardDefs

open Qatlib
open Qatlib.Papers.QPowerSimon97.StandardDefs
open scoped Classical BigOperators ENNReal

theorem simonLocalExperiment_length (n : ℕ) :
    (simonLocalExperiment n).length = 2 * n := by
  simp [simonLocalExperiment, localHadamard_length]
  omega

theorem simonLocalExperiment_matrix (n : ℕ) :
    localProgramMatrix (simonLocalExperiment n) = HadamardN n * HadamardN n := by
  rw [simonLocalExperiment, localProgramMatrix_append, localProgramMatrix_localHadamard]

theorem simonLocalBlock_length (n m : ℕ) :
    (simonLocalBlock n m).length = 2 * n * m := by
  induction m with
  | zero =>
      simp [simonLocalBlock]
  | succ m ih =>
      have h : simonLocalBlock n (m + 1)
          = simonLocalExperiment n ++ simonLocalBlock n m := by
        simp [simonLocalBlock, List.flatten_cons, List.replicate_succ]
      rw [h, List.length_append, ih, simonLocalExperiment_length]
      ring

theorem simonLocalDecision_length (n m r : ℕ) :
    (simonLocalDecision n m r).length = 2 * n * m * r := by
  induction r with
  | zero =>
      simp [simonLocalDecision]
  | succ r ih =>
      have h : simonLocalDecision n m (r + 1)
          = simonLocalBlock n m ++ simonLocalDecision n m r := by
        simp [simonLocalDecision, List.flatten_cons, List.replicate_succ]
      rw [h, List.length_append, ih, simonLocalBlock_length]
      ring

theorem simonRecordConversionCost_eq {n m : ℕ} (rows : Fin m → Reg n) :
    simonRecordConversionCost rows = m * n := by
  simp [simonRecordConversionCost, simonSerializeSteps]

theorem simonExactLedger_eq (n k r : ℕ) :
    (simonLocalDecision n (n + k) r).length = (simonExactLedger n k r).localGates ∧
    (simonExactLedger n k r).oracleQueries = (n + k) * r ∧
    (simonExactLedger n k r).measurements = (n + k) * r ∧
    (simonExactLedger n k r).recordConversion = (n + k) * n * r :=
  ⟨simonLocalDecision_length n (n + k) r, rfl, rfl, rfl⟩

theorem simonAmplifiedError_spec (n k r : ℕ) {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (h2 : 2 ≤ n + k) :
    (Function.Injective f →
      (simonAmplifiedReject f (n + k) r) true ≤ (simonAmplifiedError n k r).falseReject) ∧
    (∀ s : BooleanVec n, s ≠ 0 →
      Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n →
        (simonAmplifiedReject f (n + k) r) false ≤ (simonAmplifiedError n k r).falseAccept) := by
  have h := simonNegligibleErrorAmplification n R f k r h2
  refine ⟨fun hf => ?_, fun s hs hcard => ?_⟩
  · simpa [simonAmplifiedError] using! h.1 hf
  · simpa [simonAmplifiedError] using! h.2.1 s hs hcard

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h1 : n + 1 ≤ 2 ^ n + 1 := by omega
      have h2 : 2 ^ n + 1 ≤ 2 ^ n * 2 := by
        have h3 : (1 : ℕ) ≤ 2 ^ n := by
          have h4 := pow_le_pow_right' (a := (2 : ℕ)) (by norm_num) (Nat.zero_le n)
          simpa using! h4
        omega
      rw [pow_succ]
      omega

private theorem sq_le_two_pow_four (n : ℕ) : (n : ℝ)^2 ≤ (2 : ℝ)^(4 * n) := by
  have h1 : n ^ 2 ≤ 2 ^ n * 2 ^ n := by
    simpa [Nat.pow_two] using! Nat.mul_le_mul (nat_le_two_pow n) (nat_le_two_pow n)
  have h2 : 2 ^ n * 2 ^ n = 2 ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  have h3 : ((n : ℝ)^2 : ℝ) ≤ ((2 : ℝ)^(2 * n) : ℝ) := by
    exact_mod_cast (h1.trans_eq h2)
  have h4 : ((2 : ℝ)^(2 * n) : ℝ) ≤ ((2 : ℝ)^(4 * n) : ℝ) := by
    exact_mod_cast (pow_le_pow_right' (by norm_num) (by omega))
  linarith

private theorem pow_sub_real {a : ℝ} (ha : 0 < a) {m k : ℕ} (h : k ≤ m) :
    a ^ (m - k) = a ^ m / a ^ k := by
  have hp : a ^ (m - k) * a ^ k = a ^ m := by
    rw [← pow_add, Nat.sub_add_cancel h]
  have hne : a ^ k ≠ 0 := by positivity
  rw [eq_div_iff hne]
  exact hp

theorem simonCompletingFalseReject_negligible :
    simonNegligible simonCompletingFalseReject := by
  intro c hc
  refine ⟨c + 4, fun n hn => ?_⟩
  have h1 : 4 * n ≤ n * n - c * n := by
    have h2 : 4 ≤ n - c := by omega
    have h3 : 4 * n ≤ (n - c) * n := Nat.mul_le_mul_right n h2
    have h4 : (n - c) * n = n * n - c * n := Nat.sub_mul n c n
    omega
  have hge : (n : ℝ)^2 ≤ (2 : ℝ)^(n * n - c * n) := by
    have h2 : ((2 : ℝ)^(4 * n) : ℝ) ≤ ((2 : ℝ)^(n * n - c * n) : ℝ) := by
      exact_mod_cast (pow_le_pow_right' (by norm_num) h1)
    have h3 : ((n : ℝ)^2 : ℝ) ≤ ((2 : ℝ)^(4 * n) : ℝ) := sq_le_two_pow_four n
    linarith
  have hpos : (0 : ℝ) < (2 : ℝ)^(n * n) := by positivity
  have hmain : (n : ℝ)^2 * (1 / 2 : ℝ)^(n * n) ≤ (1 / 2 : ℝ)^(c * n) := by
    have hA : (1 / 2 : ℝ)^(n * n) = 1 / (2 : ℝ)^(n * n) := one_div_pow _ _
    have hB : (1 / 2 : ℝ)^(c * n) = 1 / (2 : ℝ)^(c * n) := one_div_pow _ _
    have hC : (n : ℝ)^2 * (1 / (2 : ℝ)^(n * n)) = (n : ℝ)^2 / (2 : ℝ)^(n * n) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
    rw [hA, hB, hC]
    rw [div_le_iff₀ hpos]
    have h6 : ((1 / 2 ^ (c * n) : ℝ)) * (2 : ℝ)^(n * n) = (2 : ℝ)^(n * n - c * n) := by
      calc
        ((1 / 2 ^ (c * n) : ℝ)) * (2 : ℝ)^(n * n)
            = (2 : ℝ)^(n * n) * ((2 : ℝ)^(c * n))⁻¹ := by
          rw [div_eq_mul_inv, one_mul, mul_comm]
        _ = (2 : ℝ)^(n * n) / (2 : ℝ)^(c * n) := by rw [div_eq_mul_inv]
        _ = (2 : ℝ)^(n * n - c * n) :=
          (pow_sub_real (a := (2 : ℝ)) (m := n * n) (k := c * n) (by norm_num) (by omega)).symm
    rw [h6]
    exact hge
  have h8 : simonCompletingFalseReject n = (n : ℝ)^2 * (1 / 2 : ℝ)^(n * n) := rfl
  rw [h8]
  exact hmain

theorem simonCompletingFalseAccept_negligible :
    simonNegligible simonCompletingFalseAccept := by
  intro c hc
  refine ⟨3 * c, fun n hn => ?_⟩
  have hbase : (3 / 4 : ℝ)^3 ≤ (1 / 2 : ℝ) := by norm_num
  have h3c : 3 * c ≤ n := by omega
  have hmain : (3 / 4 : ℝ)^(n * n) ≤ (1 / 2 : ℝ)^(c * n) := by
    have h1 : (3 / 4 : ℝ)^(n * n) = ((3 / 4 : ℝ)^n)^n := by rw [← pow_mul]
    have h2 : (3 / 4 : ℝ)^n ≤ (3 / 4 : ℝ)^(3 * c) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h3c
    have h3 : ((3 / 4 : ℝ)^n : ℝ)^n ≤ ((3 / 4 : ℝ)^(3 * c) : ℝ)^n :=
      pow_le_pow_left₀ (by positivity) h2 n
    have h4 : ((3 / 4 : ℝ)^(3 * c) : ℝ)^n = (3 / 4 : ℝ)^(3 * c * n) := by
      rw [← pow_mul]
    have h5 : (3 / 4 : ℝ)^(3 * c * n) = ((3 / 4 : ℝ)^3)^(c * n) := by
      rw [← pow_mul]
      congr 1
      ring
    have h6 : ((3 / 4 : ℝ)^3)^(c * n) ≤ (1 / 2 : ℝ)^(c * n) :=
      pow_le_pow_left₀ (by positivity) hbase (c * n)
    linarith
  have h8 : simonCompletingFalseAccept n = (3 / 4 : ℝ)^(n * n) := rfl
  rw [h8]
  exact hmain

theorem simonPaperFalseReject_le (n : ℕ) (hn : 1 ≤ n) :
    simonPaperFalseReject n ≤ (1 / 2 : ℝ)^n := by
  have h1 : (n : ℝ) ≤ (2 : ℝ)^n := by
    exact_mod_cast nat_le_two_pow n
  have hpos : (0 : ℝ) < (2 : ℝ)^(2 * n) := by positivity
  have hmain : (n : ℝ) * (1 / 2 : ℝ)^(2 * n) ≤ (1 / 2 : ℝ)^n := by
    have hA : (1 / 2 : ℝ)^(2 * n) = 1 / (2 : ℝ)^(2 * n) := one_div_pow _ _
    have hB : (1 / 2 : ℝ)^n = 1 / (2 : ℝ)^n := one_div_pow _ _
    have hC : (n : ℝ) * (1 / (2 : ℝ)^(2 * n)) = (n : ℝ) / (2 : ℝ)^(2 * n) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
    rw [hA, hB, hC]
    rw [div_le_iff₀ hpos]
    have h2 : ((1 / 2 ^ (n) : ℝ)) * (2 : ℝ)^(2 * n) = (2 : ℝ)^n := by
      calc
        ((1 / 2 ^ (n) : ℝ)) * (2 : ℝ)^(2 * n) = (2 : ℝ)^(2 * n) * ((2 : ℝ)^n)⁻¹ := by
          rw [div_eq_mul_inv, one_mul, mul_comm]
        _ = (2 : ℝ)^(2 * n) / (2 : ℝ)^n := by rw [div_eq_mul_inv]
        _ = (2 : ℝ)^n := by
          have hsub : 2 * n - n = n := by omega
          have hp :=
              (pow_sub_real (a := (2 : ℝ)) (m := 2 * n) (k := n) (by norm_num) (by omega)).symm
          rw [hsub] at hp
          exact hp
    rw [h2]
    exact h1
  have h4 : simonPaperFalseReject n = (n : ℝ) * (1 / 2 : ℝ)^(2 * n) := rfl
  rw [h4]
  exact hmain

theorem simonPaperFalseAccept_gt (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ)^n < simonPaperFalseAccept n := by
  have h1 : (1 / 2 : ℝ)^(n - 1) ≤ (3 / 4 : ℝ)^(n - 1) :=
    pow_le_pow_left₀ (by positivity) (by norm_num) (n - 1)
  have h2 : (1 / 2 : ℝ)^n = (1 / 2 : ℝ)^(n - 1) * (1 / 2 : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have h3 : (3 / 4 : ℝ)^n = (3 / 4 : ℝ)^(n - 1) * (3 / 4 : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have h4 : (1 / 2 : ℝ)^(n - 1) * (1 / 2 : ℝ) < (3 / 4 : ℝ)^(n - 1) * (3 / 4 : ℝ) := by
    calc
      (1 / 2 : ℝ)^(n - 1) * (1 / 2 : ℝ) ≤ (3 / 4 : ℝ)^(n - 1) * (1 / 2 : ℝ) := by
        have h5 := mul_le_mul (a := (1 / 2 : ℝ)^(n - 1)) (b := (3 / 4 : ℝ)^(n - 1))
          (c := (1 / 2 : ℝ)) (d := (1 / 2 : ℝ))
          h1 (le_refl _) (by positivity) (by positivity)
        exact h5
      _ < (3 / 4 : ℝ)^(n - 1) * (3 / 4 : ℝ) :=
        mul_lt_mul_of_pos_left (by norm_num) (by positivity)
  have h6 : (1 / 2 : ℝ)^n < (3 / 4 : ℝ)^n := by
    rw [h2, h3]
    exact h4
  have h5 : simonPaperFalseAccept n = (3 / 4 : ℝ)^n := rfl
  rw [h5]
  exact h6

private theorem simonTwoPowCoe (n : ℕ) :
    ((2 ^ n : ℕ) : ENNReal) = (2 ^ n : ENNReal) := by
  have hnat : ((2 ^ n : ℕ) : ENNReal) = ENNReal.ofReal ((2 ^ n : ℕ) : ℝ) :=
    (ENNReal.ofReal_natCast _).symm
  have hreal : ENNReal.ofReal ((2 ^ n : ℕ) : ℝ) = ENNReal.ofReal ((2 : ℝ)^n) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have hpow : ENNReal.ofReal ((2 : ℝ)^n) = (ENNReal.ofReal (2 : ℝ))^n :=
    ENNReal.ofReal_pow (by norm_num) n
  have hnum : (ENNReal.ofReal (2 : ℝ) : ENNReal) = (2 : ENNReal) := by
    rw [← Nat.cast_ofNat (R := ℝ), ENNReal.ofReal_natCast, ← Nat.cast_ofNat (R := ENNReal)]
  rw [hnat, hreal, hpow, hnum]

private theorem simonOfRealHalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  have h1 : ENNReal.ofReal 1 = (1 : ENNReal) := ENNReal.ofReal_one
  have h2 : ENNReal.ofReal 2 = (2 : ENNReal) := by
    rw [← Nat.cast_ofNat (R := ℝ), ENNReal.ofReal_natCast, ← Nat.cast_ofNat (R := ENNReal)]
  rw [h1, h2]

private theorem simonBirthdayTerm_le (n q : ℕ) (h : 8 * q * q ≤ 2 ^ n) :
    ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹ ≤ ENNReal.ofReal (1 / 8) := by
  rw [ENNReal.mul_inv_le_iff (by simp) (by simp)]
  have hnat : 8 * (q * q) ≤ 2 ^ n := by
    have heq : 8 * q * q = 8 * (q * q) := by ring
    omega
  have hreal : (8 * (q * q : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
  have h2 : ((q * q : ℕ) : ℝ) ≤ (1 / 8 : ℝ) * ((2 ^ n : ℕ) : ℝ) := by
    have h3 : ((q * q : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) / 8 :=
      (le_div_iff₀ (by norm_num : (0:ℝ) < (8:ℝ))).2 (by linarith [hreal])
    have h4 : (1 / 8 : ℝ) * ((2 ^ n : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) / 8 := by
      rw [one_div_mul_eq_div]
    linarith
  have h5 : ((q * q : ℕ) : ENNReal) = ENNReal.ofReal ((q * q : ℕ) : ℝ) :=
    (ENNReal.ofReal_natCast _).symm
  have h6 : (2 ^ n : ENNReal) = ENNReal.ofReal ((2 ^ n : ℕ) : ℝ) :=
    (simonTwoPowCoe n).symm.trans (ENNReal.ofReal_natCast _).symm
  have h7 : ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal ((2 ^ n : ℕ) : ℝ)
      = ENNReal.ofReal ((1 / 8 : ℝ) * ((2 ^ n : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
  have h8 : ((q * q : ℕ) : ℝ) ≤ (1 / 8 : ℝ) * ((2 ^ n : ℕ) : ℝ) := h2
  have h9 : ENNReal.ofReal ((q * q : ℕ) : ℝ)
      ≤ ENNReal.ofReal ((1 / 8 : ℝ) * ((2 ^ n : ℕ) : ℝ)) := ENNReal.ofReal_le_ofReal h8
  rw [h5, h6, h7]
  exact h9

private theorem simonClassicalBound_le (n q : ℕ) (h : 8 * q * q ≤ 2 ^ n) :
    (1 / 2 : ENNReal) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹
      ≤ ENNReal.ofReal (5 / 8) := by
  have hX := simonBirthdayTerm_le n q h
  calc
    (1 / 2 : ENNReal) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹
        ≤ (1 / 2 : ENNReal) + ENNReal.ofReal (1 / 8) := add_le_add_right hX _
    _ = ENNReal.ofReal (5 / 8) := by
      rw [← simonOfRealHalf, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      congr 1
      norm_num

private theorem simonQuantumBound (n k r : ℕ) {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (h2 : 2 ≤ n + k)
    (s : BooleanVec n) (hs : s ≠ 0)
    (hcard : Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n) :
    (simonAmplifiedReject f (n + k) r) true + ENNReal.ofReal ((3 / 4 : ℝ) ^ r) ≥ 1 := by
  have hamp := simonNegligibleErrorAmplification n R f k r h2
  have hnot : (simonAmplifiedReject f (n + k) r) false ≤ ENNReal.ofReal ((3 / 4 : ℝ) ^ r) :=
    hamp.2.1 s hs hcard
  have htot : (simonAmplifiedReject f (n + k) r) true
      + (simonAmplifiedReject f (n + k) r) false = 1 := by
    rw [pmf_bool_true, pmf_bool_false]
    have hpart := event_partition (simonAmplifiedReject f (n + k) r) (fun b => b = true)
    have heq : event (simonAmplifiedReject f (n + k) r) (fun b => ¬ (b = true))
        = event (simonAmplifiedReject f (n + k) r) (fun b => b = false) := by
      unfold event
      apply expectation_congr
      intro x
      by_cases hx : x = true <;> simp [hx]
    rw [heq] at hpart
    exact hpart
  calc
    (simonAmplifiedReject f (n + k) r) true + ENNReal.ofReal ((3 / 4 : ℝ) ^ r)
        ≥ (simonAmplifiedReject f (n + k) r) true
            + (simonAmplifiedReject f (n + k) r) false := add_le_add_right hnot _
    _ = 1 := htot

theorem clause19_separation (n q k r : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) (h2 : 2 ≤ n + k) :
    1 ≤ n ∧ 1 ≤ q ∧ 2 ≤ n + k ∧
    (∀ P : PMF (SimonQueryTree n), SimonQueryTree.bounded P q →
        simonOracleGuessMass P ≤
          (1 / 2 : ENNReal) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹)
    ∧ (∀ f : BooleanVec n → BooleanVec n,
        (∃ s : BooleanVec n, s ≠ 0 ∧ ∀ x : BooleanVec n, f x = f (x + s)) →
          (simonAmplifiedReject f (n + k) r) true + ENNReal.ofReal ((3 / 4 : ℝ) ^ r) ≥ 1)
    ∧ (8 * q * q ≤ 2 ^ n → (3 / 4 : ℝ) ^ r ≤ 1 / 8 →
        ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹ ≤ ENNReal.ofReal (1 / 8) ∧
        (1 / 2 : ENNReal) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹
          ≤ ENNReal.ofReal (5 / 8) ∧
        ENNReal.ofReal (1 / 2) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹
            + ENNReal.ofReal ((3 / 4 : ℝ) ^ r) < 1) := by
  refine ⟨hn, hq, h2, fun P hP => ?_, fun f hf => ?_, fun h1 h3 => ?_⟩
  · exact simonOracleGuessMass_le_birthday hn hq P hP
  · obtain ⟨s, hs, hfs⟩ := hf
    have hcard : Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n := by
      have hempty : {x : BooleanVec n | f x ≠ f (x + s)} = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hx (hfs x)).elim
        · intro hx
          simp at hx
      simp [hempty]
    exact simonQuantumBound n k r f h2 s hs hcard
  · have hX := simonBirthdayTerm_le n q h1
    have hcl : (1 / 2 : ENNReal) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹
        ≤ ENNReal.ofReal (5 / 8) := simonClassicalBound_le n q h1
    have hsum : ENNReal.ofReal (1 / 2)
        + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹ ≤ ENNReal.ofReal (5 / 8) := by
      rw [simonOfRealHalf]
      exact hcl
    have hlast : ENNReal.ofReal (5 / 8) + ENNReal.ofReal ((3 / 4 : ℝ) ^ r) < 1 := by
      have h5 : ENNReal.ofReal ((3 / 4 : ℝ) ^ r) ≤ ENNReal.ofReal (1 / 8) := by
        apply ENNReal.ofReal_le_ofReal
        exact h3
      have h6 : ENNReal.ofReal (5 / 8) + ENNReal.ofReal (1 / 8) = ENNReal.ofReal (3 / 4) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        congr 1
        norm_num
      calc
        ENNReal.ofReal (5 / 8) + ENNReal.ofReal ((3 / 4 : ℝ) ^ r)
            ≤ ENNReal.ofReal (5 / 8) + ENNReal.ofReal (1 / 8) := add_le_add_right h5 _
        _ = ENNReal.ofReal (3 / 4) := h6
        _ < 1 := by
          rw [← ENNReal.ofReal_one]
          rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
          norm_num
    refine ⟨hX, hcl, ?_⟩
    calc
      ENNReal.ofReal (1 / 2) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹
            + ENNReal.ofReal ((3 / 4 : ℝ) ^ r)
          ≤ ENNReal.ofReal (5 / 8) + ENNReal.ofReal ((3 / 4 : ℝ) ^ r) := by
            exact add_le_add_left hsum _
      _ < 1 := hlast

theorem simonBudgetFit : ∀ m : ℕ, 16 ≤ m → 3 * (4 * m) ^ 2 ≤ 2 ^ m := by
  intro m hm
  refine Nat.le_induction (m := 16) (n := m) ?base ?succ hm
  · norm_num
  · intro m h16 ih
    have hstep : 3 * (4 * (m + 1)) ^ 2 ≤ 2 * (3 * (4 * m) ^ 2) := by
      have h1 : (4 * (m + 1) : ℕ) ^ 2 = (4 * m) ^ 2 + 8 * (4 * m) + 16 := by ring
      have h3 : (3 : ℕ) ≤ m := by omega
      have h4 : m * m ≥ 3 * m := Nat.mul_le_mul_right m (by omega)
      rw [h1]
      nlinarith
    calc
      3 * (4 * (m + 1)) ^ 2 ≤ 2 * (3 * (4 * m) ^ 2) := hstep
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

theorem simonBudgetSeparation (n : ℕ) (hn : 64 ≤ n) (h4 : 4 ∣ n) :
    n * (n + 2 * n) ≤ 2 ^ (n / 4) ∧
    8 * (2 ^ (n / 4)) * (2 ^ (n / 4)) ≤ 2 ^ n := by
  obtain ⟨m, rfl⟩ := h4
  have hm : 16 ≤ m := by omega
  have hdiv : (4 * m) / 4 = m := by omega
  have h1 : 3 * (4 * m) ^ 2 ≤ 2 ^ m := simonBudgetFit m hm
  have h2 : (4 * m) * ((4 * m) + 2 * (4 * m)) = 3 * (4 * m) ^ 2 := by ring
  have h3 : 8 * 2 ^ m * 2 ^ m ≤ 2 ^ (4 * m) := by
    have h4' : 3 + m ≤ 4 * m := by omega
    calc
      8 * 2 ^ m * 2 ^ m = (2 ^ 3) * 2 ^ m * 2 ^ m := by norm_num
      _ = 2 ^ (3 + m) * 2 ^ m := by
        rw [show (2 ^ 3) * 2 ^ m = 2 ^ (3 + m) from (pow_add 2 3 m).symm]
      _ = 2 ^ (3 + m + m) := by
        rw [show 2 ^ (3 + m) * 2 ^ m = 2 ^ (3 + m + m) from (pow_add 2 (3 + m) m).symm]
      _ ≤ 2 ^ (4 * m) := pow_le_pow_right' (by norm_num) (by omega)
  constructor
  · rw [hdiv, h2]
    exact h1
  · rw [hdiv]
    simpa [Nat.mul_pow] using! h3

theorem clause18_endpoint : Clause18LocalGateBridge := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨simonLocalExperiment_length n, simonLocalExperiment_matrix n⟩
  · intro n m
    exact simonLocalBlock_length n m
  · intro n m r
    exact simonLocalDecision_length n m r
  · intro n m rows
    exact simonRecordConversionCost_eq rows
  · intro n k r
    exact simonExactLedger_eq n k r

theorem clause19_separation_at_schedule (n : ℕ) (hn : 64 ≤ n) (h4 : 4 ∣ n) :
    Clause19Separation n (2 ^ (n / 4)) (2 * n) n ∧
      n * (n + 2 * n) ≤ 2 ^ (n / 4) ∧
      8 * (2 ^ (n / 4)) * (2 ^ (n / 4)) ≤ 2 ^ n := by
  have hbud := simonBudgetSeparation n hn h4
  have hq : 1 ≤ 2 ^ (n / 4) := by
    have hpos : 0 < n / 4 := Nat.div_pos (by omega) (by omega)
    have h1 := pow_le_pow_right' (a := (2 : ℕ)) (by norm_num) (Nat.zero_le (n / 4))
    simpa using! h1
  refine ⟨clause19_separation n (2 ^ (n / 4)) (2 * n) n (by omega) hq (by omega), hbud.1, hbud.2⟩

theorem clause19_endpoint : Clause19TwoSidedSeparation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k r R _ _ _ f h2 hf
    have h := simonAmplifiedError_spec n k r f h2
    refine ⟨h.1 hf, ?_⟩
    intro s hs hcard
    exact h.2 s hs hcard
  · intro n k r
    exact ⟨rfl, rfl⟩
  · exact ⟨simonCompletingFalseReject_negligible, simonCompletingFalseAccept_negligible⟩
  · intro n hn
    exact simonPaperFalseReject_le n hn
  · intro n hn
    exact simonPaperFalseAccept_gt n hn
  · intro n hn h4
    exact clause19_separation_at_schedule n hn h4

end Qatlib.Papers.QPowerSimon97.StandardDefs
