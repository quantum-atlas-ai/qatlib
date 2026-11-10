/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.StandardModel.SimonRetry
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPowerSimon97.StandardDefs

open Qatlib
open Qatlib.Papers.QPowerSimon97.StandardDefs
open scoped Classical BigOperators ENNReal

theorem simonPaperScheduleLedger (n : ℕ) :
    (simonExactLedger n (2 * n) n).oracleQueries = 3 * n ^ 2 ∧
    (simonExactLedger n (2 * n) n).measurements = 3 * n ^ 2 ∧
    (simonExactLedger n (2 * n) n).localGates = 6 * n ^ 3 ∧
    (simonExactLedger n (2 * n) n).recordConversion = 3 * n ^ 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [simonExactLedger] <;> ring

theorem simonPaperScheduleTwoSided (n : ℕ) (hn : 2 ≤ n + 2 * n) (R : Type)
    [AddCommGroup R] [Fintype R] [DecidableEq R] (f : BooleanVec n → R) :
    (Function.Injective f →
      (simonAmplifiedReject f (n + 2 * n) n) true ≤
        ENNReal.ofReal ((n : ℝ) * (1 / 2 : ℝ) ^ (2 * n))) ∧
    (∀ s : BooleanVec n, s ≠ 0 →
      Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + 2 * n) ≤ 2 ^ n →
        (simonAmplifiedReject f (n + 2 * n) n) false ≤
          ENNReal.ofReal ((3 / 4 : ℝ) ^ n)) := by
  have h := simonAmplifiedError_spec n (2 * n) n f hn
  simpa [simonAmplifiedError] using! h

theorem simonThirdToleranceAmplification (n : ℕ) (hn : 1 ≤ n) (R : Type)
    [AddCommGroup R] [Fintype R] [DecidableEq R] (f : BooleanVec n → R) :
    (Function.Injective f →
      (simonAmplifiedReject f (n + 2 * n) n) true ≤
        ENNReal.ofReal ((n : ℝ) * (1 / 2 : ℝ) ^ (2 * n))) ∧
    (∀ s : BooleanVec n, s ≠ 0 →
      (Nat.card {x : BooleanVec n | f x ≠ f (x + s)} : ℝ) ≤
        (2 : ℝ) ^ n / (3 * (n : ℝ)) →
        (simonAmplifiedReject f (n + 2 * n) n) false ≤
          ENNReal.ofReal ((3 / 4 : ℝ) ^ n)) ∧
    (simonExactLedger n (2 * n) n).oracleQueries = 3 * n ^ 2 := by
  have h := simonPaperScheduleTwoSided n (by omega) R f
  refine ⟨h.1, ?_, (simonPaperScheduleLedger n).1⟩
  intro s hs hbad
  apply h.2 s hs
  have hpos : (0 : ℝ) < 3 * (n : ℝ) := by positivity
  have hb := (le_div_iff₀ hpos).mp hbad
  have hn' : (Nat.card {x : BooleanVec n | f x ≠ f (x + s)} : ℝ) *
      ((n + 2 * n : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    push_cast
    nlinarith
  exact_mod_cast hn'

theorem simonTheorem33RealBudget (n : ℕ) (hn : 1 ≤ n) (q : ℕ)
    (hq : (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4)) (P : PMF (SimonQueryTree n))
    (hP : SimonQueryTree.bounded P q) :
    simonOracleGuessMass P ≤ ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) :=
  simonClassicalRandomOracleBound_realBudget n hn q P hP hq

lemma simonExponentHalf_le (n : ℕ) (hn : 64 ≤ n) :
    (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ 1 / 8 := by
  have hn' : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp : -(n : ℝ) / 2 ≤ (-3 : ℝ) := by linarith
  have hmono : (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ (2 : ℝ) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hval : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by
    rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg (by norm_num)]
    norm_num [Real.rpow_natCast]
  linarith

lemma simonThreeQuarters_pow_le (n : ℕ) (hn : 64 ≤ n) :
    (3 / 4 : ℝ) ^ n ≤ 1 / 8 := by
  have hmono : (3 / 4 : ℝ) ^ n ≤ (3 / 4 : ℝ) ^ 10 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h10 : (3 / 4 : ℝ) ^ 10 ≤ 1 / 8 := by norm_num
  linarith

theorem simonSeparationGap (n : ℕ) (hn : 64 ≤ n) :
    ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) +
      ENNReal.ofReal ((3 / 4 : ℝ) ^ n) < 1 := by
  have hx := simonExponentHalf_le n hn
  have hy := simonThreeQuarters_pow_le n hn
  have hsum : (1 / 2 : ℝ) + (2 : ℝ) ^ (-(n : ℝ) / 2) + (3 / 4 : ℝ) ^ n < 1 := by
    linarith
  have hx0 : (0 : ℝ) ≤ 1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2) := by
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-(n : ℝ) / 2)
    linarith
  have hy0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ n := by positivity
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hx0 hy0]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hsum

theorem simonTheorem34Separation (n : ℕ) (hn : 64 ≤ n) (q : ℕ)
    (hq : (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4)) (P : PMF (SimonQueryTree n))
    (hP : SimonQueryTree.bounded P q) (R : Type) [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (s : BooleanVec n) (hs : s ≠ 0)
    (hf : ∀ x : BooleanVec n, f x = f (x + s)) :
    simonOracleGuessMass P < (simonAmplifiedReject f (n + 2 * n) n) true := by
  have hclassical : simonOracleGuessMass P ≤
      ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) :=
    simonTheorem33RealBudget n (by omega) q hq P hP
  have hcard : Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + 2 * n) ≤ 2 ^ n := by
    have hempty : {x : BooleanVec n | f x ≠ f (x + s)} = ∅ := by
      ext x
      simp [hf x]
    simp [hempty]
  have hquantum : (simonAmplifiedReject f (n + 2 * n) n) true +
      ENNReal.ofReal ((3 / 4 : ℝ) ^ n) ≥ 1 := by
    have h := (simonPaperScheduleTwoSided n (by omega) R f).2 s hs hcard
    have htot : (simonAmplifiedReject f (n + 2 * n) n) true +
        (simonAmplifiedReject f (n + 2 * n) n) false = 1 := by
      rw [pmf_bool_true, pmf_bool_false]
      have hpart := event_partition (simonAmplifiedReject f (n + 2 * n) n)
        (fun b => b = true)
      have heq : event (simonAmplifiedReject f (n + 2 * n) n) (fun b => ¬ (b = true))
          = event (simonAmplifiedReject f (n + 2 * n) n) (fun b => b = false) := by
        unfold event
        apply expectation_congr
        intro x
        by_cases hx : x = true <;> simp [hx]
      rw [heq] at hpart
      exact hpart
    calc
      (simonAmplifiedReject f (n + 2 * n) n) true +
          ENNReal.ofReal ((3 / 4 : ℝ) ^ n)
          ≥ (simonAmplifiedReject f (n + 2 * n) n) true +
              (simonAmplifiedReject f (n + 2 * n) n) false := add_le_add_right h _
      _ = 1 := htot
  by_contra hcon
  push Not at hcon
  have hstep : (simonAmplifiedReject f (n + 2 * n) n) true +
      ENNReal.ofReal ((3 / 4 : ℝ) ^ n) ≤
      simonOracleGuessMass P + ENNReal.ofReal ((3 / 4 : ℝ) ^ n) :=
    add_le_add hcon le_rfl
  have hstep2 : simonOracleGuessMass P + ENNReal.ofReal ((3 / 4 : ℝ) ^ n) ≤
      ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) +
        ENNReal.ofReal ((3 / 4 : ℝ) ^ n) :=
    add_le_add hclassical le_rfl
  exact (not_lt_of_ge hquantum) (lt_of_le_of_lt (le_trans hstep hstep2) (simonSeparationGap n hn))

end Qatlib.Papers.QPowerSimon97.StandardDefs
