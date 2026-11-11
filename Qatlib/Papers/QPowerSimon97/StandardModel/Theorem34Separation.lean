/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.StandardModel.SimonRetry

/-!
# Paper-schedule bounds for Simon's separation

This module specializes the Simon amplification analysis to `3 * n` samples per block and `n`
repetitions [Simon1997]. It proves exact polynomial resource counts, two-sided error bounds with
a near-period tolerance, and a classical guessing bound for a real-valued query budget.

For `n ≥ 64`, `simonTheorem34Separation` compares the distributional classical guessing mass
with the amplified true-output probability of any function possessing a nonzero exact period.

## Main statements

* `simonPaperScheduleLedger`: At the paper schedule, the exact ledger has `3 * n²` queries and
  measurements, `6 * n³` local gates, and `3 * n³` record-conversion steps.
* `simonThirdToleranceAmplification`: For positive width, the paper schedule has the stated
  two-sided error bounds when the number of period violations is at most `2ⁿ / (3 * n)`, and its
  query ledger is `3 * n²`.
* `simonTheorem34Separation`: For `n ≥ 64` and the stated classical query budget, classical
  oracle guessing mass is strictly smaller than the amplified true-output probability for any
  function with a nonzero exact period. This is the finite-parameter separation used for [Simon,
  Theorem 3.4][Simon1997].

## References

* [Simon, 1997][Simon1997]
-/

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

/-- At the paper schedule, the exact ledger has `3 * n²` queries and measurements, `6 * n³`
local gates, and `3 * n³` record-conversion steps. -/
theorem simonPaperScheduleLedger (n : ℕ) :
    (simonExactLedger n (2 * n) n).oracleQueries = 3 * n ^ 2 ∧
    (simonExactLedger n (2 * n) n).measurements = 3 * n ^ 2 ∧
    (simonExactLedger n (2 * n) n).localGates = 6 * n ^ 3 ∧
    (simonExactLedger n (2 * n) n).recordConversion = 3 * n ^ 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [simonExactLedger] <;> ring

/-- With at least two samples, the paper schedule bounds false rejection for injective functions
by `n * (1 / 2) ^ (2 * n)` and false acceptance under the stated near-period condition by
`(3 / 4) ^ n`. -/
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

/-- For positive width, the paper schedule has the stated two-sided error bounds when the number
of period violations is at most `2ⁿ / (3 * n)`, and its query ledger is `3 * n²`. -/
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

/-- For positive width and query budget at most `2 ^ ((n : ℝ) / 4)`, the classical oracle
guessing mass is at most `1 / 2 + 2 ^ (-(n : ℝ) / 2)`. This is the real-budget form of
[Simon, Theorem 3.3][Simon1997]. -/
theorem simonTheorem33RealBudget (n : ℕ) (hn : 1 ≤ n) (q : ℕ)
    (hq : (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4)) (P : PMF (SimonQueryTree n))
    (hP : SimonQueryTree.bounded P q) :
    simonOracleGuessMass P ≤ ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) :=
  simonClassicalRandomOracleBound_realBudget n hn q P hP hq

/-- For `n ≥ 64`, the classical excess term `2 ^ (-(n : ℝ) / 2)` is at most `1 / 8`. -/
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

/-- For `n ≥ 64`, `(3 / 4) ^ n` is at most `1 / 8`. -/
lemma simonThreeQuarters_pow_le (n : ℕ) (hn : 64 ≤ n) :
    (3 / 4 : ℝ) ^ n ≤ 1 / 8 := by
  have hmono : (3 / 4 : ℝ) ^ n ≤ (3 / 4 : ℝ) ^ 10 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h10 : (3 / 4 : ℝ) ^ 10 ≤ 1 / 8 := by norm_num
  linarith

/-- For `n ≥ 64`, the sum of the classical guessing bound and the paper-schedule periodic-oracle
error bound is strictly below one. -/
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

/-- For `n ≥ 64` and the stated classical query budget, classical oracle guessing mass is
strictly smaller than the amplified true-output probability for any function with a nonzero
exact period. This is the finite-parameter separation used for [Simon, Theorem
3.4][Simon1997]. -/
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
