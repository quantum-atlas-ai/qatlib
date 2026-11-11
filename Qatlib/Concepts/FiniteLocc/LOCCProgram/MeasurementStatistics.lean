/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementStatisticsDefs

/-!
# Moments and resource bounds for measurement records

This module proves unbiasedness, variance scaling, third central moment scaling, and Chebyshev
bounds for independent records of a finite POVM. It also derives mixture moment formulas, a
variance decomposition over measurement settings, and a bias bound for U-statistics. Finite
quantum measurement statistics are treated in [Wilde2017], with randomized measurement
applications in [HuangKuengPreskill2020].

`coinciding_record_variance` describes fully coinciding records, whose average retains the
single-record variance. The module also verifies comparison bounds and explicit ledger formulas
for native measurement campaigns.

## Main statements

* `general_sample_mean_variance`: the variance of a nonempty independent sample average is the
  record variance divided by sample size.
* `general_sample_third_central_moment`: the third central moment scales by the inverse square
  of sample size.
* `ensemble_variance_decomposition`: mixture variance splits into within-setting and
  between-setting terms.
* `native_run_ledger`: records campaign operation counts, bit time, and peak space.

## References

* [Wilde, 2017][Wilde2017]
* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatistics
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNative
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.FiniteLocc.LOCCProgram

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementStatistics

open Matrix Qatlib
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

/-- For a positive sample size, the average of independent POVM records has expectation equal to
the single-record mean. -/
theorem general_sample_mean_unbiased (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (hn : 0 < n) (h : O → ℝ) :
    (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) => FinDist.avg h ω)
      = recordMean (povmRecordLaw E ρ hρ) h := by
  have h1 := FinDist.expect_avg (povmRecordLaw E ρ hρ) h hn
  show (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω * FinDist.avg h ω) = _
  rw [h1]
  rfl

/-- For a positive sample size `n`, the mean squared deviation of the independent sample average
is the record variance divided by `n`. -/
theorem general_sample_mean_variance (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (hn : 0 < n) (h : O → ℝ) :
    (povmSampleLaw E ρ hρ).expect
        (fun ω : (Fin n → O) =>
          (FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h) ^ 2)
      = recordVariance (povmRecordLaw E ρ hρ) h / (n : ℝ) := by
  have h1 := FinDist.expect_avg_sub_sq (povmRecordLaw E ρ hρ) h hn
  show (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
      * (FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h) ^ 2) = _
  simp only [recordMean]
  rw [h1]
  rfl

/-- The probability-weighted sum of a centered POVM record statistic is zero. -/
theorem centred_record_mean_zero (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (h : O → ℝ) :
    (∑ x, (povmRecordLaw E ρ hρ).prob x * centredValue (povmRecordLaw E ρ hρ) h x) = 0 := by
  have h1 := centred_mean_zero (povmRecordLaw E ρ hρ) h
  simpa [FinDist.expect] using! h1

/-- For a mean-zero record statistic, the expected product at three sample positions vanishes
whenever the first two positions are distinct. -/
theorem sample_triple_zero_of_ne (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (i j : Fin n) (hij : i ≠ j) (h : O → ℝ) (l : Fin n)
    (hmean : (∑ x, (povmRecordLaw E ρ hρ).prob x * h x) = 0) :
    (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) => h (ω i) * h (ω j) * h (ω l))
      = 0 := by
  by_cases hli : l = i
  · rw [hli]
    have hconv : (fun ω : (Fin n → O) => h (ω i) * h (ω j) * h (ω i))
        = (fun ω : (Fin n → O) => (h (ω i)) ^ 2 * h (ω j)) := by
      funext ω
      ring
    rw [hconv, sample_expect_pair_sq E ρ hρ i j hij h h, hmean]
    simp
  · by_cases hlj : l = j
    · rw [hlj]
      have hconv : (fun ω : (Fin n → O) => h (ω i) * h (ω j) * h (ω j))
          = (fun ω : (Fin n → O) => (h (ω j)) ^ 2 * h (ω i)) := by
        funext ω
        ring
      rw [hconv, sample_expect_pair_sq E ρ hρ j i (Ne.symm hij) h h, hmean]
      simp
    · rw [sample_expect_triple E ρ hρ i j l hij (Ne.symm hli) (Ne.symm hlj) h h h,
        hmean]
      simp

/-- For a mean-zero record statistic and distinct positions, the expectation of its square at
one position times its value at the other is zero. -/
theorem sample_sq_triple_zero_of_ne (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (i l : Fin n) (hil : i ≠ l) (h : O → ℝ)
    (hmean : (∑ x, (povmRecordLaw E ρ hρ).prob x * h x) = 0) :
    (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) => h (ω i) * h (ω i) * h (ω l))
      = 0 := by
  have hconv : (fun ω : (Fin n → O) => h (ω i) * h (ω i) * h (ω l))
      = (fun ω : (Fin n → O) => (h (ω i)) ^ 2 * h (ω l)) := by
    funext ω
    ring
  rw [hconv, sample_expect_pair_sq E ρ hρ i l hil h h, hmean]
  simp

/-- The sum of all centered triple-product expectations in a nonempty independent sample equals
the sample size times the record third central moment. -/
theorem sample_triple_sum (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (hn : 0 < n) (h : O → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
        (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l)))
      = (n : ℝ) * recordThirdCentralMoment (povmRecordLaw E ρ hρ) h := by
  classical
  have hmean : (∑ x, (povmRecordLaw E ρ hρ).prob x
      * centredValue (povmRecordLaw E ρ hρ) h x) = 0 :=
    centred_record_mean_zero E ρ hρ h

  have hdiag : ∀ (i : Fin n),
      (∑ l : Fin n,
        (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l)))
        = recordThirdCentralMoment (povmRecordLaw E ρ hρ) h := by
    intro i
    have hadd := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun l : Fin n => (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
        centredValue (povmRecordLaw E ρ hρ) h (ω i)
          * centredValue (povmRecordLaw E ρ hρ) h (ω i)
          * centredValue (povmRecordLaw E ρ hρ) h (ω l))) (a := i)
      (Finset.mem_univ i)
    rw [← hadd]
    have herase : (∑ l ∈ (Finset.univ : Finset (Fin n)).erase i,
        (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l))) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hli : l ≠ i := by
        intro hli
        subst hli
        simp at hl
      exact sample_sq_triple_zero_of_ne E ρ hρ i l (Ne.symm hli)
        (centredValue (povmRecordLaw E ρ hρ) h) hmean
    rw [herase]
    have hone : (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
        centredValue (povmRecordLaw E ρ hρ) h (ω i)
          * centredValue (povmRecordLaw E ρ hρ) h (ω i)
          * centredValue (povmRecordLaw E ρ hρ) h (ω i))
        = recordThirdCentralMoment (povmRecordLaw E ρ hρ) h := by
      have hconv : (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω i))
          = (fun ω : (Fin n → O) =>
            (centredValue (povmRecordLaw E ρ hρ) h (ω i)) ^ 3) := by
        funext ω
        ring
      rw [hconv, sample_expect_single E ρ hρ i (fun x =>
        (centredValue (povmRecordLaw E ρ hρ) h x) ^ 3)]
      rfl
    have hone' : (fun l : Fin n => (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
        centredValue (povmRecordLaw E ρ hρ) h (ω i)
          * centredValue (povmRecordLaw E ρ hρ) h (ω i)
          * centredValue (povmRecordLaw E ρ hρ) h (ω l))) i
        = recordThirdCentralMoment (povmRecordLaw E ρ hρ) h := hone
    simpa using hone

  have hoff : ∀ (i j : Fin n), i ≠ j →
      (∑ l : Fin n,
        (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l))) = 0 := by
    intro i j hij
    refine Finset.sum_eq_zero fun l _ => ?_
    exact sample_triple_zero_of_ne E ρ hρ i j hij
      (centredValue (povmRecordLaw E ρ hρ) h) l hmean

  have hsplit : ∀ (i : Fin n),
      (∑ j : Fin n, ∑ l : Fin n,
        (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l)))
        = recordThirdCentralMoment (povmRecordLaw E ρ hρ) h := by
    intro i
    have hadd := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun j : Fin n => ∑ l : Fin n,
        (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l))) (a := i)
      (Finset.mem_univ i)
    rw [← hadd]
    have herase : (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ∑ l : Fin n,
        (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l))) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hji : j ≠ i := by
        intro hji
        subst hji
        simp at hj
      exact hoff i j (Ne.symm hji)
    rw [herase]
    have hbeta : (fun j : Fin n => ∑ l : Fin n,
        (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l))) i
        = ∑ l : Fin n,
          (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
            centredValue (povmRecordLaw E ρ hρ) h (ω i)
              * centredValue (povmRecordLaw E ρ hρ) h (ω i)
              * centredValue (povmRecordLaw E ρ hρ) h (ω l)) := rfl
    simpa using hdiag i
  calc (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
        (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l)))
      = ∑ i : Fin n, recordThirdCentralMoment (povmRecordLaw E ρ hρ) h := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsplit]
    _ = (n : ℝ) * recordThirdCentralMoment (povmRecordLaw E ρ hρ) h := by
        have hconst := Finset.sum_const (s := (Finset.univ : Finset (Fin n)))
          (b := recordThirdCentralMoment (povmRecordLaw E ρ hρ) h)
        rw [nsmul_eq_mul] at hconst
        rw [hconst, Finset.card_univ]
        norm_num

/-- For a positive sample size `n`, the third central moment of the independent sample average
is the record third central moment divided by `n ^ 2`. -/
theorem general_sample_third_central_moment (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (hn : 0 < n) (h : O → ℝ) :
    (povmSampleLaw E ρ hρ).expect
        (fun ω : (Fin n → O) =>
          (FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h) ^ 3)
      = recordThirdCentralMoment (povmRecordLaw E ρ hρ) h / (n : ℝ) ^ 2 := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)

  have hpoint : ∀ ω : (Fin n → O),
      (FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h) ^ 3
        = ((∑ i : Fin n, centredValue (povmRecordLaw E ρ hρ) h (ω i)) / (n : ℝ)) ^ 3 := by
    intro ω
    have hsum : (∑ i : Fin n, centredValue (povmRecordLaw E ρ hρ) h (ω i))
        = (∑ i : Fin n, h (ω i)) - (n : ℝ) * recordMean (povmRecordLaw E ρ hρ) h := by
      have h1 : (∑ i : Fin n, centredValue (povmRecordLaw E ρ hρ) h (ω i))
          = ∑ i : Fin n, (h (ω i) - recordMean (povmRecordLaw E ρ hρ) h) := by
        refine Finset.sum_congr rfl fun i _ => rfl
      rw [h1]
      have h2 : (∑ i : Fin n, (h (ω i) - recordMean (povmRecordLaw E ρ hρ) h))
          = (∑ i : Fin n, h (ω i)) - ∑ i : Fin n, recordMean (povmRecordLaw E ρ hρ) h := by
        rw [Finset.sum_sub_distrib]
      rw [h2]
      have h3 : (∑ i : Fin n, recordMean (povmRecordLaw E ρ hρ) h)
          = (n : ℝ) * recordMean (povmRecordLaw E ρ hρ) h := by
        have hconst := Finset.sum_const (s := (Finset.univ : Finset (Fin n)))
          (b := recordMean (povmRecordLaw E ρ hρ) h)
        rw [nsmul_eq_mul] at hconst
        rw [hconst, Finset.card_univ]
        norm_num
      rw [h3]
    rw [FinDist.avg, hsum]
    have hkey : (∑ i : Fin n, h (ω i)) / (n : ℝ) - recordMean (povmRecordLaw E ρ hρ) h
        = ((∑ i : Fin n, h (ω i)) - (n : ℝ) * recordMean (povmRecordLaw E ρ hρ) h) / (n : ℝ) := by
      field_simp [hn0]
    rw [hkey]

  have hexp : ∀ ω : (Fin n → O),
      (∑ i : Fin n, centredValue (povmRecordLaw E ρ hρ) h (ω i)) ^ 3
        = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l) := by
    intro ω
    let c : Fin n → ℝ := fun i => centredValue (povmRecordLaw E ρ hρ) h (ω i)
    have hA : (∑ i : Fin n, c i) * (∑ j : Fin n, c j) * (∑ l : Fin n, c l)
        = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, c i * c j * c l := by
      calc (∑ i : Fin n, c i) * (∑ j : Fin n, c j) * (∑ l : Fin n, c l)
          = (∑ i : Fin n, c i) * ((∑ j : Fin n, c j) * (∑ l : Fin n, c l)) := by
              ring
        _ = (∑ i : Fin n, c i) * (∑ j : Fin n, ∑ l : Fin n, c j * c l) := by
              rw [productLaw_sum_prod c c]
        _ = ∑ i : Fin n, c i * (∑ j : Fin n, ∑ l : Fin n, c j * c l) := by
              rw [Finset.sum_mul]
        _ = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, c i * (c j * c l) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
        _ = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, c i * c j * c l := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              refine Finset.sum_congr rfl fun l _ => ?_
              ring
    calc (∑ i : Fin n, c i) ^ 3
        = (∑ i : Fin n, c i) * (∑ j : Fin n, c j) * (∑ l : Fin n, c l) := by ring
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, c i * c j * c l := hA
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rfl

  have hexch : (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
        * (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l)))
      = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, ∑ ω : (Fin n → O),
        (povmRecordLaw E ρ hρ).probOf ω
          * (centredValue (povmRecordLaw E ρ hρ) h (ω i)
            * centredValue (povmRecordLaw E ρ hρ) h (ω j)
            * centredValue (povmRecordLaw E ρ hρ) h (ω l)) := by
    calc (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
          * (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
            centredValue (povmRecordLaw E ρ hρ) h (ω i)
              * centredValue (povmRecordLaw E ρ hρ) h (ω j)
              * centredValue (povmRecordLaw E ρ hρ) h (ω l)))
        = ∑ ω : (Fin n → O), ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          (povmRecordLaw E ρ hρ).probOf ω
            * (centredValue (povmRecordLaw E ρ hρ) h (ω i)
              * centredValue (povmRecordLaw E ρ hρ) h (ω j)
              * centredValue (povmRecordLaw E ρ hρ) h (ω l)) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
        _ = ∑ i : Fin n, ∑ ω : (Fin n → O), ∑ j : Fin n, ∑ l : Fin n,
          (povmRecordLaw E ρ hρ).probOf ω
            * (centredValue (povmRecordLaw E ρ hρ) h (ω i)
              * centredValue (povmRecordLaw E ρ hρ) h (ω j)
              * centredValue (povmRecordLaw E ρ hρ) h (ω l)) := by
          rw [Finset.sum_comm]
        _ = ∑ i : Fin n, ∑ j : Fin n, ∑ ω : (Fin n → O), ∑ l : Fin n,
          (povmRecordLaw E ρ hρ).probOf ω
            * (centredValue (povmRecordLaw E ρ hρ) h (ω i)
              * centredValue (povmRecordLaw E ρ hρ) h (ω j)
              * centredValue (povmRecordLaw E ρ hρ) h (ω l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
        _ = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, ∑ ω : (Fin n → O),
          (povmRecordLaw E ρ hρ).probOf ω
            * (centredValue (povmRecordLaw E ρ hρ) h (ω i)
              * centredValue (povmRecordLaw E ρ hρ) h (ω j)
              * centredValue (povmRecordLaw E ρ hρ) h (ω l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]

  have hsum : (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
      * (FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h) ^ 3)
      = (1 / (n : ℝ) ^ 3) * (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
            centredValue (povmRecordLaw E ρ hρ) h (ω i)
              * centredValue (povmRecordLaw E ρ hρ) h (ω j)
              * centredValue (povmRecordLaw E ρ hρ) h (ω l))) := by
    calc (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
        * (FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h) ^ 3)
        = ∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
            * ((1 / (n : ℝ) ^ 3) * (∑ i : Fin n, centredValue (povmRecordLaw E ρ hρ) h (ω i)) ^ 3) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [hpoint ω]
          ring
        _ = ∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
            * ((1 / (n : ℝ) ^ 3)
              * (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
                centredValue (povmRecordLaw E ρ hρ) h (ω i)
                  * centredValue (povmRecordLaw E ρ hρ) h (ω j)
                  * centredValue (povmRecordLaw E ρ hρ) h (ω l))) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [hexp ω]
        _ = (1 / (n : ℝ) ^ 3) * (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
            * (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
              centredValue (povmRecordLaw E ρ hρ) h (ω i)
                * centredValue (povmRecordLaw E ρ hρ) h (ω j)
                * centredValue (povmRecordLaw E ρ hρ) h (ω l))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω _ => ?_
          ring
        _ = (1 / (n : ℝ) ^ 3) * (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, ∑ ω : (Fin n → O),
            (povmRecordLaw E ρ hρ).probOf ω
              * (centredValue (povmRecordLaw E ρ hρ) h (ω i)
                * centredValue (povmRecordLaw E ρ hρ) h (ω j)
                * centredValue (povmRecordLaw E ρ hρ) h (ω l))) := by
          rw [hexch]
        _ = (1 / (n : ℝ) ^ 3) * (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
            (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → O) =>
              centredValue (povmRecordLaw E ρ hρ) h (ω i)
                * centredValue (povmRecordLaw E ρ hρ) h (ω j)
                * centredValue (povmRecordLaw E ρ hρ) h (ω l))) := by
          congr 1
  show (∑ ω : (Fin n → O), (povmRecordLaw E ρ hρ).probOf ω
      * (FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h) ^ 3) = _
  rw [hsum, sample_triple_sum E ρ hρ hn h]
  field_simp [hn0]

/-- For positive sample size and tolerance, the probability that the independent sample average
deviates by more than `ε` is at most the record variance divided by `n * ε ^ 2`. -/
theorem general_sample_confidence (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) {n : ℕ} (hn : 0 < n) (h : O → ℝ) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
        (fun ω : (Fin n → O) =>
          ε < |FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h|)
      ≤ recordVariance (povmRecordLaw E ρ hρ) h / (n * ε ^ 2) := by
  have h1 := FinDist.chebyshev_avg (povmRecordLaw E ρ hρ) h hn ε hε
  exact h1

/-- The second moment minus the variance of a finite-distribution statistic equals the square of
its mean. -/
theorem variance_second_moment_gap (p : FinDist O) (h : O → ℝ) :
    recordSecondMoment p h - recordVariance p h = (p.expect h) ^ 2 := by
  have h1 := FinDist.expect_centered_sq p h
  unfold recordSecondMoment recordVariance FinDist.variance
  rw [h1]
  ring

/-- The variance of a finite-distribution statistic is at most its second moment. -/
theorem variance_le_second_moment (p : FinDist O) (h : O → ℝ) :
    recordVariance p h ≤ recordSecondMoment p h := by
  have h1 := variance_second_moment_gap p h
  have h2 : 0 ≤ (p.expect h) ^ 2 := sq_nonneg _
  linarith

/-- For the uniform law on `Fin 2` and the statistic given by the outcome's numeric value, the
second moment minus the variance is one quarter. -/
theorem variance_envelope_gap_concrete :
    let p : FinDist (Fin 2) :=
      { prob := fun _ => (1 : ℝ) / 2
        nonneg := fun _ => by norm_num
        sum_one := by norm_num }
    let h : Fin 2 → ℝ := fun x => (x : ℝ)
    recordSecondMoment p h - recordVariance p h = (1 : ℝ) / 4 := by
  norm_num [recordSecondMoment, recordVariance, FinDist.variance, FinDist.expect]

/-- Under the coinciding-record law, the expectation of a statistic of the first coordinate
equals its expectation under the original law. -/
theorem coincidingRecordLaw_expect {m : ℕ} (p : FinDist O) (φ : O → ℝ) :
    (coincidingRecordLaw p).expect (fun ω : (Fin (m+1) → O) => φ (ω 0))
      = p.expect φ := by
  classical
  show (∑ ω : (Fin (m+1) → O),
      (if ∀ i, ω i = ω 0 then p.prob (ω 0) else 0) * φ (ω 0)) = _
  have hconv : (∑ ω : (Fin (m+1) → O),
      (if ∀ i, ω i = ω 0 then p.prob (ω 0) else 0) * φ (ω 0))
      = ∑ ω : (Fin (m+1) → O),
        (if ∀ i, ω i = ω 0 then p.prob (ω 0) * φ (ω 0) else 0) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : ∀ i, ω i = ω 0
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      ring
  have h1 := Finset.sum_filter (s := (Finset.univ : Finset (Fin (m+1) → O)))
    (p := fun ω => ∀ i, ω i = ω 0) (f := fun ω => p.prob (ω 0) * φ (ω 0))
  rw [hconv, ← h1]
  refine Finset.sum_bij
    (s := (Finset.univ : Finset (Fin (m+1) → O)).filter
      (fun ω => ∀ i, ω i = ω 0))
    (t := (Finset.univ : Finset O))
    (f := fun ω : (Fin (m+1) → O) => p.prob (ω 0) * φ (ω 0))
    (g := fun x : O => p.prob x * φ x)
    (fun ω _ => ω 0) ?_ ?_ ?_ ?_
  · intro ω hω
    exact Finset.mem_univ (ω 0)
  · intro a1 ha1 a2 ha2 hEq
    have h1' : a1 = fun _ => a1 0 := by
      funext i
      exact (Finset.mem_filter.mp ha1).2 i
    have h2' : a2 = fun _ => a2 0 := by
      funext i
      exact (Finset.mem_filter.mp ha2).2 i
    have hEq' : a1 0 = a2 0 := by simpa using! hEq
    rw [h1', h2', hEq']
  · intro b hb
    refine ⟨fun _ => b, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by intro i; rfl⟩
    · rfl
  · intro a ha
    rfl

/-- The average of fully coinciding records has the original statistic's variance, for any
positive number of records. -/
theorem coinciding_record_variance {m : ℕ} (p : FinDist O) (h : O → ℝ) :
    (coincidingRecordLaw p).expect
        (fun ω : (Fin (m+1) → O) =>
          (FinDist.avg h ω - p.expect h) ^ 2)
      = p.variance h := by
  classical
  have hsq : (coincidingRecordLaw p).expect
      (fun ω : (Fin (m+1) → O) => (h (ω 0) - p.expect h) ^ 2)
      = p.variance h := by
    have h2 := coincidingRecordLaw_expect (m := m) p (fun x => (h x - p.expect h) ^ 2)
    rw [h2]
    rfl
  have hconv : (coincidingRecordLaw p).expect
      (fun ω : (Fin (m+1) → O) => (FinDist.avg h ω - p.expect h) ^ 2)
      = (coincidingRecordLaw p).expect
      (fun ω : (Fin (m+1) → O) => (h (ω 0) - p.expect h) ^ 2) := by
    show (∑ ω : (Fin (m+1) → O),
        (if ∀ i, ω i = ω 0 then p.prob (ω 0) else 0)
          * (FinDist.avg h ω - p.expect h) ^ 2)
      = ∑ ω : (Fin (m+1) → O),
        (if ∀ i, ω i = ω 0 then p.prob (ω 0) else 0)
          * (h (ω 0) - p.expect h) ^ 2
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hc : ∀ i, ω i = ω 0
    · rw [if_pos hc]
      have heq : ω = fun _ => ω 0 := by
        funext i
        exact hc i
      rw [heq]
      have havg : FinDist.avg h (fun _ : (Fin (m+1)) => ω 0) = h (ω 0) := by
        have hne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by
          have hpos : (0 : ℕ) < m + 1 := by omega
          exact_mod_cast hpos.ne'
        have hsum : (∑ i : (Fin (m+1)), h (ω 0)) = ((m + 1 : ℕ) : ℝ) * h (ω 0) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        unfold FinDist.avg
        rw [hsum]
        exact mul_div_cancel_left₀ _ hne
      rw [havg]
    · rw [if_neg hc]
      ring
  rw [hconv, hsq]

/-- The ensemble mean is the setting-probability-weighted sum of the individual setting means. -/
theorem ensemble_mean_mixture {m : ℕ} (E : Fin m → FinitePOVM O D) (q : FinDist (Fin m))
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (h : O → ℝ) :
    ensembleMean E q ρ hρ h = ∑ s : Fin m, q.prob s * settingMean E q ρ hρ h s := by
  unfold ensembleMean settingMean
  show (∑ x : O, (∑ s : Fin m, q.prob s * (povmRecordLaw (E s) ρ hρ).prob x) * h x)
    = ∑ s : Fin m, q.prob s * (∑ x : O, (povmRecordLaw (E s) ρ hρ).prob x * h x)
  calc (∑ x : O, (∑ s : Fin m, q.prob s * (povmRecordLaw (E s) ρ hρ).prob x) * h x)
      = ∑ x : O, ∑ s : Fin m, (q.prob s * (povmRecordLaw (E s) ρ hρ).prob x) * h x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ s : Fin m, ∑ x : O, (q.prob s * (povmRecordLaw (E s) ρ hρ).prob x) * h x :=
          Finset.sum_comm
    _ = ∑ s : Fin m, q.prob s * (∑ x : O, (povmRecordLaw (E s) ρ hρ).prob x * h x) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring

/-- The ensemble second moment is the setting-probability-weighted sum of the individual setting
second moments. -/
theorem ensemble_second_moment_mixture {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (h : O → ℝ) :
    ensembleSecondMoment E q ρ hρ h
      = ∑ s : Fin m, q.prob s * settingSecondMoment E q ρ hρ h s := by
  unfold ensembleSecondMoment settingSecondMoment
  show (∑ x : O, (∑ s : Fin m, q.prob s * (povmRecordLaw (E s) ρ hρ).prob x) * (h x) ^ 2)
    = ∑ s : Fin m, q.prob s * (∑ x : O, (povmRecordLaw (E s) ρ hρ).prob x * (h x) ^ 2)
  calc (∑ x : O, (∑ s : Fin m, q.prob s * (povmRecordLaw (E s) ρ hρ).prob x) * (h x) ^ 2)
      = ∑ x : O, ∑ s : Fin m, (q.prob s * (povmRecordLaw (E s) ρ hρ).prob x) * (h x) ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ s : Fin m, ∑ x : O, (q.prob s * (povmRecordLaw (E s) ρ hρ).prob x) * (h x) ^ 2 :=
          Finset.sum_comm
    _ = ∑ s : Fin m, q.prob s * (∑ x : O, (povmRecordLaw (E s) ρ hρ).prob x * (h x) ^ 2) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring

/-- The ensemble variance equals the mean of the setting variances plus the variance of the
setting means. -/
theorem ensemble_variance_decomposition {m : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (h : O → ℝ) :
    ensembleVariance E q ρ hρ h
      = (∑ s : Fin m, q.prob s * settingVariance E q ρ hρ h s)
        + q.variance (fun s => settingMean E q ρ hρ h s) := by
  have hvar : ensembleVariance E q ρ hρ h
      = ensembleSecondMoment E q ρ hρ h - (ensembleMean E q ρ hρ h) ^ 2 := by
    have h1 := FinDist.expect_centered_sq (ensembleOutcomeLaw E q ρ hρ) h
    unfold ensembleVariance ensembleSecondMoment FinDist.variance
    rw [h1]
    unfold ensembleMean
    rfl
  have hsetvar (s : Fin m) :
      settingVariance E q ρ hρ h s
        = settingSecondMoment E q ρ hρ h s - (settingMean E q ρ hρ h s) ^ 2 := by
    have h1 := FinDist.expect_centered_sq (povmRecordLaw (E s) ρ hρ) h
    unfold settingVariance settingSecondMoment settingMean FinDist.variance
    rw [h1]
  have hqvar : q.variance (fun s => settingMean E q ρ hρ h s)
      = (∑ s : Fin m, q.prob s * (settingMean E q ρ hρ h s) ^ 2)
        - (∑ s : Fin m, q.prob s * settingMean E q ρ hρ h s) ^ 2 := by
    have h1 := FinDist.expect_centered_sq q (fun s => settingMean E q ρ hρ h s)
    unfold FinDist.variance
    rw [h1]
    rfl
  have hsumeq : (∑ s : Fin m, q.prob s
          * (settingSecondMoment E q ρ hρ h s - (settingMean E q ρ hρ h s) ^ 2))
        = ∑ s : Fin m, q.prob s * settingVariance E q ρ hρ h s := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hsetvar]
  have hmix := ensemble_mean_mixture E q ρ hρ h
  have hmix2 := ensemble_second_moment_mixture E q ρ hρ h
  rw [hvar, hmix, hmix2]
  calc (∑ s : Fin m, q.prob s * settingSecondMoment E q ρ hρ h s)
        - (∑ s : Fin m, q.prob s * settingMean E q ρ hρ h s) ^ 2
      = (∑ s : Fin m, q.prob s * settingSecondMoment E q ρ hρ h s)
        - (∑ s : Fin m, q.prob s * (settingMean E q ρ hρ h s) ^ 2)
        + ((∑ s : Fin m, q.prob s * (settingMean E q ρ hρ h s) ^ 2)
          - (∑ s : Fin m, q.prob s * settingMean E q ρ hρ h s) ^ 2) := by ring
    _ = (∑ s : Fin m, q.prob s
          * (settingSecondMoment E q ρ hρ h s - (settingMean E q ρ hρ h s) ^ 2))
        + ((∑ s : Fin m, q.prob s * (settingMean E q ρ hρ h s) ^ 2)
          - (∑ s : Fin m, q.prob s * settingMean E q ρ hρ h s) ^ 2) := by
        have h1 : (∑ s : Fin m, q.prob s * settingSecondMoment E q ρ hρ h s)
            - (∑ s : Fin m, q.prob s * (settingMean E q ρ hρ h s) ^ 2)
            = ∑ s : Fin m, q.prob s
              * (settingSecondMoment E q ρ hρ h s - (settingMean E q ρ hρ h s) ^ 2) := by
          calc (∑ s : Fin m, q.prob s * settingSecondMoment E q ρ hρ h s)
              - (∑ s : Fin m, q.prob s * (settingMean E q ρ hρ h s) ^ 2)
              = ∑ s : Fin m, (q.prob s * settingSecondMoment E q ρ hρ h s
                  - q.prob s * (settingMean E q ρ hρ h s) ^ 2) := by
                rw [Finset.sum_sub_distrib]
            _ = ∑ s : Fin m, q.prob s
                * (settingSecondMoment E q ρ hρ h s - (settingMean E q ρ hρ h s) ^ 2) := by
                refine Finset.sum_congr rfl fun s _ => ?_
                ring
        rw [h1]
    _ = (∑ s : Fin m, q.prob s * settingVariance E q ρ hρ h s)
        + q.variance (fun s => settingMean E q ρ hρ h s) := by
        rw [hsumeq, hqvar]

/-- For positive sample size and tolerance, independent ensemble records satisfy the Chebyshev
bound using the ensemble variance. -/
theorem ensemble_sample_confidence {m n : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (hn : 0 < n) (h : O → ℝ) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := n) (ensembleOutcomeLaw E q ρ hρ)
        (fun ω : (Fin n → O) =>
          ε < |FinDist.avg h ω - ensembleMean E q ρ hρ h|)
      ≤ ensembleVariance E q ρ hρ h / (n * ε ^ 2) := by
  have h1 := FinDist.chebyshev_avg (ensembleOutcomeLaw E q ρ hρ) h hn ε hε
  exact h1

/-- Independent ensemble records satisfy the Chebyshev bound with the ensemble second moment in
place of the variance. -/
theorem ensemble_sample_confidence_conservative {m n : ℕ} (E : Fin m → FinitePOVM O D)
    (q : FinDist (Fin m)) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (hn : 0 < n) (h : O → ℝ) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := n) (ensembleOutcomeLaw E q ρ hρ)
        (fun ω : (Fin n → O) =>
          ε < |FinDist.avg h ω - ensembleMean E q ρ hρ h|)
      ≤ ensembleSecondMoment E q ρ hρ h / (n * ε ^ 2) := by
  have h1 := ensemble_sample_confidence E q ρ hρ hn h ε hε
  have h2 := variance_le_second_moment (ensembleOutcomeLaw E q ρ hρ) h
  unfold ensembleVariance recordVariance at h2
  unfold ensembleSecondMoment at *
  calc FinDist.probEvent (L := n) (ensembleOutcomeLaw E q ρ hρ)
        (fun ω : (Fin n → O) => ε < |FinDist.avg h ω - ensembleMean E q ρ hρ h|)
      ≤ (ensembleOutcomeLaw E q ρ hρ).variance h / (n * ε ^ 2) := h1
    _ ≤ (ensembleOutcomeLaw E q ρ hρ).expect (fun x => (h x) ^ 2) / (n * ε ^ 2) := by
          exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- If the number of distinct index tuples is positive and every injective tuple has deviation
at most `Δ`, the absolute U-statistic bias is at most `Δ`. -/
theorem uStatistic_bias_bound {n k : ℕ} (q : FinDist (Fin n → O)) (p : FinDist O)
    (h : (Fin k → O) → ℝ) (Δ : ℝ) (hN : 0 < distinctTupleCount n k)
    (hbound : UStatisticDeviationBound q p h Δ) :
    |uStatisticBias q p h| ≤ Δ := by
  classical
  set N := distinctTupleCount n k with hNdef
  have hNpos : (N : ℝ) ≠ 0 := by
    have h1 : (0 : ℕ) < N := hN
    exact_mod_cast h1.ne'
  have hNabs : 0 ≤ (N : ℝ) := by
    have h1 : (0 : ℕ) < N := hN
    exact_mod_cast h1.le

  have hcount : (∑ t : (Fin k → Fin n), (if Function.Injective t then (1 : ℝ) else 0))
      = (N : ℝ) := by
    have h1 := distinctTupleCount_indicator n k
    rw [← hNdef] at h1
    calc (∑ t : (Fin k → Fin n), (if Function.Injective t then (1 : ℝ) else 0))
        = ((∑ t : (Fin k → Fin n), (if Function.Injective t then (1 : ℕ) else 0)) : ℝ) := by
          exact_mod_cast rfl
      _ = (N : ℝ) := by exact_mod_cast h1

  have hsubk (f g : (Fin k → Fin n) → ℝ) :
      (∑ t : (Fin k → Fin n), f t) - (∑ t : (Fin k → Fin n), g t)
        = ∑ t : (Fin k → Fin n), (f t - g t) := by
    rw [Finset.sum_sub_distrib]

  have hsplit : (∑ t : (Fin k → Fin n),
        (if Function.Injective t then uStatisticTupleDeviation q p h t else 0))
      = (∑ t : (Fin k → Fin n),
          (if Function.Injective t
            then (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s)))
            else 0))
        - (N : ℝ) * kernelMeanK p h := by
    have h1 : (∑ t : (Fin k → Fin n),
          (if Function.Injective t
            then (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s)) - kernelMeanK p h)
            else 0))
        = (∑ t : (Fin k → Fin n),
            (if Function.Injective t
              then (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s)))
              else 0))
          - (∑ t : (Fin k → Fin n),
            (if Function.Injective t then kernelMeanK p h else 0)) := by
      calc (∑ t : (Fin k → Fin n),
          (if Function.Injective t
            then (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s)) - kernelMeanK p h)
            else 0))
          = ∑ t : (Fin k → Fin n),
            ((if Function.Injective t
              then (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s)))
              else 0)
              - (if Function.Injective t then kernelMeanK p h else 0)) := by
              refine Finset.sum_congr rfl fun t _ => ?_
              by_cases ht : Function.Injective t
              · simp [ht] <;> ring
              · simp [ht] <;> ring
        _ = (∑ t : (Fin k → Fin n),
            (if Function.Injective t
              then (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s)))
              else 0))
            - (∑ t : (Fin k → Fin n),
              (if Function.Injective t then kernelMeanK p h else 0)) :=
          (hsubk
            (fun t : (Fin k → Fin n) => if Function.Injective t
              then (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s))) else 0)
            (fun t : (Fin k → Fin n) => if Function.Injective t then kernelMeanK p h else 0)).symm
    have h2 : (∑ t : (Fin k → Fin n),
          (if Function.Injective t then kernelMeanK p h else 0))
        = (N : ℝ) * kernelMeanK p h := by
      calc (∑ t : (Fin k → Fin n), (if Function.Injective t then kernelMeanK p h else 0))
          = ∑ t : (Fin k → Fin n),
              ((if Function.Injective t then (1 : ℝ) else 0) * kernelMeanK p h) := by
            refine Finset.sum_congr rfl fun t _ => ?_
            by_cases ht : Function.Injective t
            · simp [ht] <;> ring
            · simp [ht] <;> ring
        _ = (∑ t : (Fin k → Fin n), (if Function.Injective t then (1 : ℝ) else 0))
              * kernelMeanK p h := by rw [← Finset.sum_mul]
        _ = (N : ℝ) * kernelMeanK p h := by rw [hcount]
    unfold uStatisticTupleDeviation
    rw [h1, h2]

  have h3 : (∑ t : (Fin k → Fin n),
        (if Function.Injective t
          then (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s)))
          else 0))
      = (∑ ω : (Fin n → O), q.prob ω
          * (∑ t : (Fin k → Fin n),
            (if Function.Injective t then h (fun s => ω (t s)) else 0))) := by
    calc (∑ t : (Fin k → Fin n),
          (if Function.Injective t
            then (∑ ω : (Fin n → O), q.prob ω * h (fun s => ω (t s)))
            else 0))
        = (∑ t : (Fin k → Fin n), ∑ ω : (Fin n → O),
          (if Function.Injective t then q.prob ω * h (fun s => ω (t s)) else 0)) := by
            refine Finset.sum_congr rfl fun t _ => ?_
            by_cases ht : Function.Injective t
            · simp [ht] <;> ring
            · simp [ht] <;> ring
      _ = (∑ ω : (Fin n → O), ∑ t : (Fin k → Fin n),
          (if Function.Injective t then q.prob ω * h (fun s => ω (t s)) else 0)) :=
        Finset.sum_comm
      _ = (∑ ω : (Fin n → O), q.prob ω
          * (∑ t : (Fin k → Fin n),
            (if Function.Injective t then h (fun s => ω (t s)) else 0))) := by
            refine Finset.sum_congr rfl fun ω _ => ?_
            have h4 : (∑ t : (Fin k → Fin n),
                (if Function.Injective t then q.prob ω * h (fun s => ω (t s)) else 0))
              = q.prob ω * (∑ t : (Fin k → Fin n),
                (if Function.Injective t then h (fun s => ω (t s)) else 0)) := by
              calc (∑ t : (Fin k → Fin n),
                  (if Function.Injective t then q.prob ω * h (fun s => ω (t s)) else 0))
                  = ∑ t : (Fin k → Fin n),
                    ((if Function.Injective t then h (fun s => ω (t s)) else 0)
                      * q.prob ω) := by
                    refine Finset.sum_congr rfl fun t _ => ?_
                    by_cases ht : Function.Injective t
                    · simp [ht] <;> ring
                    · simp [ht] <;> ring
                _ = (∑ t : (Fin k → Fin n),
                    (if Function.Injective t then h (fun s => ω (t s)) else 0)) * q.prob ω := by
                    rw [← Finset.sum_mul]
                _ = q.prob ω * (∑ t : (Fin k → Fin n),
                    (if Function.Injective t then h (fun s => ω (t s)) else 0)) := by ring
            rw [h4]

  have hdev : (∑ t : (Fin k → Fin n),
        (if Function.Injective t then uStatisticTupleDeviation q p h t else 0))
      = (N : ℝ) * uStatisticBias q p h := by
    rw [hsplit, h3]
    unfold uStatisticBias uStatisticExpectation
    rw [hNdef.symm]
    field_simp [hNpos]

  have habs : |(∑ t : (Fin k → Fin n),
        (if Function.Injective t then uStatisticTupleDeviation q p h t else 0))|
      ≤ ∑ t : (Fin k → Fin n),
        (if Function.Injective t then |uStatisticTupleDeviation q p h t| else 0) := by
    have h1 := Finset.abs_sum_le_sum_abs
      (fun t : (Fin k → Fin n) =>
        if Function.Injective t then uStatisticTupleDeviation q p h t else 0)
      (Finset.univ : Finset (Fin k → Fin n))
    refine le_trans h1 (Finset.sum_le_sum fun t _ => ?_)
    by_cases ht : Function.Injective t
    · simp [ht]
    · simp [ht]
  have hle : (∑ t : (Fin k → Fin n),
        (if Function.Injective t then |uStatisticTupleDeviation q p h t| else 0))
      ≤ (∑ t : (Fin k → Fin n), (if Function.Injective t then Δ else 0)) := by
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases ht : Function.Injective t
    · rw [if_pos ht, if_pos ht]
      exact hbound t ht
    · rw [if_neg ht, if_neg ht]
  have hsumΔ : (∑ t : (Fin k → Fin n), (if Function.Injective t then Δ else 0))
      = (N : ℝ) * Δ := by
    calc (∑ t : (Fin k → Fin n), (if Function.Injective t then Δ else 0))
        = ∑ t : (Fin k → Fin n),
            ((if Function.Injective t then (1 : ℝ) else 0) * Δ) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases ht : Function.Injective t
          · simp [ht] <;> ring
          · simp [ht] <;> ring
        _ = (∑ t : (Fin k → Fin n), (if Function.Injective t then (1 : ℝ) else 0)) * Δ := by
          rw [← Finset.sum_mul]
        _ = (N : ℝ) * Δ := by rw [hcount]

  have hscale : |uStatisticBias q p h|
      = (1 / (N : ℝ)) * |(∑ t : (Fin k → Fin n),
          (if Function.Injective t then uStatisticTupleDeviation q p h t else 0))| := by
    have h1 : uStatisticBias q p h
        = (1 / (N : ℝ)) * (∑ t : (Fin k → Fin n),
            (if Function.Injective t then uStatisticTupleDeviation q p h t else 0)) := by
      rw [hdev]
      field_simp [hNpos]
    rw [h1, abs_mul, abs_div, abs_one, abs_of_nonneg hNabs]
  calc |uStatisticBias q p h|
      = (1 / (N : ℝ)) * |(∑ t : (Fin k → Fin n),
          (if Function.Injective t then uStatisticTupleDeviation q p h t else 0))| := hscale
    _ ≤ (1 / (N : ℝ))
        * (∑ t : (Fin k → Fin n),
          (if Function.Injective t then |uStatisticTupleDeviation q p h t| else 0)) := by
          exact mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ (1 / (N : ℝ)) * (∑ t : (Fin k → Fin n),
          (if Function.Injective t then Δ else 0)) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (1 / (N : ℝ)) * ((N : ℝ) * Δ) := by rw [hsumΔ]
    _ = Δ := by field_simp [hNpos]

/-- The result-dependent native axis cost is at most the history length plus the native
axis-table length. -/
theorem result_dependent_table_cost (history : List (Fin 3 × Fin 2)) :
    nativeResultDependentAxisCost history
      ≤ history.length + nativeAxisTable.length := by
  exact nativeResultDependentAxisCost_le history

/-- Counted rational insertion sort uses at most the square of the input length in comparisons. -/
theorem order_statistic_cost (means : List ℚ) :
    (rationalInsertionSortCounted means).2 ≤ means.length * means.length :=
  rationalInsertionSortCounted_cost_le means

/-- Establishes the native campaign's exact measurement, query, draw, read, and addition counts,
comparison bounds, and formulas for bit time and peak space. -/
theorem native_run_ledger {K L : ℕ} (c : NativeCampaign K L) (m : NativeMachine) :
    (nativeLedger c m).measurements = K * L ∧
    (nativeLedger c m).queries = 0 ∧
    (nativeLedger c m).axisDraws = (campaignFlatten c.records).length ∧
    (nativeLedger c m).tableReads = (campaignFlatten c.records).length ∧
    (nativeLedger c m).statisticReads = (campaignFlatten c.records).length ∧
    (nativeLedger c m).rationalAdditions = (campaignFlatten c.records).length ∧
    (nativeLedger c m).medianComparisons ≤ K * K ∧
    (nativeLedger c m).axisComparisons
      ≤ (campaignFlatten c.records).length
        * (nativeAxisTable.length + nativeAxisTable.length) ∧
    (nativeLedger c m).bitTime
      = (nativeLedger c m).axisDraws * m.axisDrawBits
        + (nativeLedger c m).axisComparisons * m.comparisonBits
        + (nativeLedger c m).tableReads * (m.addressBits + m.wordBits)
        + (nativeLedger c m).statisticReads * m.wordBits
        + (nativeLedger c m).rationalAdditions * m.additionBits
        + (nativeLedger c m).medianComparisons * m.comparisonBits ∧
    (nativeLedger c m).peakSpace
      = (campaignFlatten c.records).length * m.recordBits
        + K * m.wordBits + K * m.wordBits := by
  have h := nativeLedger_spec c m
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Collects sample-mean unbiasedness and variance scaling, ensemble mean and variance
decompositions, and the U-statistic bias bound. -/
theorem clause6_endpoint :
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] (Dt : ℕ)
      (E : FinitePOVM Ot Dt) (ρ : Operator Dt) (hρ : IsDensityOperator ρ)
      {n : ℕ} (hn : 0 < n) (h : Ot → ℝ),
      (povmSampleLaw E ρ hρ).expect (fun ω : (Fin n → Ot) => FinDist.avg h ω)
        = recordMean (povmRecordLaw E ρ hρ) h) ∧
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] (Dt : ℕ)
      (E : FinitePOVM Ot Dt) (ρ : Operator Dt) (hρ : IsDensityOperator ρ)
      {n : ℕ} (hn : 0 < n) (h : Ot → ℝ),
      (povmSampleLaw E ρ hρ).expect
          (fun ω : (Fin n → Ot) =>
            (FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h) ^ 2)
        = recordVariance (povmRecordLaw E ρ hρ) h / (n : ℝ)) ∧
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] (Dt : ℕ) (m : ℕ)
      (E : Fin m → FinitePOVM Ot Dt) (q : FinDist (Fin m))
      (ρ : Operator Dt) (hρ : IsDensityOperator ρ) (h : Ot → ℝ),
      ensembleMean E q ρ hρ h
        = ∑ s : Fin m, q.prob s * settingMean E q ρ hρ h s) ∧
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] (Dt : ℕ) (m : ℕ)
      (E : Fin m → FinitePOVM Ot Dt) (q : FinDist (Fin m))
      (ρ : Operator Dt) (hρ : IsDensityOperator ρ) (h : Ot → ℝ),
      ensembleVariance E q ρ hρ h
        = (∑ s : Fin m, q.prob s * settingVariance E q ρ hρ h s)
          + q.variance (fun s => settingMean E q ρ hρ h s)) ∧
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] {n k : ℕ}
      (q : FinDist (Fin n → Ot)) (p : FinDist Ot) (h : (Fin k → Ot) → ℝ)
      (Δ : ℝ) (hN : 0 < distinctTupleCount n k)
      (hbound : UStatisticDeviationBound q p h Δ),
      |uStatisticBias q p h| ≤ Δ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Ot inst inst2 Dt E ρ hρ n hn h
    exact general_sample_mean_unbiased E ρ hρ hn h
  · intro Ot inst inst2 Dt E ρ hρ n hn h
    exact general_sample_mean_variance E ρ hρ hn h
  · intro Ot inst inst2 Dt m E q ρ hρ h
    exact ensemble_mean_mixture E q ρ hρ h
  · intro Ot inst inst2 Dt m E q ρ hρ h
    exact ensemble_variance_decomposition E q ρ hρ h
  · intro Ot inst inst2 n k q p h Δ hN hbound
    exact uStatistic_bias_bound q p h Δ hN hbound

/-- Collects POVM and ensemble confidence bounds, the second-moment gap identity, and the
variance formula for fully coinciding records. -/
theorem clause9_endpoint :
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] (Dt : ℕ)
      (E : FinitePOVM Ot Dt) (ρ : Operator Dt) (hρ : IsDensityOperator ρ)
      {n : ℕ} (hn : 0 < n) (h : Ot → ℝ) (ε : ℝ) (hε : 0 < ε),
      FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
          (fun ω : (Fin n → Ot) =>
            ε < |FinDist.avg h ω - recordMean (povmRecordLaw E ρ hρ) h|)
        ≤ recordVariance (povmRecordLaw E ρ hρ) h / (n * ε ^ 2)) ∧
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] (Dt : ℕ) {m n : ℕ}
      (E : Fin m → FinitePOVM Ot Dt) (q : FinDist (Fin m))
      (ρ : Operator Dt) (hρ : IsDensityOperator ρ) (hn : 0 < n) (h : Ot → ℝ)
      (ε : ℝ) (hε : 0 < ε),
      FinDist.probEvent (L := n) (ensembleOutcomeLaw E q ρ hρ)
          (fun ω : (Fin n → Ot) =>
            ε < |FinDist.avg h ω - ensembleMean E q ρ hρ h|)
        ≤ ensembleVariance E q ρ hρ h / (n * ε ^ 2)) ∧
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] (Dt : ℕ) {m n : ℕ}
      (E : Fin m → FinitePOVM Ot Dt) (q : FinDist (Fin m))
      (ρ : Operator Dt) (hρ : IsDensityOperator ρ) (hn : 0 < n) (h : Ot → ℝ)
      (ε : ℝ) (hε : 0 < ε),
      FinDist.probEvent (L := n) (ensembleOutcomeLaw E q ρ hρ)
          (fun ω : (Fin n → Ot) =>
            ε < |FinDist.avg h ω - ensembleMean E q ρ hρ h|)
        ≤ ensembleSecondMoment E q ρ hρ h / (n * ε ^ 2)) ∧
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] (p : FinDist Ot) (h : Ot → ℝ),
      recordSecondMoment p h - recordVariance p h = (p.expect h) ^ 2) ∧
    (∀ (Ot : Type) [Fintype Ot] [DecidableEq Ot] (m : ℕ)
      (p : FinDist Ot) (h : Ot → ℝ),
      (coincidingRecordLaw p).expect
          (fun ω : (Fin (m+1) → Ot) => (FinDist.avg h ω - p.expect h) ^ 2)
        = p.variance h) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Ot inst inst2 Dt E ρ hρ n hn h ε hε
    exact general_sample_confidence E ρ hρ hn h ε hε
  · intro Ot inst inst2 Dt m n E q ρ hρ hn h ε hε
    exact ensemble_sample_confidence E q ρ hρ hn h ε hε
  · intro Ot inst inst2 Dt m n E q ρ hρ hn h ε hε
    exact ensemble_sample_confidence_conservative E q ρ hρ hn h ε hε
  · intro Ot inst inst2 p h
    exact variance_second_moment_gap p h
  · intro Ot inst inst2 m p h
    exact coinciding_record_variance p h

/-- Collects the native campaign ledger formulas, result-dependent axis-table cost bound, and
quadratic sorting-comparison bound. -/
theorem thresholdGoal_endpoint :
    (∀ {K L : ℕ} (c : NativeCampaign K L) (m : NativeMachine),
      (nativeLedger c m).measurements = K * L ∧
      (nativeLedger c m).queries = 0 ∧
      (nativeLedger c m).axisDraws = (campaignFlatten c.records).length ∧
      (nativeLedger c m).tableReads = (campaignFlatten c.records).length ∧
      (nativeLedger c m).statisticReads = (campaignFlatten c.records).length ∧
      (nativeLedger c m).rationalAdditions = (campaignFlatten c.records).length ∧
      (nativeLedger c m).medianComparisons ≤ K * K ∧
      (nativeLedger c m).axisComparisons
        ≤ (campaignFlatten c.records).length
          * (nativeAxisTable.length + nativeAxisTable.length) ∧
      (nativeLedger c m).bitTime
        = (nativeLedger c m).axisDraws * m.axisDrawBits
          + (nativeLedger c m).axisComparisons * m.comparisonBits
          + (nativeLedger c m).tableReads * (m.addressBits + m.wordBits)
          + (nativeLedger c m).statisticReads * m.wordBits
          + (nativeLedger c m).rationalAdditions * m.additionBits
          + (nativeLedger c m).medianComparisons * m.comparisonBits ∧
      (nativeLedger c m).peakSpace
        = (campaignFlatten c.records).length * m.recordBits
          + K * m.wordBits + K * m.wordBits) ∧
    (∀ (history : List (Fin 3 × Fin 2)),
      nativeResultDependentAxisCost history ≤ history.length + nativeAxisTable.length) ∧
    (∀ (means : List ℚ),
      (rationalInsertionSortCounted means).2 ≤ means.length * means.length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K L c m
    exact native_run_ledger c m
  · intro history
    exact result_dependent_table_cost history
  · intro means
    exact order_statistic_cost means

end Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementStatistics
