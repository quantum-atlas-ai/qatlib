/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3SourceFamilyTigh
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Concepts.AmplitudeSearch.Amplification.FinalRemarksAmplificationAqua
import Qatlib.Concepts.AmplitudeSearch.Amplification.ChargedClock

/-!
# Search and minimum bounds for string matching

This module supplies the search and minimum estimates used for Corollary 1 of [RameshVinay2000].
The results `corollary1_search` and `corollary1_minimum` combine the BBHT terminal law and
amplified minimum search guarantees with an explicit majority repetition count, yielding scalar
failure and logarithmic cost bounds.

## Main statements

* `bbht_uniform_contract`: Gives normalized uniform marked output and an expected Boolean query
  bound.
* `corollary1_search`: Combines uniform search output with majority failure and cost estimates.
* `corollary1_minimum`: Combines amplified minimum success with majority failure and cost
  estimates.

## References

* [Ramesh and Vinay, 2000][RameshVinay2000]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.QueryComplexity.Amplification

namespace Qatlib.Papers.QStringMatch00.MainResults.Corollary1

/-- The natural ceiling of 9 log(8S), used as the majority repetition parameter. -/
def majorityReps (S : ℝ) : ℕ := Nat.ceil (9 * Real.log (8 * S))

/-- The logarithm of 8/9 is at most −1/9. -/
lemma log_eight_ninths_le : Real.log (8 / 9 : ℝ) ≤ -(1 / 9 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8 / 9)
  linarith

/-- For S ≥ 1, raising 8/9 to the majority repetition parameter gives at most 1/(8S). -/
lemma majorityReps_pow_bound (S : ℝ) (hS : 1 ≤ S) :
    (8 / 9 : ℝ) ^ majorityReps S ≤ 1 / (8 * S) := by
  have hS8 : (0 : ℝ) < 8 * S := by linarith
  have hceil : 9 * Real.log (8 * S) ≤ (majorityReps S : ℝ) := Nat.le_ceil _
  have hr_nonneg : (0 : ℝ) ≤ (majorityReps S : ℝ) := Nat.cast_nonneg _
  have hmul : (majorityReps S : ℝ) * Real.log (8 / 9) ≤ (majorityReps S : ℝ) * (-(1 / 9)) :=
    mul_le_mul_of_nonneg_left log_eight_ninths_le hr_nonneg
  have hkey : (majorityReps S : ℝ) * Real.log (8 / 9) ≤ -(Real.log (8 * S)) := by
    nlinarith
  calc (8 / 9 : ℝ) ^ majorityReps S
      = Real.exp ((majorityReps S : ℝ) * Real.log (8 / 9)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 8 / 9)]
    _ ≤ Real.exp (-(Real.log (8 * S))) := Real.exp_le_exp.mpr hkey
    _ = 1 / (8 * S) := by
        rw [Real.exp_neg, Real.exp_log hS8, one_div]

/-- For S ≥ 1, the odd majority size 2 `majorityReps` S + 1 is at most 21(log(8S) + 1). -/
lemma majorityReps_linear (S : ℝ) (hS : 1 ≤ S) :
    2 * (majorityReps S : ℝ) + 1 ≤ 21 * (Real.log (8 * S) + 1) := by
  have hlog : 0 ≤ Real.log (8 * S) := Real.log_nonneg (by linarith)
  have hnonneg : (0 : ℝ) ≤ 9 * Real.log (8 * S) := by linarith
  have hlt : (majorityReps S : ℝ) < 9 * Real.log (8 * S) + 1 :=
    Nat.ceil_lt_add_one hnonneg
  nlinarith

/-- For a nonempty marked set, the BBHT terminal mass sums to one, its output is uniform on
marked addresses, and its expected Boolean query count is at most (29/2)√(N/|A|). -/
theorem bbht_uniform_contract
    (N : ℕ) (hN : 0 < N) (A : Finset (Fin N)) (hA : 0 < A.card) :
    HasSum (TerminalMass A (SourceSizes N (6 / 5))) 1 ∧
      (∀ i : Fin N, HasSum
        (fun x : TerminalTrace (Fin N) (SourceSizes N (6 / 5)) =>
          if TerminalOutput x = i then TerminalMass A (SourceSizes N (6 / 5)) x else 0)
        (if i ∈ A then 1 / (A.card : ℝ) else 0)) ∧
      (∃ q : ℝ, HasSum
        (fun x : TerminalTrace (Fin N) (SourceSizes N (6 / 5)) =>
          TerminalMass A (SourceSizes N (6 / 5)) x *
            (TerminalBooleanQueries (SourceSizes N (6 / 5)) x : ℝ)) q ∧
        0 ≤ q ∧ q ≤ (29 / 2 : ℝ) * Real.sqrt ((N : ℝ) / A.card)) := by
  have h := theorem3SourceFamily (I := Fin N) (by simpa using! hN)
    (6 / 5 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨hgoal, _hbudget, _hempty, _htimeout⟩ := h
  obtain ⟨hmass, _hsupp, huniform, _hcost, hbool, _hlookup⟩ := hgoal A hA
  obtain ⟨q, hq, hq0, hqb⟩ := hbool
  rw [Fintype.card_fin] at hmass huniform hq hqb
  have hconst : (1 + 3 * ((6 / 5 : ℝ) / 4 *
      (1 / ((6 / 5 : ℝ) - 1) + 4 / (4 - 3 * (6 / 5 : ℝ))))) = 29 / 2 := by norm_num
  refine ⟨hmass, huniform, q, hq, hq0, ?_⟩
  rw [hconst] at hqb
  simpa using! hqb

/-- For t marked items among N addresses, gives uniform marked terminal output and a repetition
count whose scalar majority error is at most 1/8, cost is at most 4800Q(log(64Q) + 1), and
combined success lower bound is at least 3/4, where Q = (29/2)√(N/t). See [RameshVinay2000]. -/
theorem corollary1_search
    (N t : ℕ) (hN : 0 < N) (ht : 1 ≤ t) (htN : t ≤ N)
    (A : Finset (Fin N)) (hA : A.card = t) :
    let Q : ℝ := (29 / 2) * Real.sqrt ((N : ℝ) / t)
    ∃ r : ℕ,
      0 < Q ∧
      (∀ i : Fin N, HasSum
        (fun x : TerminalTrace (Fin N) (SourceSizes N (6 / 5)) =>
          if TerminalOutput x = i then TerminalMass A (SourceSizes N (6 / 5)) x else 0)
        (if i ∈ A then 1 / (t : ℝ) else 0)) ∧
      (8 * Q) * (8 / 9 : ℝ) ^ r ≤ 1 / 8 ∧
      (2 * (r : ℝ) + 1) * (8 * Q) ≤ 4800 * Q * (Real.log (64 * Q) + 1) ∧
      (3 / 4 : ℝ) ≤ 1 - (1 / 8 + (8 * Q) * (8 / 9 : ℝ) ^ r) := by
  (try dsimp only)
  set Q : ℝ := (29 / 2) * Real.sqrt ((N : ℝ) / t) with hQdef
  have ht0 : 0 < A.card := by omega
  have hcontract := bbht_uniform_contract N hN A ht0

  have huniform : ∀ i : Fin N, HasSum
      (fun x : TerminalTrace (Fin N) (SourceSizes N (6 / 5)) =>
        if TerminalOutput x = i then TerminalMass A (SourceSizes N (6 / 5)) x else 0)
      (if i ∈ A then 1 / (t : ℝ) else 0) := by
    intro i
    have hi := hcontract.2.1 i
    simpa [hA] using! hi

  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hratio : (1 : ℝ) ≤ (N : ℝ) / t := by
    rw [le_div_iff₀ htR]
    have h1 : (t : ℝ) ≤ N := by exact_mod_cast htN
    simpa using! h1
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((N : ℝ) / t) := Real.one_le_sqrt.mpr hratio
  have hQ1 : (1 : ℝ) ≤ Q := by
    have h29 : (1 : ℝ) ≤ 29 / 2 := by norm_num
    nlinarith [Real.sqrt_nonneg ((N : ℝ) / t), hsqrt, h29]
  have hQ0 : (0 : ℝ) < Q := by linarith
  refine ⟨majorityReps (8 * Q), hQ0, huniform, ?_, ?_, ?_⟩
  · have hS : (1 : ℝ) ≤ 8 * Q := by linarith
    have hb := majorityReps_pow_bound (8 * Q) hS

    have hpos : (0 : ℝ) < 8 * Q := by linarith
    have : (8 * Q) * (8 / 9 : ℝ) ^ majorityReps (8 * Q) ≤ (8 * Q) * (1 / (8 * (8 * Q))) :=
      mul_le_mul_of_nonneg_left hb hpos.le
    have he : (8 * Q) * (1 / (8 * (8 * Q))) = 1 / 8 := by
      field_simp
    linarith [this, he.le, he.ge]
  · have hS : (1 : ℝ) ≤ 8 * Q := by linarith
    have hlin := majorityReps_linear (8 * Q) hS
    have hlog : Real.log (8 * (8 * Q)) = Real.log (64 * Q) := by
      congr 1
      ring
    have hpos8Q : (0 : ℝ) ≤ 8 * Q := by linarith
    have hstep : (2 * (majorityReps (8 * Q) : ℝ) + 1) * (8 * Q)
        ≤ 21 * (Real.log (8 * (8 * Q)) + 1) * (8 * Q) :=
      mul_le_mul_of_nonneg_right hlin hpos8Q
    rw [hlog] at hstep
    have hlog0 : 0 ≤ Real.log (64 * Q) + 1 := by
      have : 0 ≤ Real.log (64 * Q) := Real.log_nonneg (by nlinarith)
      linarith
    nlinarith [hstep, hlog0, hpos8Q]
  · have hS : (1 : ℝ) ≤ 8 * Q := by linarith
    have hb := majorityReps_pow_bound (8 * Q) hS
    have hpos : (0 : ℝ) < 8 * Q := by linarith
    have hfail : (8 * Q) * (8 / 9 : ℝ) ^ majorityReps (8 * Q) ≤ 1 / 8 := by
      have hmul := mul_le_mul_of_nonneg_left hb hpos.le
      have he : (8 * Q) * (1 / (8 * (8 * Q))) = 1 / 8 := by
        field_simp
      rwa [he] at hmul
    linarith

/-- Fourfold amplified minimum search returns a minimum with probability at least 15/16. -/
theorem dh_minimum_success
    (N : ℕ) (hN : 0 < N) (α : Type) [LinearOrder α] (T : Fin N → α) :
    ENNReal.ofReal (15 / 16 : ℝ) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (amplifiedMinimumPMF T hN 4) (fun x => ∀ j, T x.1 ≤ T j) := by
  have h := finalRemarksAmplification N hN α T 4 (by norm_num)
  have he : (1 - (1 / 2 : ℝ) ^ 4) = 15 / 16 := by norm_num
  rw [he] at h
  exact h.1

/-- Four charged minimum search budgets are at most 4(4(45/2 + (112/5)/(log 2)²) + 1)√N. -/
theorem dh_minimum_budget (N : ℕ) (hN : 0 < N) :
    (4 * (chargedBudget N) : ℝ) ≤
      4 * (4 * ((45 / 2 : ℝ) + (112 / 5 : ℝ) / (Real.log 2) ^ 2) + 1) * Real.sqrt N := by
  have h := chargedBudget_le_sqrt N hN
  have hs : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- Gives a repetition count combining minimum success at least 15/16 with scalar majority error
at most 1/8, the stated logarithmic cost bound, and combined success lower bound at least
3/4. See [RameshVinay2000]. -/
theorem corollary1_minimum
    (N : ℕ) (hN : 0 < N) (α : Type) [LinearOrder α] (T : Fin N → α) :
    ∃ r : ℕ,
      let C : ℝ := 4 * ((45 / 2 : ℝ) + (112 / 5 : ℝ) / (Real.log 2) ^ 2) + 1
      let Q : ℝ := 4 * C * Real.sqrt N
      0 < Q ∧
      ENNReal.ofReal (15 / 16 : ℝ) ≤
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
          (amplifiedMinimumPMF T hN 4) (fun x => ∀ j, T x.1 ≤ T j) ∧
      Q * (8 / 9 : ℝ) ^ r ≤ 1 / 8 ∧
      (2 * (r : ℝ) + 1) * Q ≤ 4800 * Q * (Real.log (8 * Q) + 1) ∧
      (3 / 4 : ℝ) ≤ 1 - (1 / 16 + Q * (8 / 9 : ℝ) ^ r) := by
  (try dsimp only)
  set C : ℝ := 4 * ((45 / 2 : ℝ) + (112 / 5 : ℝ) / (Real.log 2) ^ 2) + 1 with hCdef
  set Q : ℝ := 4 * C * Real.sqrt N with hQdef

  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hNR
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC : (1 : ℝ) ≤ C := by
    have h0 : (0 : ℝ) < (112 / 5 : ℝ) / (Real.log 2) ^ 2 := by
      apply div_pos (by norm_num)
      exact pow_pos hlog2 2
    nlinarith [h0]
  have hQ1 : (1 : ℝ) ≤ Q := by
    have hC0 : (0 : ℝ) ≤ C := by linarith
    nlinarith [Real.sqrt_nonneg (N : ℝ), hsqrt, hC, hC0]
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hfail : Q * (8 / 9 : ℝ) ^ majorityReps Q ≤ 1 / 8 := by
    have hb := majorityReps_pow_bound Q hQ1
    have hmul := mul_le_mul_of_nonneg_left hb hQ0.le
    have he : Q * (1 / (8 * Q)) = 1 / 8 := by field_simp
    rwa [he] at hmul
  refine ⟨majorityReps Q, hQ0, dh_minimum_success N hN α T, hfail, ?_, ?_⟩
  · have hlin := majorityReps_linear Q hQ1
    have hpos : (0 : ℝ) ≤ Q := hQ0.le
    have hstep := mul_le_mul_of_nonneg_right hlin hpos
    have hlog0 : 0 ≤ Real.log (8 * Q) + 1 := by
      have : 0 ≤ Real.log (8 * Q) := Real.log_nonneg (by linarith)
      linarith
    nlinarith [hstep, hlog0, hpos]
  · linarith

end Qatlib.Papers.QStringMatch00.MainResults.Corollary1
