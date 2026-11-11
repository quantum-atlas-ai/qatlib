/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.Section3StrictImprovementSubgoalStat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# A certified strict improvement from Grover restarts

Proves `section3StrictImprovementSubgoal` using rational bounds for the search angle and
alternating Taylor bounds for sine. The numerical window for the 596-iteration success
probability yields a strict improvement over the 804-iteration benchmark. For the quantum-search
analysis, see [BoyerEtAl1998].

## Main statements

* `improvementSin_window`: The squared sine at angle `1193 * Real.arcsin (1 / 1024)` lies
  strictly between 0.8441 and 0.8443.
* `section3StrictImprovementSubgoal`: Establishes `Section3StrictImprovementSubgoal`, the
  certified strict improvement of a 596-iteration restart strategy over the 804-iteration
  benchmark.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.PaidRestart

open Qatlib.Concepts.SearchStopping.KnownCount Finset Filter

/-- For `0 ≤ x ≤ 5 / 4`, the sequence `x ^ (2 * n + d) / (2 * n + d)!` is antitone. -/
private theorem improvementTerms_antitone (x : ℝ) (hx : 0 ≤ x) (hu : x ≤ 5 / 4) (d : ℕ) :
    Antitone (fun n : ℕ => x ^ (2 * n + d) / ((2 * n + d).factorial : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro n
  let m := 2 * n + d
  have he : 2 * (n + 1) + d = m + 2 := by dsimp [m]; omega
  have hf : ((m + 2).factorial : ℝ) =
      ((m : ℝ) + 2) * ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hsq : x ^ 2 ≤ 2 := by nlinarith
  have hm : (2 : ℝ) ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [sq_nonneg (m : ℝ)]
  have hfp : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hfp2 : (0 : ℝ) < ((m + 2).factorial : ℝ) := by positivity
  change x ^ (2 * (n + 1) + d) / _ ≤ x ^ m / _
  rw [he, pow_add, div_le_div_iff₀ hfp2 hfp]
  calc
    x ^ m * x ^ 2 * (m.factorial : ℝ) ≤
        x ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (m.factorial : ℝ) := by
      gcongr
      exact hsq.trans hm
    _ = x ^ m * ((m + 2).factorial : ℝ) := by rw [hf]; ring

/-- For `0 ≤ x ≤ 5 / 4`, the sine Taylor sums with `2 * k` and `2 * k + 1` terms bound `Real.sin
x` from below and above, respectively. -/
private theorem improvementSin_bounds (x : ℝ) (hx : 0 ≤ x) (hu : x ≤ 5 / 4) (k : ℕ) :
    (∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))
      ≤ Real.sin x ∧ Real.sin x ≤
    ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ) := by
  have ht := (Real.hasSum_sin x).tendsto_sum_nat
  have ha := improvementTerms_antitone x hx hu 1
  simpa only [mul_div_assoc] using
    And.intro (ha.alternating_series_le_tendsto (by simpa only [mul_div_assoc] using ht) k)
      (ha.tendsto_le_alternating_series (by simpa only [mul_div_assoc] using ht) k)

/-- The angle `Real.arcsin (1 / 1024)` lies strictly between `1 / 1024` and `1 / 1024 + 1 /
536870912`. -/
private theorem improvementAngle_bounds :
    (1 / 1024 : ℝ) < Real.arcsin (1 / 1024) ∧
      Real.arcsin (1 / 1024) < 1 / 1024 + 1 / 536870912 := by
  have hp : 0 < Real.arcsin (1 / 1024 : ℝ) := Real.arcsin_pos.mpr (by norm_num)
  have hs : Real.sin (Real.arcsin (1 / 1024 : ℝ)) = 1 / 1024 :=
    Real.sin_arcsin (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · linarith [Real.sin_lt hp]
  · have ht := Real.sin_gt_sub_cube
      (by norm_num : (0 : ℝ) < 1 / 1024 + 1 / 536870912)
    have hst : Real.sin (Real.arcsin (1 / 1024 : ℝ)) <
        Real.sin (1 / 1024 + 1 / 536870912 : ℝ) := by rw [hs]; norm_num at ht ⊢; linarith
    exact (Real.strictMonoOn_sin.lt_iff_lt (Real.arcsin_mem_Icc (1 / 1024))
      (by constructor <;> linarith [Real.pi_gt_d2])).mp hst

/-- The squared sine at angle `1193 * Real.arcsin (1 / 1024)` lies strictly between 0.8441 and
0.8443. -/
private theorem improvementSin_window :
    (8441 / 10000 : ℝ) < Real.sin (1193 * Real.arcsin (1 / 1024)) ^ 2 ∧
      Real.sin (1193 * Real.arcsin (1 / 1024)) ^ 2 < 8443 / 10000 := by
  have ht := improvementAngle_bounds
  have hslo := improvementSin_bounds (1193 / 1024 : ℝ) (by norm_num) (by norm_num) 2
  have hshi := improvementSin_bounds (1193 * (1 / 1024 + 1 / 536870912) : ℝ)
    (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hslo hshi
  have hl : (91879 / 100000 : ℝ) < Real.sin (1193 / 1024 : ℝ) := by linarith [hslo.1]
  have hu : Real.sin (1193 * (1 / 1024 + 1 / 536870912) : ℝ) < 91881 / 100000 := by
    linarith [hshi.2]
  have hmem : 1193 * Real.arcsin (1 / 1024 : ℝ) ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_gt_d2, ht.1, ht.2]
  have hmlo : Real.sin (1193 / 1024 : ℝ) ≤ Real.sin (1193 * Real.arcsin (1 / 1024 : ℝ)) := by
    apply Real.strictMonoOn_sin.monotoneOn
    · constructor <;> linarith [Real.pi_gt_d2]
    · exact hmem
    · linarith [ht.1]
  have hmhi : Real.sin (1193 * Real.arcsin (1 / 1024 : ℝ)) ≤
      Real.sin (1193 * (1 / 1024 + 1 / 536870912) : ℝ) := by
    apply Real.strictMonoOn_sin.monotoneOn
    · exact hmem
    · constructor <;> linarith [Real.pi_gt_d2]
    · linarith [ht.2]
  have hsl : (91879 / 100000 : ℝ) < Real.sin (1193 * Real.arcsin (1 / 1024 : ℝ)) := hl.trans_le hmlo
  have hsu : Real.sin (1193 * Real.arcsin (1 / 1024 : ℝ)) < (91881 / 100000 : ℝ) := hmhi.trans_lt hu
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hsl)
      (by linarith : 0 < Real.sin (1193 * Real.arcsin (1 / 1024 : ℝ)) + 91879 / 100000)]
  · nlinarith [mul_pos (sub_pos.mpr hsu)
      (by linarith : 0 < (91881 / 100000 : ℝ) + Real.sin (1193 * Real.arcsin (1 / 1024 : ℝ)))]

/-- Establishes `Section3StrictImprovementSubgoal`, the certified strict improvement of a
596-iteration restart strategy over the 804-iteration benchmark. -/
theorem section3StrictImprovementSubgoal : Section3StrictImprovementSubgoal := by
  intro I _ _ hN A hA
  have ht := improvementAngle_bounds
  have hp : 0 < Real.arcsin (1 / 1024 : ℝ) := by linarith [ht.1]
  have hd : 0 < 4 * Real.arcsin (1 / 1024 : ℝ) := by positivity
  have hf : Nat.floor (Real.pi / (4 * Real.arcsin (1 / 1024 : ℝ))) = 804 := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor
    · rw [le_div_iff₀ hd]
      norm_num
      linarith [Real.pi_gt_d4, ht.2]
    · rw [div_lt_iff₀ hd]
      norm_num
      linarith [Real.pi_lt_d4, ht.1]
  have hs : Real.sin (Real.arcsin (1 / 1024 : ℝ)) = 1 / 1024 :=
    Real.sin_arcsin (by norm_num) (by norm_num)
  have hc : Real.cos (Real.arcsin (1 / 1024 : ℝ)) ≠ 0 := by
    have h := Real.sin_sq_add_cos_sq (Real.arcsin (1 / 1024 : ℝ))
    rw [hs] at h
    intro hh
    rw [hh] at h
    norm_num at h
  have hprob : MeasureProb (GroverState A 596) A =
      Real.sin (1193 * Real.arcsin (1 / 1024 : ℝ)) ^ 2 := by
    have h := measureProb_groverState (by rw [hN]; norm_num) A
      (Real.arcsin (1 / 1024 : ℝ))
      (by rw [hs, hA, hN]; norm_num)
      (by rw [hs]; norm_num) hc 596
    norm_num at h
    exact h
  have hw := improvementSin_window
  rw [← hprob] at hw
  have hpp : 0 < MeasureProb (GroverState A 596) A := by linarith [hw.1]
  refine ⟨hf, hw.1, hw.2, ?_, ?_⟩
  · rw [div_lt_iff₀ hpp]
    linarith [hw.1]
  · rw [lt_div_iff₀ hpp]
    linarith [hw.2]

end Qatlib.Concepts.SearchStopping.PaidRestart
