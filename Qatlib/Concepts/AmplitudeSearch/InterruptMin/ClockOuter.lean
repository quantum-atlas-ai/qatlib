/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.RunMoment

/-!
# Completion mass for clocked rank processes

This module defines `completion` as the mass of finite rank-process runs whose clock fits a real
budget. It proves a first-call recurrence, a probability upper bound, and a
uniform-initialization formula.

These formulas support the clocked analysis of minimum finding [DurrHoyer1996].

## Main statements

* `completion_step`: At a positive starting rank, completion mass splits over first-call
  outcomes fitting the budget and continuation with the residual budget.
* `initial_completion`: The uniformly initialized completion mass equals the uniform average of
  completion masses from the initial ranks.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open scoped Classical BigOperators ENNReal

/-- An equivalence separating the empty list from lists with a head and tail. -/
private def listCases (Ω : Type) : List Ω ≃ Unit ⊕ (Ω × List Ω) where
  toFun | [] => .inl () | x::xs => .inr (x,xs)
  invFun | .inl _ => [] | .inr (x,xs) => x::xs
  left_inv xs := by cases xs <;> rfl
  right_inv x := by
    rcases x with u | ⟨x,xs⟩
    · cases u; rfl
    · rfl

/-- Splits a nonnegative sum over lists into the empty-list term and the sum over heads and
tails. -/
theorem list_tsum {Ω : Type} (f : List Ω → ℝ≥0∞) :
    (∑' xs, f xs) = f [] + ∑' x, ∑' xs, f (x::xs) := by
  let e := listCases Ω
  calc
    _ = ∑' y : Unit ⊕ (Ω × List Ω), f (e.symm y) := (e.symm.tsum_eq f).symm
    _ = (∑' _u : Unit, f []) + ∑' p : Ω × List Ω, f (p.1::p.2) :=
      ENNReal.summable.tsum_sum ENNReal.summable
    _ = f [] + ∑' p : Ω × List Ω, f (p.1::p.2) := by simp
    _ = _ := congrArg (fun q : ℝ≥0∞ => f [] + q) (ENNReal.tsum_prod (f := fun x xs => f (x::xs)))

variable {N : ℕ} {Ω : Type}

/-- The total mass of rank-process runs whose accumulated clock is at most the budget. -/
def completion (law : RankedCallLaw N Ω) (skip : RankSkip N) (t : ℕ) (budget : ℝ) : ℝ≥0∞ :=
  ∑' xs : List Ω, if law.runClock xs ≤ budget then ENNReal.ofReal (law.runMass skip t xs) else 0

/-- At rank zero, completion mass is one for a nonnegative budget and zero for a negative
budget. -/
theorem completion_zero (law : RankedCallLaw N Ω) (skip : RankSkip N) (budget : ℝ) :
    completion law skip 0 budget = if 0 ≤ budget then 1 else 0 := by
  unfold completion
  have he (xs : List Ω) : (if law.runClock xs ≤ budget then ENNReal.ofReal (law.runMass skip 0 xs) else 0) =
      if xs = [] then (if 0 ≤ budget then 1 else 0) else 0 := by
    cases xs <;> simp [RankedCallLaw.runClock,RankedCallLaw.runMass]
  simp_rw [he]
  simp

/-- A negative budget gives zero completion mass. -/
theorem completion_neg (law : RankedCallLaw N Ω) (skip : RankSkip N) (t : ℕ)
    (budget : ℝ) (hb : budget < 0) : completion law skip t budget = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro xs
  have hc : ¬law.runClock xs ≤ budget := by have hn := law.runClock_nonneg xs; linarith
  rw [if_neg hc]

/-- For a starting rank below `N`, completion mass is at most one. -/
theorem completion_le_one (law : RankedCallLaw N Ω) (skip : RankSkip N) (t : ℕ)
    (ht : t < N) (budget : ℝ) : completion law skip t budget ≤ 1 := by
  calc
    _ ≤ ∑' xs : List Ω, ENNReal.ofReal (law.runMass skip t xs) := by
      apply ENNReal.tsum_le_tsum
      intro xs
      split_ifs
      · exact le_rfl
      · exact zero_le
    _ = ENNReal.ofReal (∑' xs : List Ω, law.runMass skip t xs) :=
      (ENNReal.ofReal_tsum_of_nonneg (law.runMass_nonneg skip t ht)
        (law.runMass_normalized skip t ht).summable).symm
    _ = 1 := by rw [(law.runMass_normalized skip t ht).tsum_eq,ENNReal.ofReal_one]

/-- At a positive starting rank, completion mass splits over first-call outcomes fitting the
budget and continuation with the residual budget. -/
theorem completion_step (law : RankedCallLaw N Ω) (skip : RankSkip N) (t : ℕ)
    (ht : 0 < t) (htN : t < N) (budget : ℝ) :
    completion law skip t budget =
      ∑' x : Ω, if law.duration x ≤ budget then ENNReal.ofReal (law.mass t x) *
        completion law skip (skip.next (law.outputRank x)) (budget-law.duration x) else 0 := by
  unfold completion
  rw [list_tsum]
  have hn : (if law.runClock [] ≤ budget then ENNReal.ofReal (law.runMass skip t []) else 0) = 0 := by
    simp [RankedCallLaw.runMass,Nat.ne_of_gt ht]
  rw [hn,zero_add]
  apply tsum_congr
  intro x
  by_cases hc : law.duration x ≤ budget
  · rw [if_pos hc,← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro xs
    by_cases hx : (law.outputRank x).val < t
    · have hclock : law.runClock (x::xs) ≤ budget ↔ law.runClock xs ≤ budget-law.duration x := by
        rw [RankedCallLaw.runClock]
        constructor <;> intro h <;> linarith
      simp only [RankedCallLaw.runMass,if_neg (Nat.ne_of_gt ht),if_pos hx,hclock]
      split_ifs
      · rw [ENNReal.ofReal_mul (law.mass_nonneg t htN x)]
      · simp
    · have hz := law.lower_support t ht htN x hx
      simp [RankedCallLaw.runMass,Nat.ne_of_gt ht,hx,hz]
  · rw [if_neg hc]
    apply ENNReal.tsum_eq_zero.mpr
    intro xs
    have hclock : ¬law.runClock (x::xs) ≤ budget := by
      rw [RankedCallLaw.runClock]
      have hn := law.runClock_nonneg xs
      linarith
    rw [if_neg hclock]

/-- The uniformly initialized completion mass equals the uniform average of completion masses
from the initial ranks. -/
theorem initial_completion (law : RankedCallLaw N Ω) (skip : RankSkip N) (hN : 0 < N) (budget : ℝ) :
    ENNReal.ofReal (∑' x : Fin N × List Ω,
      if law.runClock x.2 ≤ budget then law.initialMass skip x else 0) =
      ∑' i : Fin N, ENNReal.ofReal ((1:ℝ)/N) * completion law skip (skip.next i) budget := by
  let f : Fin N × List Ω → ℝ :=
    fun x => if law.runClock x.2 ≤ budget then law.initialMass skip x else 0
  have hm := law.initialMass_normalized skip hN
  have hn (x : Fin N × List Ω) : 0 ≤ f x := by
    dsimp [f]
    split_ifs
    · exact hm.2 x
    · exact le_rfl
  have hle (x : Fin N × List Ω) : f x ≤ law.initialMass skip x := by
    dsimp [f]
    split_ifs
    · exact le_rfl
    · exact hm.2 x
  have hs : Summable f := Summable.of_nonneg_of_le hn hle hm.1.summable
  change ENNReal.ofReal (∑' x, f x) = _
  rw [ENNReal.ofReal_tsum_of_nonneg hn hs]
  calc
    _ = ∑' i : Fin N, ∑' xs : List Ω, ENNReal.ofReal (f (i,xs)) := ENNReal.tsum_prod'
    _ = _ := by
      apply tsum_congr
      intro i
      unfold completion
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro xs
      dsimp [f,RankedCallLaw.initialMass]
      split_ifs
      · rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1:ℝ)/(N:ℝ))]
        congr 1
        ring
      · simp

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
