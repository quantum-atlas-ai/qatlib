/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Checked updates and clocked prefixes

`checkedUpdate` retains the current candidate unless a strict improvement is found.
`budgetPrefixIndex` and `completedPrefixClock` evaluate the initial calls that finish within a
real-valued budget, while `finalCheckedIndex` evaluates the full trace.

The module proves that completed traces retain their result under a sufficient budget, that
minima survive further checked updates, and that a nonnegative clock has at least half its mass
below twice an upper bound on its mean. These facts support the interruption argument for
[DurrHoyer1996].

## Main statements

* `budgetPrefixIndex_complete`: identifies the prefix result when the entire trace fits.
* `interrupted_output_preserves`: preserves a completed minimum under a later candidate update.
* `nonnegative_clock_half_mass`: gives the half-mass clock estimate.

## References

* [Durr and Hoyer, 1996][DurrHoyer1996]
-/

open Qatlib.Concepts.AmplitudeSearch.Amplification.DistinctRankedTable

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

variable {I α : Type*} [LinearOrder α]

/-- Replace the current index by the candidate only when its table value is strictly smaller. -/
def checkedUpdate (T : I → α) (old candidate : I) : I :=
  if T candidate < T old then candidate else old

/-- A checked update cannot increase the current table value. -/
theorem checkedUpdate_nonincrease (T : I → α) (old candidate : I) :
    T (checkedUpdate T old candidate) ≤ T old := by
  unfold checkedUpdate
  split_ifs with h
  · exact h.le
  · exact le_rfl

/-- A checked update leaves a minimum index unchanged. -/
theorem checkedUpdate_preserves_minimum (T : I → α) (old candidate : I)
    (hmin : ∀ i, T old ≤ T i) :
    checkedUpdate T old candidate = old := by
  exact if_neg (not_lt_of_ge (hmin candidate))

/-- A list of candidate indices paired with real-valued call durations. -/
abbrev ClockedTrace (I : Type*) := List (I × ℝ)

/-- The total duration of a clocked trace. -/
noncomputable def traceClock : ClockedTrace I → ℝ
  | [] => 0
  | x :: xs => x.2 + traceClock xs

/-- The final index obtained by applying all checked updates in a clocked trace. -/
noncomputable def finalCheckedIndex (T : I → α) (initial : I) : ClockedTrace I → I
  | [] => initial
  | x :: xs => finalCheckedIndex T (checkedUpdate T initial x.1) xs

/-- The index obtained from the longest initial sequence of calls that can be completed within
the remaining budget. -/
noncomputable def budgetPrefixIndex (T : I → α) (initial : I) (budget : ℝ) :
    ClockedTrace I → I
  | [] => initial
  | x :: xs => if x.2 ≤ budget then
      budgetPrefixIndex T (checkedUpdate T initial x.1) (budget - x.2) xs else initial

/-- The total duration of the initial calls completed within the given budget. -/
noncomputable def completedPrefixClock (budget : ℝ) : ClockedTrace I → ℝ
  | [] => 0
  | x :: xs => if x.2 ≤ budget then
      x.2 + completedPrefixClock (budget - x.2) xs else 0

/-- A trace with nonnegative call durations has nonnegative total duration. -/
theorem traceClock_nonneg (xs : ClockedTrace I) (hc : ∀ x ∈ xs, 0 ≤ x.2) :
    0 ≤ traceClock xs := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    exact add_nonneg (hc x (by simp)) (ih (fun y hy => hc y (by simp [hy])))

/-- For a nonnegative budget and call durations, the completed prefix clock lies between zero
and the budget. -/
theorem completedPrefixClock_bounds (xs : ClockedTrace I) (budget : ℝ)
    (hb : 0 ≤ budget) (hc : ∀ x ∈ xs, 0 ≤ x.2) :
    0 ≤ completedPrefixClock budget xs ∧ completedPrefixClock budget xs ≤ budget := by
  induction xs generalizing budget with
  | nil => exact ⟨le_rfl, hb⟩
  | cons x xs ih =>
    rw [completedPrefixClock]
    split_ifs with hx
    · have ht := ih (budget - x.2) (sub_nonneg.mpr hx)
        (fun y hy => hc y (by simp [hy]))
      have hc0 := hc x (by simp)
      constructor <;> linarith [ht.1, ht.2]
    · exact ⟨le_rfl, hb⟩

/-- If the budget covers the entire trace and durations are nonnegative, the budgeted index
equals the final checked index. -/
theorem budgetPrefixIndex_complete (T : I → α) (xs : ClockedTrace I)
    (hc : ∀ x ∈ xs, 0 ≤ x.2) (initial : I) (budget : ℝ)
    (hb : traceClock xs ≤ budget) :
    budgetPrefixIndex T initial budget xs = finalCheckedIndex T initial xs := by
  induction xs generalizing initial budget with
  | nil => rfl
  | cons x xs ih =>
    have htail := traceClock_nonneg xs (fun y hy => hc y (by simp [hy]))
    have hx : x.2 ≤ budget := by simp only [traceClock] at hb; linarith
    rw [budgetPrefixIndex, if_pos hx, finalCheckedIndex]
    apply ih (fun y hy => hc y (by simp [hy]))
    simp only [traceClock] at hb
    linarith

/-- Once the completed trace yields a minimum within budget, a subsequent checked update
preserves the minimum-value property. -/
theorem interrupted_output_preserves (T : I → α) (xs : ClockedTrace I)
    (hc : ∀ x ∈ xs, 0 ≤ x.2) (initial candidate : I) (budget : ℝ)
    (hb : traceClock xs ≤ budget)
    (hmin : ∀ i, T (finalCheckedIndex T initial xs) ≤ T i) :
    ∀ i, T (checkedUpdate T (budgetPrefixIndex T initial budget xs) candidate) ≤ T i := by
  rw [budgetPrefixIndex_complete T xs hc initial budget hb,
    checkedUpdate_preserves_minimum T _ candidate hmin]
  exact hmin

/-- A normalized nonnegative mass function with nonnegative clock and mean at most positive `m`
assigns mass at least `1 / 2` to clocks at most `2 * m`. -/
theorem nonnegative_clock_half_mass {Ω : Type*} (mass clock : Ω → ℝ)
    (hmass : HasSum mass 1) (hmnn : ∀ x, 0 ≤ mass x) (hcnn : ∀ x, 0 ≤ clock x)
    (q m : ℝ) (hq : HasSum (fun x => mass x * clock x) q) (hqm : q ≤ m) (hm : 0 < m) :
    ∃ p : ℝ, HasSum (fun x => if clock x ≤ 2 * m then mass x else 0) p ∧
      1 / 2 ≤ p ∧ p ≤ 1 := by
  classical
  let good : Ω → ℝ := fun x => if clock x ≤ 2 * m then mass x else 0
  let bad : Ω → ℝ := fun x => if clock x ≤ 2 * m then 0 else mass x
  have hgood (x : Ω) : 0 ≤ good x ∧ good x ≤ mass x := by
    dsimp [good]; split_ifs <;> simp [hmnn x]
  have hbad (x : Ω) : 0 ≤ bad x ∧ bad x ≤ mass x := by
    dsimp [bad]; split_ifs <;> simp [hmnn x]
  have hg := Summable.of_nonneg_of_le (fun x => (hgood x).1)
    (fun x => (hgood x).2) hmass.summable
  have hb := Summable.of_nonneg_of_le (fun x => (hbad x).1)
    (fun x => (hbad x).2) hmass.summable
  have heq : (fun x => good x + bad x) = mass := by
    funext x; dsimp [good, bad]; split_ifs <;> ring
  have htotal : (∑' x, good x) + (∑' x, bad x) = 1 := by
    have h := hg.hasSum.add hb.hasSum
    rw [heq] at h
    exact h.unique hmass
  have hpoint (x : Ω) : (2 * m) * bad x ≤ mass x * clock x := by
    dsimp [bad]
    split_ifs with hx
    · simpa using mul_nonneg (hmnn x) (hcnn x)
    · have h := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hx)) (hmnn x)
      nlinarith
  have hwb := hb.hasSum.mul_left (2 * m)
  have hbound := Summable.tsum_le_tsum hpoint hwb.summable hq.summable
  rw [hwb.tsum_eq, hq.tsum_eq] at hbound
  refine ⟨_, hg.hasSum, ?_, ?_⟩
  · nlinarith
  · have hbn : 0 ≤ (∑' x, bad x) := tsum_nonneg (fun x => (hbad x).1)
    linarith

end Qatlib.Concepts.AmplitudeSearch.Amplification
