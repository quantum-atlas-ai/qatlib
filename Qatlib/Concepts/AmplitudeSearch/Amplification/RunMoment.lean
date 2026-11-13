/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.DiscreteRun

/-!
# First moments of ranked search runs

The clock `RankedCallLaw.runClock` adds the durations of calls in a completed run. Given a bound
on each call moment and a potential satisfying the threshold recurrence, this module bounds the
total clock moment and its average over initial ranks, as required for the minimum-finding
runtime analysis [DurrHoyer1996].

## Main statements

* `RankedCallLaw.runClock_nonneg`: proves that every accumulated run clock is nonnegative.
* `RankedCallLaw.runClock_moment`: bounds the moment from a fixed threshold by a potential.
* `RankedCallLaw.initialClock_moment`: bounds the moment with uniform initialization.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
namespace RankedCallLaw

variable {N : ℕ} {Ω : Type}

/-- The sum of the durations assigned by the ranked call law to the outcomes in a run. -/
noncomputable def runClock (law : RankedCallLaw N Ω) : List Ω → ℝ
  | [] => 0
  | x :: xs => law.duration x + runClock law xs

/-- The accumulated clock of every run is nonnegative. -/
theorem runClock_nonneg (law : RankedCallLaw N Ω) (xs : List Ω) : 0 ≤ law.runClock xs := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact add_nonneg (law.duration_nonneg x) ih

/-- If call moments are bounded by `D` and `V` satisfies the stated threshold recurrence with `V
0 = 0`, the total run-clock moment from `t < N` exists and lies between zero and `V t`. -/
theorem runClock_moment (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (D V : ℕ → ℝ) (hV0 : V 0 = 0)
    (hcall : ∀ t, 0 < t → t < N → ∃ q,
      HasSum (fun x => law.mass t x * law.duration x) q ∧ q ≤ D t)
    (hstep : ∀ t, 0 < t → t < N →
      D t + (∑ i : Fin N, if i.val < t then V (skip.next i) else 0) / (t : ℝ) ≤ V t)
    (t : ℕ) (htN : t < N) :
    ∃ q, HasSum (fun xs => law.runMass skip t xs * law.runClock xs) q ∧
      0 ≤ q ∧ q ≤ V t := by
  classical
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero =>
      have hz : (fun xs : List Ω => law.runMass skip 0 xs * law.runClock xs) = fun _ => 0 := by
        funext xs
        cases xs <;> simp [runMass, runClock]
      refine ⟨0, ?_, le_rfl, ?_⟩
      · rw [hz]; exact hasSum_zero
      · exact le_of_eq hV0.symm
    | succ t =>
      let E : ℕ → ℝ := fun u => ∑' xs : List Ω, law.runMass skip u xs * law.runClock xs
      have hE (u : ℕ) (hu : u < t + 1) :
          HasSum (fun xs => law.runMass skip u xs * law.runClock xs) (E u) ∧
            0 ≤ E u ∧ E u ≤ V u := by
        obtain ⟨q, hq, hqnn, hqb⟩ := ih u hu (lt_trans hu htN)
        have heq : E u = q := hq.tsum_eq
        rw [heq]
        exact ⟨hq, hqnn, hqb⟩
      let g : Ω → ℝ := fun x => law.mass (t + 1) x *
        (law.duration x + E (skip.next (law.outputRank x)))
      have hfib (x : Ω) :
          HasSum (fun xs => law.runMass skip (t + 1) (x :: xs) * law.runClock (x :: xs))
            (g x) := by
        by_cases hx : (law.outputRank x).val < t + 1
        · have hnext : skip.next (law.outputRank x) < t + 1 := lt_of_le_of_lt (skip.le_rank _) hx
          have hnorm := law.runMass_normalized skip _ (lt_trans hnext htN)
          have hmean := (hE _ hnext).1
          have h := (hnorm.mul_left (law.mass (t + 1) x * law.duration x)).add
            (hmean.mul_left (law.mass (t + 1) x))
          have hfun :
              (fun xs => law.runMass skip (t + 1) (x :: xs) * law.runClock (x :: xs)) =
              (fun xs => law.mass (t + 1) x * law.duration x *
                law.runMass skip (skip.next (law.outputRank x)) xs +
                law.mass (t + 1) x * (law.runMass skip (skip.next (law.outputRank x)) xs *
                  law.runClock xs)) := by
            funext xs
            simp only [runMass, if_neg (by omega : ¬ t + 1 = 0), if_pos hx, runClock]
            ring
          rw [hfun]
          have hg : g x = law.mass (t + 1) x * law.duration x * 1 +
              law.mass (t + 1) x * E (skip.next (law.outputRank x)) := by dsimp [g]; ring
          rw [hg]
          exact h
        · have hz : law.mass (t + 1) x = 0 := law.lower_support _ (by omega) htN x hx
          have hg : g x = 0 := by simp [g, hz]
          rw [hg]
          simpa only [runMass, if_neg (by omega : ¬ t + 1 = 0), if_neg hx, zero_mul]
            using hasSum_zero
      obtain ⟨qc, hqc, hqcb⟩ := hcall (t + 1) (by omega) htN
      have hcont := law.continuation_finite (t + 1) (by omega) htN (fun i => E (skip.next i))
      have hrows : HasSum g
          (qc + (∑ i : Fin N, if i.val < t + 1 then E (skip.next i) else 0) / (t + 1 : ℝ)) := by
        have h := hqc.add hcont
        have heq : g = (fun x => law.mass (t + 1) x * law.duration x +
            law.mass (t + 1) x * E (skip.next (law.outputRank x))) := by
          funext x; dsimp [g]; ring
        rw [heq]
        simpa only [Nat.cast_add, Nat.cast_one] using h
      have hprod := nonnegative_product_sum
        (fun x xs => law.runMass skip (t + 1) (x :: xs) * law.runClock (x :: xs))
        (fun x xs => mul_nonneg (law.runMass_nonneg skip _ htN _) (law.runClock_nonneg _))
        g _ hfib hrows
      have hfull := list_run_hasSum
        (fun xs => law.runMass skip (t + 1) xs * law.runClock xs) _ hprod
      have hmean : HasSum (fun xs => law.runMass skip (t + 1) xs * law.runClock xs)
          (qc + (∑ i : Fin N, if i.val < t + 1 then E (skip.next i) else 0) / (t + 1 : ℝ)) := by
        simpa only [runMass, if_neg (by omega : ¬ t + 1 = 0), zero_mul, zero_add] using hfull
      refine ⟨_, hmean, ?_, ?_⟩
      · have h : 0 ≤ ∑' xs : List Ω, law.runMass skip (t + 1) xs * law.runClock xs :=
          tsum_nonneg (fun xs => mul_nonneg
            (law.runMass_nonneg skip _ htN xs) (law.runClock_nonneg xs))
        rwa [hmean.tsum_eq] at h
      · have hfuture :
            (∑ i : Fin N, if i.val < t + 1 then E (skip.next i) else 0) / (t + 1 : ℝ) ≤
              (∑ i : Fin N, if i.val < t + 1 then V (skip.next i) else 0) / (t + 1 : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply Finset.sum_le_sum
          intro i _
          split_ifs with hi
          · exact (hE _ (lt_of_le_of_lt (skip.le_rank _) hi)).2.2
          · exact le_rfl
        have hp := hstep (t + 1) (by omega) htN
        push_cast at hp
        linarith

/-- Under the call-moment and potential-recurrence hypotheses, the initial run-clock moment for
`N > 0` exists and lies between zero and the average of `V (skip.next i)` over initial
ranks. -/
theorem initialClock_moment (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (D V : ℕ → ℝ) (hV0 : V 0 = 0)
    (hcall : ∀ t, 0 < t → t < N → ∃ q,
      HasSum (fun x => law.mass t x * law.duration x) q ∧ q ≤ D t)
    (hstep : ∀ t, 0 < t → t < N →
      D t + (∑ i : Fin N, if i.val < t then V (skip.next i) else 0) / (t : ℝ) ≤ V t)
    (hN : 0 < N) :
    ∃ q, HasSum (fun x : Fin N × List Ω => law.initialMass skip x * law.runClock x.2) q ∧
      0 ≤ q ∧ q ≤ (∑ i : Fin N, V (skip.next i)) / (N : ℝ) := by
  let E : Fin N → ℝ := fun i => ∑' xs : List Ω,
    law.runMass skip (skip.next i) xs * law.runClock xs
  have hE (i : Fin N) :
      HasSum (fun xs => law.runMass skip (skip.next i) xs * law.runClock xs) (E i) ∧
        0 ≤ E i ∧ E i ≤ V (skip.next i) := by
    obtain ⟨q, hq, hqnn, hqb⟩ := law.runClock_moment skip D V hV0 hcall hstep
      (skip.next i) (lt_of_le_of_lt (skip.le_rank i) i.isLt)
    have heq : E i = q := hq.tsum_eq
    rw [heq]
    exact ⟨hq, hqnn, hqb⟩
  have hfib (i : Fin N) :
      HasSum (fun xs => law.initialMass skip (i, xs) * law.runClock xs) (E i / (N : ℝ)) := by
    convert! (hE i).1.div_const (N : ℝ) using 1
    funext xs
    unfold initialMass
    ring
  have hrows : HasSum (fun i : Fin N => E i / (N : ℝ))
      ((∑ i : Fin N, E i) / (N : ℝ)) := by
    rw [Finset.sum_div]
    exact hasSum_fintype _
  have hnn (x : Fin N × List Ω) : 0 ≤ law.initialMass skip x * law.runClock x.2 :=
    mul_nonneg ((law.initialMass_normalized skip hN).2 x) (law.runClock_nonneg x.2)
  have hfull := nonnegative_product_sum
    (fun i xs => law.initialMass skip (i, xs) * law.runClock xs)
    (fun i xs => hnn (i, xs)) _ _ hfib hrows
  refine ⟨_, hfull, ?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => (hE i).2.1)) (Nat.cast_nonneg N)
  · exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => (hE i).2.2))
      (Nat.cast_nonneg N)

end RankedCallLaw
end Qatlib.Concepts.AmplitudeSearch.Amplification
