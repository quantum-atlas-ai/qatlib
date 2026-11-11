/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.DiscreteRun

/-!
# Completion laws for naturally charged runs

`runCharge` sums natural call costs, and `RankedCallLaw.completionMass` sums the masses of
terminating runs that fit a budget. The module proves normalization bounds, the terminal
threshold-zero case, and a first-call recurrence for completion mass.

A final summation result averages these completion probabilities over a uniform initial rank,
supporting budgeted quantum minimum-finding analysis as in [DurrHoyer1996].

## Main statements

* `RankedCallLaw.completion_law`: shows that completion mass lies between zero and one.
* `RankedCallLaw.completion_step`: decomposes completion through affordable first calls.
* `RankedCallLaw.initial_completion_hasSum`: gives the uniform initial completion average.

## References

* [Durr and Hoyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

variable {N : ℕ} {Ω : Type}

/-- The sum of the natural call charges along a run. -/
def runCharge (charge : Ω → ℕ) (xs : List Ω) : ℕ := (xs.map charge).sum

namespace RankedCallLaw

/-- The total mass of terminating ranked runs whose accumulated natural charge is within the
budget. -/
noncomputable def completionMass (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (charge : Ω → ℕ) (t budget : ℕ) : ℝ :=
  ∑' xs : List Ω, if runCharge charge xs ≤ budget then law.runMass skip t xs else 0

/-- For `t < N`, budget-completing run masses sum to `completionMass`, which lies between zero
and one. -/
theorem completion_law (law : RankedCallLaw N Ω) (skip : RankSkip N) (charge : Ω → ℕ)
    (t : ℕ) (htN : t < N) (budget : ℕ) :
    HasSum (fun xs : List Ω => if runCharge charge xs ≤ budget then law.runMass skip t xs else 0)
      (law.completionMass skip charge t budget) ∧
      0 ≤ law.completionMass skip charge t budget ∧ law.completionMass skip charge t budget ≤ 1 := by
  have hm := law.runMass_normalized skip t htN
  have hn (xs : List Ω) : 0 ≤ law.runMass skip t xs := law.runMass_nonneg skip t htN xs
  have hf (xs : List Ω) :
      0 ≤ (if runCharge charge xs ≤ budget then law.runMass skip t xs else 0) ∧
        (if runCharge charge xs ≤ budget then law.runMass skip t xs else 0) ≤ law.runMass skip t xs := by
    split_ifs <;> simp [hn xs]
  have hs := Summable.of_nonneg_of_le (fun xs => (hf xs).1) (fun xs => (hf xs).2) hm.summable
  refine ⟨hs.hasSum, tsum_nonneg (fun xs => (hf xs).1), ?_⟩
  have h := Summable.tsum_le_tsum (fun xs => (hf xs).2) hs hm.summable
  rwa [hm.tsum_eq] at h

/-- At threshold zero, the completion mass is one for any natural budget and nonempty rank type. -/
theorem completion_zero (law : RankedCallLaw N Ω) (skip : RankSkip N) (charge : Ω → ℕ)
    (hN : 0 < N) (budget : ℕ) : law.completionMass skip charge 0 budget = 1 := by
  have heq : (fun xs : List Ω => if runCharge charge xs ≤ budget then law.runMass skip 0 xs else 0) =
      law.runMass skip 0 := by
    funext xs
    cases xs <;> simp [runMass, runCharge]
  unfold completionMass
  rw [heq]
  exact (law.runMass_normalized skip 0 hN).tsum_eq

/-- For a positive threshold below `N`, completion mass is the sum over affordable first calls
of their mass times the remaining-budget continuation mass. -/
theorem completion_step (law : RankedCallLaw N Ω) (skip : RankSkip N) (charge : Ω → ℕ)
    (t : ℕ) (ht : 0 < t) (htN : t < N) (budget : ℕ) :
    HasSum (fun x : Ω => if charge x ≤ budget then law.mass t x *
      law.completionMass skip charge (skip.next (law.outputRank x)) (budget - charge x) else 0)
      (law.completionMass skip charge t budget) := by
  let g : Ω → ℝ := fun x => if charge x ≤ budget then law.mass t x *
    law.completionMass skip charge (skip.next (law.outputRank x)) (budget - charge x) else 0
  have hg (x : Ω) : 0 ≤ g x ∧ g x ≤ law.mass t x := by
    have hc := law.completion_law skip charge (skip.next (law.outputRank x))
      (lt_of_le_of_lt (skip.le_rank _) (law.outputRank x).isLt) (budget - charge x)
    have hm := law.mass_nonneg t htN x
    dsimp [g]
    split_ifs
    · constructor
      · exact mul_nonneg hm hc.2.1
      · nlinarith [hc.2.2]
    · exact ⟨le_rfl, hm⟩
  have hgs := Summable.of_nonneg_of_le (fun x => (hg x).1) (fun x => (hg x).2)
    (law.normalized t ht htN).summable
  have hfib (x : Ω) : HasSum (fun xs : List Ω => if runCharge charge (x :: xs) ≤ budget then
      law.runMass skip t (x :: xs) else 0) (g x) := by
    by_cases hcost : charge x ≤ budget
    · by_cases hx : (law.outputRank x).val < t
      · have htail := (law.completion_law skip charge (skip.next (law.outputRank x))
          (lt_of_le_of_lt (skip.le_rank _) (law.outputRank x).isLt) (budget - charge x)).1
        have h := htail.mul_left (law.mass t x)
        convert! h using 1
        · funext xs
          simp only [runCharge, List.map_cons, List.sum_cons, runMass,
            if_neg (Nat.ne_of_gt ht), if_pos hx]
          have heq : charge x + runCharge charge xs ≤ budget ↔
              runCharge charge xs ≤ budget - charge x := by omega
          simp only [runCharge] at heq
          simp only [heq]
          split_ifs <;> ring
        · (try simp only [g, if_pos hcost])
      · have hz := law.lower_support t ht htN x hx
        have hzero : g x = 0 := by simp [g, hcost, hz]
        rw [hzero]
        simpa only [runMass, if_neg (Nat.ne_of_gt ht), if_neg hx, ite_self] using
          (hasSum_zero : HasSum (fun _ : List Ω => (0 : ℝ)) 0)
    · have hzero : g x = 0 := by simp [g, hcost]
      rw [hzero]
      have heq : (fun xs : List Ω => if runCharge charge (x :: xs) ≤ budget then
          law.runMass skip t (x :: xs) else 0) = fun _ => 0 := by
        funext xs
        have hnot : ¬ runCharge charge (x :: xs) ≤ budget := by
          simp only [runCharge, List.map_cons, List.sum_cons]
          omega
        simp only [if_neg hnot]
      rw [heq]
      exact hasSum_zero
  have hprod := nonnegative_product_sum
    (fun x xs => if runCharge charge (x :: xs) ≤ budget then law.runMass skip t (x :: xs) else 0)
    (fun x xs => by (try dsimp only); split_ifs; exact law.runMass_nonneg skip t htN _; exact le_rfl)
    g _ hfib hgs.hasSum
  have hfull := list_run_hasSum
    (fun xs => if runCharge charge xs ≤ budget then law.runMass skip t xs else 0) _ hprod
  have hmean : HasSum (fun xs => if runCharge charge xs ≤ budget then law.runMass skip t xs else 0)
      (∑' x, g x) := by
    simpa only [runMass, if_neg (Nat.ne_of_gt ht), ite_self, zero_add] using hfull
  have heq := (law.completion_law skip charge t htN budget).1.unique hmean
  rw [heq]
  exact hgs.hasSum

/-- The budget-completing initial run mass sums to the uniform average of the corresponding
completion masses over starting ranks. -/
theorem initial_completion_hasSum (law : RankedCallLaw N Ω) (skip : RankSkip N) (charge : Ω → ℕ)
    (hN : 0 < N) (budget : ℕ) :
    HasSum (fun x : Fin N × List Ω => if runCharge charge x.2 ≤ budget then law.initialMass skip x else 0)
      ((∑ i : Fin N, law.completionMass skip charge (skip.next i) budget) / (N : ℝ)) := by
  have hfib (i : Fin N) : HasSum (fun xs : List Ω => if runCharge charge xs ≤ budget then
      law.initialMass skip (i, xs) else 0) (law.completionMass skip charge (skip.next i) budget / (N : ℝ)) := by
    have h := (law.completion_law skip charge (skip.next i)
      (lt_of_le_of_lt (skip.le_rank i) i.isLt) budget).1.div_const (N : ℝ)
    convert! h using 1
    funext xs
    unfold initialMass
    split_ifs <;> ring
  have hrows : HasSum (fun i : Fin N => law.completionMass skip charge (skip.next i) budget / (N : ℝ))
      ((∑ i : Fin N, law.completionMass skip charge (skip.next i) budget) / (N : ℝ)) := by
    rw [Finset.sum_div]
    exact hasSum_fintype _
  apply nonnegative_product_sum _ _ _ _ hfib hrows
  intro i xs
  (try dsimp only)
  split_ifs
  · exact (law.initialMass_normalized skip hN).2 (i, xs)
  · exact le_rfl

end RankedCallLaw
end Qatlib.Concepts.AmplitudeSearch.Amplification
