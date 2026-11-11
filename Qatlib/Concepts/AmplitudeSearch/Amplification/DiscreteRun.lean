/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockedPrefix

/-!
# Discrete descending-rank run laws

`RankedCallLaw` packages a search-call distribution with a uniform output rank below the current
threshold and a nonnegative duration. `RankSkip` allows the next threshold to decrease further,
as needed for tied values, and `RankedCallLaw.runMass` assigns mass to finite terminating runs.

The module proves normalization, termination bounds, initial-rank averaging, and uniform
continuation expectations. This probabilistic rank model supports the quantum minimum-finding
analysis of [DurrHoyer1996].

## Main statements

* `RankedCallLaw.runMass_normalized`: normalizes finite terminating runs.
* `RankedCallLaw.runMass_terminates`: bounds a positive-mass run's length by its starting
  threshold.
* `RankedCallLaw.continuation_sum`: computes continuation expectations as uniform lower-rank
  averages.

## References

* [Durr and Hoyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AmplitudeSearch.Amplification.DistinctRankedTable

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- A ranked search-call law with nonnegative durations and, below `N`, nonnegative call masses
that are normalized and uniform over lower output ranks at positive thresholds. -/
structure RankedCallLaw (N : ℕ) (Ω : Type) where
  mass : ℕ → Ω → ℝ
  outputRank : Ω → Fin N
  duration : Ω → ℝ
  mass_nonneg : ∀ t, t < N → ∀ x, 0 ≤ mass t x
  duration_nonneg : ∀ x, 0 ≤ duration x
  normalized : ∀ t, 0 < t → t < N → HasSum (mass t) 1
  lower_support : ∀ t, 0 < t → t < N → ∀ x, ¬ (outputRank x).val < t → mass t x = 0
  output_uniform : ∀ t, 0 < t → t < N → ∀ i : Fin N,
    HasSum (fun x => if outputRank x = i then mass t x else 0)
      (if i.val < t then 1 / (t : ℝ) else 0)

/-- A rank-threshold update bounded above by the selected rank. -/
structure RankSkip (N : ℕ) where
  next : Fin N → ℕ
  le_rank : ∀ i, next i ≤ i.val

/-- The rank skip that uses the selected rank itself as the next threshold. -/
def RankSkip.distinct (N : ℕ) : RankSkip N := ⟨Fin.val, fun _ => le_rfl⟩

/-- For a nonnegative family, summing each fiber and then its fiber sums gives the same sum over
the product type. -/
theorem nonnegative_product_sum {α β : Type*}
    (f : α → β → ℝ) (hf : ∀ a b, 0 ≤ f a b) (g : α → ℝ) (q : ℝ)
    (hfib : ∀ a, HasSum (f a) (g a)) (hrows : HasSum g q) :
    HasSum (fun x : α × β => f x.1 x.2) q := by
  have heq : (fun a => ∑' b, f a b) = g := funext (fun a => (hfib a).tsum_eq)
  have hs : Summable (fun x : Σ _a : α, β => f x.1 x.2) :=
    (summable_sigma_of_nonneg
      (f := fun x : Σ _a : α, β => f x.1 x.2) (fun x => hf x.1 x.2)).2
      ⟨fun a => (hfib a).summable, by rw [heq]; exact hrows.summable⟩
  have h := hrows.sigma_of_hasSum hfib hs
  exact (Equiv.sigmaEquivProd α β).hasSum_iff.mp h

/-- The equivalence splitting a list into either the empty list or a head and tail. -/
private def runListCases (α : Type*) : List α ≃ (Unit ⊕ (α × List α)) where
  toFun
    | [] => Sum.inl ()
    | x :: xs => Sum.inr (x, xs)
  invFun
    | Sum.inl _ => []
    | Sum.inr (x, xs) => x :: xs
  left_inv := by intro xs; cases xs <;> rfl
  right_inv := by
    intro x
    rcases x with u | ⟨a, xs⟩
    · cases u; rfl
    · rfl

/-- If the nonempty-list terms sum to `q`, the entire list family sums to its empty-list value
plus `q`. -/
theorem list_run_hasSum {α : Type*} (f : List α → ℝ) (q : ℝ)
    (hcons : HasSum (fun x : α × List α => f (x.1 :: x.2)) q) :
    HasSum f (f [] + q) := by
  let e := runListCases α
  have h : HasSum (fun x : Unit ⊕ (α × List α) => f (e.symm x)) (f [] + q) := by
    apply HasSum.sum
    · change HasSum (fun _ : Unit => f []) (f [])
      simp
    · exact hcons
  exact e.symm.hasSum_iff.mp h

namespace RankedCallLaw

variable {N : ℕ} {Ω : Type}

/-- The mass of a finite terminating run, multiplying supported descending call masses and
stopping exactly at threshold zero. -/
noncomputable def runMass (law : RankedCallLaw N Ω) (skip : RankSkip N) (t : ℕ) :
    List Ω → ℝ
  | [] => if t = 0 then 1 else 0
  | x :: xs => if t = 0 then 0 else
      if (law.outputRank x).val < t then
        law.mass t x * runMass law skip (skip.next (law.outputRank x)) xs else 0

/-- For a starting threshold below `N`, every ranked run mass is nonnegative. -/
theorem runMass_nonneg (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (t : ℕ) (htN : t < N) (xs : List Ω) : 0 ≤ law.runMass skip t xs := by
  induction xs generalizing t with
  | nil => simp [runMass]; split_ifs <;> norm_num
  | cons x xs ih =>
    rw [runMass]
    split_ifs with ht hlow
    · exact le_rfl
    · exact mul_nonneg (law.mass_nonneg t htN x)
        (ih _ (lt_of_le_of_lt (skip.le_rank _) (lt_trans hlow htN)))
    · exact le_rfl

/-- For a starting threshold below `N`, the finite terminating run masses sum to one. -/
theorem runMass_normalized (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (t : ℕ) (htN : t < N) : HasSum (law.runMass skip t) 1 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero =>
      have hc : HasSum (fun x : Ω × List Ω => law.runMass skip 0 (x.1 :: x.2)) 0 := by
        simpa only [runMass, if_pos rfl] using! hasSum_zero
      simpa only [runMass, if_pos rfl, add_zero] using!
        list_run_hasSum (law.runMass skip 0) 0 hc
    | succ t =>
      have hfib (x : Ω) : HasSum (fun xs => law.runMass skip (t + 1) (x :: xs))
          (law.mass (t + 1) x) := by
        by_cases hx : (law.outputRank x).val < t + 1
        · have hnext : skip.next (law.outputRank x) < t + 1 :=
            lt_of_le_of_lt (skip.le_rank _) hx
          have htail := ih _ hnext (lt_trans hnext htN)
          have h := htail.mul_left (law.mass (t + 1) x)
          simpa only [runMass, if_neg (by omega : ¬ t + 1 = 0), if_pos hx, mul_one] using h
        · have hz := law.lower_support (t + 1) (by omega) htN x hx
          simpa only [runMass, if_neg (by omega : ¬ t + 1 = 0), if_neg hx, hz] using hasSum_zero
      have hcons := nonnegative_product_sum
        (fun x xs => law.runMass skip (t + 1) (x :: xs))
        (fun x xs => law.runMass_nonneg skip (t + 1) htN (x :: xs))
        _ 1 hfib (law.normalized (t + 1) (by omega) htN)
      have h := list_run_hasSum (law.runMass skip (t + 1)) 1 hcons
      simpa only [runMass, if_neg (by omega : ¬ t + 1 = 0), zero_add] using h

/-- The candidate threshold remaining after applying the rank skip along a list of calls. -/
def finalCandidateCount (law : RankedCallLaw N Ω) (skip : RankSkip N) (t : ℕ) : List Ω → ℕ
  | [] => t
  | x :: xs => finalCandidateCount law skip (skip.next (law.outputRank x)) xs

/-- A positive-mass run ends at threshold zero and contains at most its starting threshold many
calls. -/
theorem runMass_terminates (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (t : ℕ) (htN : t < N) (xs : List Ω) (hm : 0 < law.runMass skip t xs) :
    law.finalCandidateCount skip t xs = 0 ∧ xs.length ≤ t := by
  induction xs generalizing t with
  | nil =>
    have ht : t = 0 := by by_contra ht; simp [runMass, ht] at hm
    simp [finalCandidateCount, ht]
  | cons x xs ih =>
    by_cases ht : t = 0
    · simp [runMass, ht] at hm
    by_cases hx : (law.outputRank x).val < t
    · have hnext : skip.next (law.outputRank x) < t := lt_of_le_of_lt (skip.le_rank _) hx
      have hprod : 0 < law.mass t x * law.runMass skip (skip.next (law.outputRank x)) xs := by
        simpa only [runMass, if_neg ht, if_pos hx] using hm
      have htail : 0 < law.runMass skip (skip.next (law.outputRank x)) xs := by
        rcases mul_pos_iff.mp hprod with h | h
        · exact h.2
        · linarith [law.mass_nonneg t htN x, h.1]
      have h := ih _ (lt_trans hnext htN) htail
      refine ⟨h.1, ?_⟩
      simp only [List.length_cons]
      omega
    · simp only [runMass, if_neg ht, if_neg hx] at hm
      linarith

/-- The run mass obtained by choosing an initial rank uniformly and applying its skipped
starting threshold. -/
noncomputable def initialMass (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (x : Fin N × List Ω) : ℝ := law.runMass skip (skip.next x.1) x.2 / (N : ℝ)

/-- For positive `N`, the initial run masses are nonnegative and sum to one. -/
theorem initialMass_normalized (law : RankedCallLaw N Ω) (skip : RankSkip N) (hN : 0 < N) :
    HasSum (law.initialMass skip) 1 ∧ ∀ x, 0 ≤ law.initialMass skip x := by
  have hnext (i : Fin N) : skip.next i < N := lt_of_le_of_lt (skip.le_rank _) i.isLt
  have hnn (x : Fin N × List Ω) : 0 ≤ law.initialMass skip x :=
    div_nonneg (law.runMass_nonneg skip _ (hnext x.1) x.2) (Nat.cast_nonneg _)
  refine ⟨?_, hnn⟩
  have hfib (i : Fin N) : HasSum (fun xs => law.initialMass skip (i, xs)) (1 / (N : ℝ)) :=
    (law.runMass_normalized skip _ (hnext i)).div_const _
  have hg : HasSum (fun _i : Fin N => 1 / (N : ℝ)) 1 := by
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    simpa [hn] using hasSum_fintype (fun _i : Fin N => 1 / (N : ℝ))
  exact nonnegative_product_sum (fun i xs => law.initialMass skip (i, xs))
    (fun i xs => hnn (i, xs)) _ 1 hfib hg

/-- A sum over ranks below `t` inside `Fin N` equals the corresponding sum over `Fin t` when `t
≤ N`. -/
theorem sum_lower_ranks (t : ℕ) (htN : t ≤ N) (V : ℕ → ℝ) :
    (∑ i : Fin N, if i.val < t then V i.val else 0) = ∑ k : Fin t, V k.val := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin t))
  · intro i hi; exact Finset.mem_univ _
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun x : Fin t => x.val) hij)
  · intro k hk
    refine ⟨⟨k.val, lt_of_lt_of_le k.isLt htN⟩, ?_, ?_⟩
    · simp [k.isLt]
    · rfl
  · intro i hi; rfl

/-- A finite payoff of the call's output rank has expectation equal to its uniform average below
the positive threshold. -/
theorem continuation_finite (law : RankedCallLaw N Ω) (t : ℕ)
    (ht : 0 < t) (htN : t < N) (V : Fin N → ℝ) :
    HasSum (fun x => law.mass t x * V (law.outputRank x))
      ((∑ i : Fin N, if i.val < t then V i else 0) / (t : ℝ)) := by
  have ho (i : Fin N) := (law.output_uniform t ht htN i).mul_right (V i)
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => ho i)
  have hleft (x : Ω) :
      (∑ i : Fin N, (if law.outputRank x = i then law.mass t x else 0) * V i) =
        law.mass t x * V (law.outputRank x) := by simp [ite_mul]
  have hright : (∑ i : Fin N, (if i.val < t then (1 : ℝ) / t else 0) * V i) =
      (∑ i : Fin N, if i.val < t then V i else 0) / (t : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  simp_rw [hleft] at hsum
  rw [hright] at hsum
  exact hsum

/-- A natural-rank payoff of the call output has expectation equal to its average over ranks
below the positive threshold. -/
theorem continuation_sum (law : RankedCallLaw N Ω) (t : ℕ)
    (ht : 0 < t) (htN : t < N) (V : ℕ → ℝ) :
    HasSum (fun x => law.mass t x * V (law.outputRank x).val)
      ((∑ k : Fin t, V k.val) / (t : ℝ)) := by
  have h := law.continuation_finite t ht htN (fun i => V i.val)
  rwa [sum_lower_ranks t htN.le V] at h

end RankedCallLaw

end Qatlib.Concepts.AmplitudeSearch.Amplification
