/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchAttempt
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized

/-!
# Retry reach masses and geometric search tails

This module defines reach, first-success, and output masses for a sequence of checked search
attempts. It proves finite-prefix normalization and geometric tail bounds once the attempt sizes
pass the angle-dependent search threshold.

For a nonempty proper marked set, the exponential schedule gives first-success masses summing to
one, as required for randomized search [BoyerEtAl1998].

## Main statements

* `search_weighted_retry_tail`: After every attempt size exceeds `1 / sin (2θ)`, the retry reach
  mass after `k` further stages is at most the starting reach mass times `(3 / 4)^k`.
* `search_all_density_termination`: For a nonempty proper marked set, first-success masses under
  the exponential schedule sum to one.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open scoped BigOperators
open Filter

/-- The product of checked failure probabilities over stages before `n`. -/
noncomputable def RetryReach {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, CheckedFailure A (sizes k)

/-- The mass of reaching stage `n` and succeeding at that stage. -/
noncomputable def RetryFirstSuccess {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) : ℝ :=
  RetryReach A sizes n * CheckedSuccess A (sizes n)

/-- The mass of reaching stage `s` and returning index `i`, averaging over that stage's
iteration counts. -/
noncomputable def RetryOutputMass {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (s : ℕ) (i : I) : ℝ :=
  RetryReach A sizes s *
    ((∑ j ∈ Finset.range (sizes s), CheckedOutputMass A j i) / (sizes s : ℝ))

/-- Reach mass lies in `[0, 1]`, first-success mass is nonnegative, and earlier first-success
masses plus the surviving mass sum to one. -/
theorem search_retry_prefix {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (n : ℕ) :
    0 ≤ RetryReach A sizes n ∧ RetryReach A sizes n ≤ 1 ∧
    (∑ k ∈ Finset.range n, RetryFirstSuccess A sizes k) + RetryReach A sizes n = 1 ∧
    0 ≤ RetryFirstSuccess A sizes n := by
  have hstep (k : ℕ) : RetryReach A sizes (k + 1) =
      RetryReach A sizes k * CheckedFailure A (sizes k) := by
    simp only [RetryReach, Finset.prod_range_succ]
  induction n with
  | zero =>
    have hp := search_checked_random_attempt hN A (sizes 0) (hsizes 0)
    simpa [RetryReach, RetryFirstSuccess] using hp.2.2.1.1
  | succ n ih =>
    have hp := search_checked_random_attempt hN A (sizes n) (hsizes n)
    have hpnext := search_checked_random_attempt hN A (sizes (n+1)) (hsizes (n+1))
    have hfail : CheckedFailure A (sizes n) ≤ 1 := by linarith [hp.2.1, hp.2.2.1.1]
    have hnonneg : 0 ≤ RetryReach A sizes (n+1) := by
      rw [hstep]
      exact mul_nonneg ih.1 hp.2.2.1.2
    refine ⟨hnonneg, ?_, ?_, ?_⟩
    · rw [hstep]
      calc
        _ ≤ RetryReach A sizes n := mul_le_of_le_one_right ih.1 hfail
        _ ≤ 1 := ih.2.1
    · rw [Finset.sum_range_succ, RetryFirstSuccess, hstep, hp.2.1]
      nlinarith [ih.2.2.1]
    · exact mul_nonneg hnonneg hpnext.2.2.1.1

/-- The retry reach mass cannot increase with the stage. -/
theorem search_retry_reach_mono {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (n m : ℕ) (hnm : n ≤ m) :
    RetryReach A sizes m ≤ RetryReach A sizes n := by
  have step (k : ℕ) : RetryReach A sizes (k+1) ≤ RetryReach A sizes k := by
    have hp := search_checked_random_attempt hN A (sizes k) (hsizes k)
    have hf : CheckedFailure A (sizes k) ≤ 1 := by linarith [hp.2.1, hp.2.2.1.1]
    rw [RetryReach, Finset.prod_range_succ]
    change RetryReach A sizes k * CheckedFailure A (sizes k) ≤ _
    exact mul_le_of_le_one_right (search_retry_prefix hN A sizes hsizes k).1 hf
  exact antitone_nat_of_succ_le step hnm

/-- After every attempt size exceeds `1 / sin (2θ)`, the retry reach mass after `k` further
stages is at most the starting reach mass times `(3 / 4)^k`. -/
theorem search_weighted_retry_tail {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I)
    (θ : ℝ) (hθ0 : 0 < θ) (hθp : θ < Real.pi / 2)
    (hdensity : (Real.sin θ)^2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (L : ℕ)
    (hlarge : ∀ k, L ≤ k → 1 / Real.sin (2*θ) ≤ (sizes k : ℝ)) :
    ∀ k : ℕ, RetryReach A sizes (L+k) ≤ RetryReach A sizes L * (3/4 : ℝ)^k := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have h2 : 0 < Real.sin (2*θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hfail (s : ℕ) (hs : L ≤ s) : CheckedFailure A (sizes s) ≤ 3/4 := by
    have hq := (search_randomized_angle hN A θ hdensity h2 (sizes s) (hsizes s)).2.2
      (hlarge s hs)
    have hc := search_checked_random_attempt hN A (sizes s) (hsizes s)
    linarith [hc.1, hc.2.1]
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, RetryReach, Finset.prod_range_succ, pow_succ]
    change RetryReach A sizes (L+k) * CheckedFailure A (sizes (L+k)) ≤ _
    calc
      _ ≤ RetryReach A sizes (L+k) * (3/4) :=
        mul_le_mul_of_nonneg_left (hfail (L+k) (by omega))
          (search_retry_prefix hN A sizes hsizes (L+k)).1
      _ ≤ (RetryReach A sizes L * (3/4 : ℝ)^k) * (3/4) :=
        mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = _ := by ring

/-- Beyond the angle-dependent size threshold, reach mass is at most `(3 / 4)^k` and accumulated
first-success mass is at least `1 - (3 / 4)^k`. -/
theorem search_retry_tail {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I)
    (θ : ℝ) (hθ0 : 0 < θ) (hθp : θ < Real.pi / 2)
    (hdensity : (Real.sin θ)^2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (K : ℕ)
    (hlarge : ∀ k, K ≤ k → 1 / Real.sin (2*θ) ≤ (sizes k : ℝ)) (k : ℕ) :
    RetryReach A sizes (K+k) ≤ (3/4 : ℝ)^k ∧
      1 - (3/4 : ℝ)^k ≤ ∑ s ∈ Finset.range (K+k), RetryFirstSuccess A sizes s := by
  have hN := lt_trans hA hproper
  have h := search_weighted_retry_tail A hA hproper θ hθ0 hθp hdensity sizes hsizes K hlarge k
  have hb : RetryReach A sizes (K+k) ≤ (3/4 : ℝ)^k := by
    exact h.trans (mul_le_of_le_one_left (by positivity)
      (search_retry_prefix hN A sizes hsizes K).2.1)
  exact ⟨hb, by linarith [(search_retry_prefix hN A sizes hsizes (K+k)).2.2.1]⟩

/-- For a nonempty proper marked set, first-success masses under the exponential schedule sum to
one. -/
theorem search_all_density_termination {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    HasSum (RetryFirstSuccess A (ExponentialSizes (Fintype.card I))) 1 := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  let sizes := ExponentialSizes (Fintype.card I)
  have hsizes : ∀ k, 0 < sizes k := (search_exponential_schedule _ hN).2.1
  obtain ⟨θ,hθ0,hθp,hdensity,L,hL,hLhi,hlarge⟩ := search_critical_stage A hA hproper
  have htail := search_retry_tail A hA hproper θ hθ0 hθp hdensity sizes hsizes L hlarge
  have hpow : Tendsto (fun n : ℕ => (3/4 : ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hshift : Tendsto (fun n : ℕ => RetryReach A sizes (L+n)) atTop (nhds 0) :=
    squeeze_zero (fun n => (search_retry_prefix hN A sizes hsizes (L+n)).1)
      (fun n => (htail n).1) hpow
  have hreach : Tendsto (RetryReach A sizes) atTop (nhds 0) := by
    apply (tendsto_add_atTop_iff_nat L).mp
    simpa only [Nat.add_comm] using hshift
  have hmass (s : ℕ) : 0 ≤ RetryFirstSuccess A sizes s :=
    (search_retry_prefix hN A sizes hsizes s).2.2.2
  apply (hasSum_iff_tendsto_nat_of_nonneg hmass 1).2
  have heq : (fun n => ∑ s ∈ Finset.range n, RetryFirstSuccess A sizes s) =
      (fun n => 1 - RetryReach A sizes n) := by
    funext n
    linarith [(search_retry_prefix hN A sizes hsizes n).2.2.1]
  rw [heq]
  simpa only [sub_zero] using (tendsto_const_nhds.sub hreach)

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
