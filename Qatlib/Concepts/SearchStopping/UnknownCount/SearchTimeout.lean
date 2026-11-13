/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBoundary

/-!
# Uniform timeout bounds for unknown-count search

Defines `WorstPrefixIterations`, a deterministic upper bound on the Grover iterations in any
history of a given length. For the factor `6 / 5` schedule, `search_uniform_timeout` bounds the
residual reach probability by `(3 / 4) ^ k`, and `search_uniform_query_timeout` includes
verification-query costs. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `search_uniform_timeout`: On a nonempty search space, there is `K ≤ 6 * Real.sqrt
  (Fintype.card I)` such that every `K + k` stage prefix costs at most `(6 + k) * Real.sqrt
  (Fintype.card I)` iterations and has reach probability at most `(3 / 4) ^ k` for every
  nonempty marked set.
* `search_timeout_error_tendsto`: The geometric timeout-error bound `(3 / 4) ^ k` converges to
  zero as `k` tends to infinity.
* `search_uniform_query_timeout`: On a nonempty search space, a common stage offset gives
  Boolean-query prefix cost at most `(12 + 2 * k) * Real.sqrt (Fintype.card I)` and reach
  probability at most `(3 / 4) ^ k` for every nonempty marked set.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Concepts.SearchStopping.UnknownCount

open scoped BigOperators
open Filter

/-- The sum of the largest available iteration count `sizes s - 1` over the first `n` stages. -/
def WorstPrefixIterations (sizes : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ s ∈ Finset.range n, (sizes s - 1)

/-- The Grover iteration count of any trial history is at most `WorstPrefixIterations` for its
stage count. -/
theorem search_history_worst_bound (sizes : ℕ → ℕ) (n : ℕ) (h : TrialHistory sizes n) :
    HistoryIterations sizes n h ≤ WorstPrefixIterations sizes n := by
  unfold HistoryIterations WorstPrefixIterations
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum
  intro k _
  have hk := (h k).isLt
  omega

/-- For positive `N`, the largest integer sampled from the exponential stage range is at most
its real-valued width. -/
theorem search_largest_sample_le_width (N s : ℕ) (hN : 0 < N) :
    ((ExponentialSizes N s - 1 : ℕ) : ℝ) ≤ ExponentialWidth N s := by
  have hs := (search_exponential_schedule N hN).2.1 s
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hw : 0 ≤ ExponentialWidth N s := by
    rw [(search_exponential_schedule N hN).1]
    exact le_min (by positivity) (Real.sqrt_nonneg _)
  have hc := Nat.ceil_lt_add_one hw
  change (Nat.ceil (ExponentialWidth N s) : ℝ) - 1 ≤ _
  linarith

/-- If the exponential scale at stage `K` is at most `(6 / 5) * Real.sqrt N`, the worst
iteration prefix through `K + k` stages is at most `(6 + k) * Real.sqrt N`. -/
theorem search_worst_prefix_cap (N K k : ℕ) (hN : 0 < N)
    (hK : (6/5 : ℝ)^K ≤ (6/5) * Real.sqrt N) :
    (WorstPrefixIterations (ExponentialSizes N) (K+k) : ℝ) ≤
      (6 + (k : ℝ)) * Real.sqrt N := by
  have hbefore : (∑ s ∈ Finset.range K, ((ExponentialSizes N s - 1 : ℕ) : ℝ)) ≤
      5 * (6/5 : ℝ)^K := by
    calc
      _ ≤ ∑ s ∈ Finset.range K, (6/5 : ℝ)^s := by
        apply Finset.sum_le_sum
        intro s _
        apply (search_largest_sample_le_width N s hN).trans
        rw [(search_exponential_schedule N hN).1]
        exact min_le_left _ _
      _ ≤ _ := (search_geometric_sums K).1
  have hafter : (∑ s ∈ Finset.range k, ((ExponentialSizes N (K+s) - 1 : ℕ) : ℝ)) ≤
      (k : ℝ) * Real.sqrt N := by
    calc
      _ ≤ ∑ _s ∈ Finset.range k, Real.sqrt N := by
        apply Finset.sum_le_sum
        intro s _
        apply (search_largest_sample_le_width N (K+s) hN).trans
        rw [(search_exponential_schedule N hN).1]
        exact min_le_right _ _
      _ = _ := by simp
  simp only [WorstPrefixIterations, Finset.sum_range_add]
  push_cast
  nlinarith

/-- On a nonempty search space, there is `K ≤ 6 * Real.sqrt (Fintype.card I)` such that every `K
+ k` stage prefix costs at most `(6 + k) * Real.sqrt (Fintype.card I)` iterations and has
reach probability at most `(3 / 4) ^ k` for every nonempty marked set. -/
theorem search_uniform_timeout {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) :
    ∃ K : ℕ, (K : ℝ) ≤ 6 * Real.sqrt (Fintype.card I) ∧ ∀ k : ℕ,
      (WorstPrefixIterations (ExponentialSizes (Fintype.card I)) (K+k) : ℝ) ≤
        (6 + (k : ℝ)) * Real.sqrt (Fintype.card I) ∧
      ∀ A : Finset I, 0 < A.card →
        RetryReach A (ExponentialSizes (Fintype.card I)) (K+k) ≤ (3/4 : ℝ)^k := by
  have hNr : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast hN
  have hroot : 1 ≤ Real.sqrt (Fintype.card I) := by
    nlinarith [Real.sqrt_nonneg (Fintype.card I : ℝ),
      Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I))]
  obtain ⟨K,hKlo,hKhi⟩ := search_first_scale_crossing (Real.sqrt (Fintype.card I)) hroot
  have hcount : (K : ℝ) ≤ 6 * Real.sqrt (Fintype.card I) := by
    have hsum : (K : ℝ) ≤ ∑ s ∈ Finset.range K, (6/5 : ℝ)^s := by
      calc
        _ = ∑ _s ∈ Finset.range K, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun _ _ => one_le_pow₀ (by norm_num))
    nlinarith [(search_geometric_sums K).1]
  have hsizes := (search_exponential_schedule _ hN).2.1
  have hcap (s : ℕ) (hs : K ≤ s) : Real.sqrt (Fintype.card I) ≤
      (ExponentialSizes (Fintype.card I) s : ℝ) := by
    have hp : (6/5 : ℝ)^K ≤ (6/5 : ℝ)^s := by
      have heq : s = K + (s-K) := by omega
      rw [heq, pow_add]
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
    apply le_trans _ (Nat.le_ceil _)
    rw [(search_exponential_schedule _ hN).1]
    exact le_min (hKlo.trans hp) le_rfl
  refine ⟨K,hcount,?_⟩
  intro k
  refine ⟨search_worst_prefix_cap _ K k hN hKhi, ?_⟩
  intro A hA
  by_cases hp : A.card < Fintype.card I
  · obtain ⟨θ,hθ0,hθp,hdensity,_⟩ := search_principal_angle A hA hp
    have hc := (search_integer_cap _ _ hA hp θ hθ0 hθp hdensity).2
    exact (search_retry_tail A hA hp θ hθ0 hθp hdensity _ hsizes K
      (fun s hs => hc.trans (hcap s hs)) k).1
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hr := search_univ_first_success hN _ hsizes (K+k)
    rw [RetryFirstSuccess, (search_univ_failure hN _ (hsizes (K+k))).1, mul_one] at hr
    rw [hr]
    split_ifs with hz
    · have hk : k = 0 := by omega
      simp [hk]
    · positivity

/-- The geometric timeout-error bound `(3 / 4) ^ k` converges to zero as `k` tends to infinity. -/
theorem search_timeout_error_tendsto :
    Tendsto (fun k : ℕ => (3/4 : ℝ)^k) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- On a nonempty search space, the retry output mass at every unmarked address is zero at every
stage, for any schedule. -/
theorem search_no_false_positive {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (n : ℕ) (i : I) (hi : i ∉ A) : RetryOutputMass A sizes n i = 0 := by
  unfold RetryOutputMass
  have hz (j : ℕ) : CheckedOutputMass A j i = 0 := by
    rw [(search_checked_attempt hN A j).2.1 i, if_neg hi]
  simp_rw [hz]
  simp

/-- On a nonempty search space, a common stage offset gives Boolean-query prefix cost at most
`(12 + 2 * k) * Real.sqrt (Fintype.card I)` and reach probability at most `(3 / 4) ^ k` for
every nonempty marked set. -/
theorem search_uniform_query_timeout {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) :
    ∃ K : ℕ, ∀ k : ℕ,
      ((WorstPrefixIterations (ExponentialSizes (Fintype.card I)) (K+k) + (K+k) : ℕ) : ℝ) ≤
        (12 + 2*(k : ℝ)) * Real.sqrt (Fintype.card I) ∧
      ∀ A : Finset I, 0 < A.card →
        RetryReach A (ExponentialSizes (Fintype.card I)) (K+k) ≤ (3/4 : ℝ)^k := by
  obtain ⟨K,hK,hall⟩ := search_uniform_timeout hN
  have hNr : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast hN
  have hroot : 1 ≤ Real.sqrt (Fintype.card I) := by
    nlinarith [Real.sqrt_nonneg (Fintype.card I : ℝ),
      Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I))]
  refine ⟨K,?_⟩
  intro k
  refine ⟨?_,(hall k).2⟩
  have hk : (k : ℝ) ≤ (k : ℝ) * Real.sqrt (Fintype.card I) :=
    le_mul_of_one_le_right (Nat.cast_nonneg k) hroot
  push_cast
  nlinarith [(hall k).1]

end Qatlib.Concepts.SearchStopping.UnknownCount
