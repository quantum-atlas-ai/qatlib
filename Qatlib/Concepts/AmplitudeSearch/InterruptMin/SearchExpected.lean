/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchRetry
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchAttempt
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchCircuit
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open scoped BigOperators
open Qatlib

noncomputable def RetryPhasePrefixCost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ s ∈ Finset.range n, RetryReach A sizes s * MeanQueries I (sizes s)

theorem search_geometric_sums (n : ℕ) :
    (∑ k ∈ Finset.range n, (6/5 : ℝ)^k) ≤ 5 * (6/5 : ℝ)^n ∧
    (∑ k ∈ Finset.range n, (9/10 : ℝ)^k) ≤ 10 := by
  have hbefore (k : ℕ) : (∑ s ∈ Finset.range k, (6/5 : ℝ)^s) ≤ 5 * (6/5 : ℝ)^k := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have htail (k : ℕ) : (∑ s ∈ Finset.range k, (9/10 : ℝ)^s) + 10 * (9/10 : ℝ)^k = 10 := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  refine ⟨hbefore n, ?_⟩
  have hp : 0 ≤ (9/10 : ℝ)^n := by positivity
  nlinarith [htail n]

theorem search_initial_trial {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ExponentialSizes (Fintype.card I) 0 = 1 ∧ MeanQueries I 1 = 0 ∧
      CheckedMeanQueries I 1 = 1 ∧ CheckedFailure A 1 = 1 - (A.card : ℝ) / Fintype.card I := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  obtain ⟨θ,hθ0,hθp,hdensity,h2⟩ := search_principal_angle A hA hproper
  have hs : Real.sin θ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθp⟩)
  obtain ⟨_,_,_,_,_,hQ,_⟩ := search_randomized_search_contract A hA hproper 1 (by omega)
  have hchecked := search_checked_random_attempt hN A 1 (by omega)
  refine ⟨by norm_num [ExponentialSizes, ExponentialWidth], by simpa using hQ,
    by simpa using hchecked.2.2.2, ?_⟩
  rw [hchecked.2.1, hchecked.1]
  have hP : RandomizedSuccess A 1 = (A.card : ℝ) / Fintype.card I := by
    unfold RandomizedSuccess
    norm_num only [Finset.sum_range_one, Nat.cast_one, div_one]
    rw [search_grover_success hN A θ hdensity hs hc 0]
    simpa using hdensity
  rw [hP]

theorem search_phase_mean_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) (s : ℕ) :
    0 ≤ MeanQueries I (ExponentialSizes (Fintype.card I) s) ∧
      MeanQueries I (ExponentialSizes (Fintype.card I) s) ≤ (6/5 : ℝ)^s / 2 := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have hsizes := (search_exponential_schedule _ hN).2.1
  obtain ⟨_,_,_,_,_,hQ,_⟩ := search_randomized_search_contract A hA hproper _ (hsizes s)
  rw [hQ]
  have hone : (1 : ℝ) ≤ ExponentialSizes (Fintype.card I) s := by exact_mod_cast hsizes s
  have hw : 0 ≤ ExponentialWidth (Fintype.card I) s := by
    rw [(search_exponential_schedule _ hN).1]
    exact le_min (by positivity) (Real.sqrt_nonneg _)
  have hceil := Nat.ceil_lt_add_one hw
  have hwidth : ExponentialWidth (Fintype.card I) s ≤ (6/5 : ℝ)^s := by
    rw [(search_exponential_schedule _ hN).1]
    exact min_le_left _ _
  change (Nat.ceil (ExponentialWidth (Fintype.card I) s) : ℝ) < _ at hceil
  constructor <;> dsimp [ExponentialSizes] at * <;> linarith

theorem search_failure_weighted_scale (N t θ : ℝ) (_hN : 0 < N) (_ht : 0 < t)
    (hθ0 : 0 < θ) (hθp : θ < Real.pi / 2) (hdensity : (Real.sin θ)^2 = t/N) :
    (1-t/N) * (1 / Real.sin (2*θ)) ≤ Real.sqrt (N/t) / 2 := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθp⟩
  have hroot : Real.sqrt (N/t) = (Real.sin θ)⁻¹ := by
    have hi : N/t = ((Real.sin θ)^2)⁻¹ := by rw [hdensity, inv_div]
    rw [hi, Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hs]
  have hcos : 1-t/N = (Real.cos θ)^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    _ = Real.cos θ / (2*Real.sin θ) := by
      rw [hcos, Real.sin_two_mul]
      field_simp
    _ ≤ 1 / (2*Real.sin θ) := div_le_div_of_nonneg_right (Real.cos_le_one θ) (by positivity)
    _ = _ := by rw [hroot]; ring

theorem search_phase_prefix_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) (n : ℕ) :
    RetryPhasePrefixCost A (ExponentialSizes (Fintype.card I)) n ≤
      (9/2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have hNr : (0 : ℝ) < Fintype.card I := by exact_mod_cast hN
  have hAr : (0 : ℝ) < A.card := by exact_mod_cast hA
  let sizes := ExponentialSizes (Fintype.card I)
  let δ : ℝ := 1 - (A.card : ℝ) / Fintype.card I
  have hsizes : ∀ k, 0 < sizes k := (search_exponential_schedule _ hN).2.1
  have hinit := search_initial_trial A hA hproper
  have hδ : 0 ≤ δ := by
    change 0 ≤ 1 - (A.card : ℝ) / Fintype.card I
    rw [← hinit.2.2.2]
    exact (search_checked_random_attempt hN A 1 (by omega)).2.2.1.2
  have hreachone : RetryReach A sizes 1 = δ := by
    simp only [RetryReach, Finset.prod_range_one]
    change CheckedFailure A (ExponentialSizes (Fintype.card I) 0) = δ
    rw [hinit.1]
    exact hinit.2.2.2
  have hreach (s : ℕ) (hs : 0 < s) : RetryReach A sizes s ≤ δ := by
    rw [← hreachone]
    exact search_retry_reach_mono hN A sizes hsizes 1 s hs
  have hcost (s : ℕ) : 0 ≤ MeanQueries I (sizes s) ∧
      MeanQueries I (sizes s) ≤ (6/5 : ℝ)^s / 2 := search_phase_mean_bound A hA hproper s
  have hterm (s : ℕ) : 0 ≤ RetryReach A sizes s * MeanQueries I (sizes s) :=
    mul_nonneg (search_retry_prefix hN A sizes hsizes s).1 (hcost s).1
  obtain ⟨θ,hθ0,hθp,hdensity,L,hL,hLhi,hlarge⟩ := search_critical_stage A hA hproper
  have hweighted := search_weighted_retry_tail A hA hproper θ hθ0 hθp hdensity sizes hsizes L hlarge
  have htail (k : ℕ) : RetryReach A sizes (L+k) ≤ δ * (3/4 : ℝ)^k :=
    (hweighted k).trans (mul_le_mul_of_nonneg_right (hreach L hL) (by positivity))
  have hbefore : RetryPhasePrefixCost A sizes L ≤ (5/2 : ℝ) * δ * (6/5 : ℝ)^L := by
    unfold RetryPhasePrefixCost
    calc
      _ ≤ ∑ s ∈ Finset.range L, (δ/2) * (6/5 : ℝ)^s := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : s = 0
        · subst s
          have hz : MeanQueries I (sizes 0) = 0 := by
            change MeanQueries I (ExponentialSizes (Fintype.card I) 0) = 0
            rw [hinit.1, hinit.2.1]
          rw [hz, mul_zero]
          positivity
        · calc
            _ ≤ δ * MeanQueries I (sizes s) := mul_le_mul_of_nonneg_right (hreach s (by omega)) (hcost s).1
            _ ≤ δ * ((6/5 : ℝ)^s / 2) := mul_le_mul_of_nonneg_left (hcost s).2 hδ
            _ = _ := by ring
      _ = (δ/2) * (∑ s ∈ Finset.range L, (6/5 : ℝ)^s) := by rw [Finset.mul_sum]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (search_geometric_sums L).1 hδ]
  have hafter (m : ℕ) : (∑ k ∈ Finset.range m,
      RetryReach A sizes (L+k) * MeanQueries I (sizes (L+k))) ≤ 5 * δ * (6/5 : ℝ)^L := by
    calc
      _ ≤ ∑ k ∈ Finset.range m, (δ * (6/5 : ℝ)^L / 2) * (9/10 : ℝ)^k := by
        apply Finset.sum_le_sum
        intro k _
        have hpow : (3/4 : ℝ)^k * (6/5 : ℝ)^k = (9/10 : ℝ)^k := by
          rw [← mul_pow]
          norm_num
        calc
          _ ≤ (δ * (3/4 : ℝ)^k) * MeanQueries I (sizes (L+k)) :=
            mul_le_mul_of_nonneg_right (htail k) (hcost (L+k)).1
          _ ≤ (δ * (3/4 : ℝ)^k) * ((6/5 : ℝ)^(L+k) / 2) :=
            mul_le_mul_of_nonneg_left (hcost (L+k)).2 (mul_nonneg hδ (by positivity))
          _ = _ := by rw [pow_add, ← hpow]; ring
      _ = (δ * (6/5 : ℝ)^L / 2) * (∑ k ∈ Finset.range m, (9/10 : ℝ)^k) := by rw [Finset.mul_sum]
      _ ≤ _ := by
        have hp : 0 ≤ δ * (6/5 : ℝ)^L / 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (search_geometric_sums m).2 hp]
  have hmono : RetryPhasePrefixCost A sizes n ≤ RetryPhasePrefixCost A sizes (L+n) := by
    unfold RetryPhasePrefixCost
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : n ≤ L+n))
    intro s _ _
    exact hterm s
  have hdecomp : RetryPhasePrefixCost A sizes (L+n) = RetryPhasePrefixCost A sizes L +
      ∑ k ∈ Finset.range n, RetryReach A sizes (L+k) * MeanQueries I (sizes (L+k)) :=
    Finset.sum_range_add _ _ _
  rw [hdecomp] at hmono
  have htotal : RetryPhasePrefixCost A sizes n ≤ (15/2 : ℝ)*δ*(6/5 : ℝ)^L := by
    linarith [hbefore, hafter n]
  have hscale := search_failure_weighted_scale (Fintype.card I) A.card θ hNr hAr hθ0 hθp hdensity
  calc
    _ ≤ (15/2 : ℝ)*δ*(6/5 : ℝ)^L := htotal
    _ ≤ 9 * (δ * (1 / Real.sin (2*θ))) := by
      nlinarith [mul_le_mul_of_nonneg_left hLhi hδ]
    _ ≤ _ := by dsimp [δ]; nlinarith [hscale]

theorem search_expected_grover_iterations {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ∃ q : ℝ, HasSum (fun s => RetryReach A (ExponentialSizes (Fintype.card I)) s *
      MeanQueries I (ExponentialSizes (Fintype.card I) s)) q ∧
      0 ≤ q ∧ q ≤ (9/2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have hsizes := (search_exponential_schedule _ hN).2.1
  have hnonneg (s : ℕ) : 0 ≤ RetryReach A (ExponentialSizes (Fintype.card I)) s *
      MeanQueries I (ExponentialSizes (Fintype.card I) s) :=
    mul_nonneg (search_retry_prefix hN A _ hsizes s).1 (search_phase_mean_bound A hA hproper s).1
  have hbound (n : ℕ) : (∑ s ∈ Finset.range n,
      RetryReach A (ExponentialSizes (Fintype.card I)) s * MeanQueries I (ExponentialSizes (Fintype.card I) s)) ≤
      (9/2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := search_phase_prefix_bound A hA hproper n
  have hsummable := summable_of_sum_range_le hnonneg hbound
  exact ⟨_, hsummable.hasSum, tsum_nonneg hnonneg, hsummable.tsum_le_of_sum_range_le hbound⟩

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
