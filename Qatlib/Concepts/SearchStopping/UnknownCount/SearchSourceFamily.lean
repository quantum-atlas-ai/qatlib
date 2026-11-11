/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSourceSchedule
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchQueryCost
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchTimeout

/-!
# Expected costs and output laws for search schedules

Analyzes the capped exponential schedule for every growth factor `1 < l < 4 / 3`. The results
establish almost-sure termination and uniform marked output, then bound expected iteration,
attempt, Boolean-query, and lookup costs using `SourcePhaseConstant`.

The same analysis gives uniform geometric timeout bounds and evaluates the constants for the
factor `6 / 5` schedule. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `search_source_terminal_output_nonempty`: For `1 < l < 4 / 3` and any nonempty marked set, the
  terminal output law is uniform on that set.
* `search_source_terminal_boolean_cost`: For `1 < l < 4 / 3` and any nonempty marked set, the
  expected terminal Boolean-query cost exists and is at most `(1 + 3 * SourcePhaseConstant l) *
  √(N / t)`.
* `search_source_terminal_lookup_cost`: For `1 < l < 4 / 3` and any nonempty marked set, the
  expected source-lookup clock exists and is at most `(1 + 4 * SourcePhaseConstant l) * √(N /
  t)`.
* `search_source_uniform_timeout`: For `1 < l < 4 / 3` on a nonempty search space, a common
  stage offset `K ≤ l / (l - 1) * √N` gives worst-prefix cost at most `(l / (l - 1) + k) * √N`
  and reach probability at most `(3 / 4) ^ k` for every nonempty marked set.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Concepts.SearchStopping.UnknownCount

set_option linter.unusedSectionVars false

open scoped BigOperators
open Filter

/-- The real-valued coefficient `(l / 4) * (1 / (l - 1) + 4 / (4 - 3 * l))` used in expected
Grover-iteration bounds. -/
noncomputable def SourcePhaseConstant (l : ℝ) : ℝ :=
  (l / 4) * (1 / (l - 1) + 4 / (4 - 3 * l))

section Family

variable (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3)
include hl hl4

/-- For `1 < l < 4 / 3`, the coefficient `SourcePhaseConstant l` is nonnegative. -/
theorem search_source_constant_nonneg : 0 ≤ SourcePhaseConstant l := by
  have ha : 0 < l - 1 := by linarith
  have hb : 0 < 4 - 3 * l := by linarith
  unfold SourcePhaseConstant
  positivity

/-- For `1 < l < 4 / 3`, finite sums of `l ^ k` and `(3 * l / 4) ^ k` satisfy the bounds `l ^ n
/ (l - 1)` and `4 / (4 - 3 * l)`, respectively. -/
theorem search_source_geometric_sums (n : ℕ) :
    (∑ k ∈ Finset.range n, l ^ k) ≤ l ^ n / (l - 1) ∧
    (∑ k ∈ Finset.range n, (3 * l / 4) ^ k) ≤ 4 / (4 - 3 * l) := by
  have ha : 0 < l - 1 := by linarith
  have hb : 0 < 4 - 3 * l := by linarith
  have hbefore (k : ℕ) : (l - 1) * (∑ s ∈ Finset.range k, l ^ s) = l ^ k - 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linear_combination ih
  have htail (k : ℕ) :
      (4 - 3 * l) * (∑ s ∈ Finset.range k, (3 * l / 4) ^ s) =
        4 * (1 - (3 * l / 4) ^ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linear_combination ih
  constructor
  · apply (le_div_iff₀ ha).2
    nlinarith only [hbefore n]
  · apply (le_div_iff₀ hb).2
    have hp : 0 ≤ (3 * l / 4) ^ n := pow_nonneg (by linarith) _
    nlinarith only [htail n, hp]

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, there are a density angle and a
positive stage after which every search range reaches `1 / Real.sin (2 * θ)`, with the
stated bound on `l ^ L`. -/
theorem search_source_critical_stage {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ) ∧
      ∃ L : ℕ, 0 < L ∧ l ^ L ≤ l * (1 / Real.sin (2 * θ)) ∧
        ∀ k, L ≤ k → 1 / Real.sin (2 * θ) ≤ (SourceSizes (Fintype.card I) l k : ℝ) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  obtain ⟨θ, hθ0, hθp, hdensity, _⟩ := search_principal_angle A hA hproper
  have hscale := search_integer_cap (Fintype.card I) A.card hA hproper θ hθ0 hθp hdensity
  obtain ⟨L, hL, hlo, hhi⟩ := search_source_first_scale_crossing l hl
    (1 / Real.sin (2 * θ)) hscale.1
  refine ⟨θ, hθ0, hθp, hdensity, L, hL, hhi, ?_⟩
  intro k hk
  have hp : l ^ L ≤ l ^ k := by
    have heq : k = L + (k - L) := by omega
    rw [heq, pow_add]
    exact le_mul_of_one_le_right (pow_nonneg (by linarith) _) (one_le_pow₀ hl.le)
  change _ ≤ (Nat.ceil (SourceWidths (Fintype.card I) l k) : ℝ)
  apply le_trans _ (Nat.le_ceil _)
  rw [(search_source_schedule_laws _ hN l hl.le).1]
  exact le_min (hlo.trans hp) hscale.2

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the initial range has size one, zero
mean Grover iterations, one checked mean query, and failure probability `1 - A.card /
Fintype.card I`. -/
theorem search_source_initial_trial {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    SourceSizes (Fintype.card I) l 0 = 1 ∧ MeanQueries I 1 = 0 ∧
      CheckedMeanQueries I 1 = 1 ∧ CheckedFailure A 1 = 1 - (A.card : ℝ) / Fintype.card I := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  obtain ⟨θ,hθ0,hθp,hdensity,h2⟩ := search_principal_angle A hA hproper
  have hs : Real.sin θ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθp⟩)
  obtain ⟨_,_,_,_,_,hQ,_⟩ := search_randomized_search_contract A hA hproper 1 (by omega)
  have hchecked := search_checked_random_attempt hN A 1 (by omega)
  refine ⟨by norm_num [SourceSizes, SourceWidths], by simpa using hQ,
    by simpa using hchecked.2.2.2, ?_⟩
  rw [hchecked.2.1, hchecked.1]
  have hP : RandomizedSuccess A 1 = (A.card : ℝ) / Fintype.card I := by
    unfold RandomizedSuccess
    norm_num only [Finset.sum_range_one, Nat.cast_one, div_one]
    rw [search_grover_success hN A θ hdensity hs hc 0]
    simpa using hdensity
  rw [hP]

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the mean Grover-iteration cost at
stage `s` is nonnegative and at most `l ^ s / 2`. -/
theorem search_source_phase_mean_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) (s : ℕ) :
    0 ≤ MeanQueries I (SourceSizes (Fintype.card I) l s) ∧
      MeanQueries I (SourceSizes (Fintype.card I) l s) ≤ l^s / 2 := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
  obtain ⟨_,_,_,_,_,hQ,_⟩ := search_randomized_search_contract A hA hproper _ (hsizes s)
  rw [hQ]
  have hone : (1 : ℝ) ≤ SourceSizes (Fintype.card I) l s := by exact_mod_cast hsizes s
  have hw : 0 ≤ SourceWidths (Fintype.card I) l s := by
    rw [(search_source_schedule_laws _ hN l hl.le).1]
    exact le_min (by positivity) (Real.sqrt_nonneg _)
  have hceil := Nat.ceil_lt_add_one hw
  have hwidth : SourceWidths (Fintype.card I) l s ≤ l^s := by
    rw [(search_source_schedule_laws _ hN l hl.le).1]
    exact min_le_left _ _
  change (Nat.ceil (SourceWidths (Fintype.card I) l s) : ℝ) < _ at hceil
  constructor <;> dsimp [SourceSizes] at * <;> linarith

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the first-success masses of the
parameterized retry schedule sum to one. -/
theorem search_source_all_density_termination {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    HasSum (RetryFirstSuccess A (SourceSizes (Fintype.card I) l)) 1 := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  let sizes := SourceSizes (Fintype.card I) l
  have hsizes : ∀ k, 0 < sizes k := (search_source_schedule_laws _ hN l hl.le).2.1
  obtain ⟨θ,hθ0,hθp,hdensity,L,hL,hLhi,hlarge⟩ := search_source_critical_stage l hl hl4 A hA hproper
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

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, every expected phase-cost prefix is at
most `SourcePhaseConstant l * √(N / t)`, where `N` is the search-space size and `t` the
marked count. -/
theorem search_source_phase_prefix_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) (n : ℕ) :
    RetryPhasePrefixCost A (SourceSizes (Fintype.card I) l) n ≤
      SourcePhaseConstant l * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have hNr : (0 : ℝ) < Fintype.card I := by exact_mod_cast hN
  have hAr : (0 : ℝ) < A.card := by exact_mod_cast hA
  have ha : 0 < l - 1 := by linarith
  have hb : 0 < 4 - 3 * l := by linarith
  let sizes := SourceSizes (Fintype.card I) l
  let δ : ℝ := 1 - (A.card : ℝ) / Fintype.card I
  let D : ℝ := 1 / (l - 1) + 4 / (4 - 3 * l)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsizes : ∀ k, 0 < sizes k := (search_source_schedule_laws _ hN l hl.le).2.1
  have hinit := search_source_initial_trial l hl hl4 A hA hproper
  have hδ : 0 ≤ δ := by
    change 0 ≤ 1 - (A.card : ℝ) / Fintype.card I
    rw [← hinit.2.2.2]
    exact (search_checked_random_attempt hN A 1 (by omega)).2.2.1.2
  have hreachone : RetryReach A sizes 1 = δ := by
    simp only [RetryReach, Finset.prod_range_one]
    change CheckedFailure A (SourceSizes (Fintype.card I) l 0) = δ
    rw [hinit.1]
    exact hinit.2.2.2
  have hreach (s : ℕ) (hs : 0 < s) : RetryReach A sizes s ≤ δ := by
    rw [← hreachone]
    exact search_retry_reach_mono hN A sizes hsizes 1 s hs
  have hcost (s : ℕ) : 0 ≤ MeanQueries I (sizes s) ∧ MeanQueries I (sizes s) ≤ l ^ s / 2 :=
    search_source_phase_mean_bound l hl hl4 A hA hproper s
  have hterm (s : ℕ) : 0 ≤ RetryReach A sizes s * MeanQueries I (sizes s) :=
    mul_nonneg (search_retry_prefix hN A sizes hsizes s).1 (hcost s).1
  obtain ⟨θ, hθ0, hθp, hdensity, L, hL, hLhi, hlarge⟩ :=
    search_source_critical_stage l hl hl4 A hA hproper
  have hweighted := search_weighted_retry_tail A hA hproper θ hθ0 hθp hdensity sizes hsizes L hlarge
  have htail (k : ℕ) : RetryReach A sizes (L + k) ≤ δ * (3 / 4 : ℝ) ^ k :=
    (hweighted k).trans (mul_le_mul_of_nonneg_right (hreach L hL) (by positivity))
  have hbefore : RetryPhasePrefixCost A sizes L ≤ (δ / 2) * (l ^ L / (l - 1)) := by
    unfold RetryPhasePrefixCost
    calc
      _ ≤ ∑ s ∈ Finset.range L, (δ / 2) * l ^ s := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : s = 0
        · subst s
          have hz : MeanQueries I (sizes 0) = 0 := by
            change MeanQueries I (SourceSizes (Fintype.card I) l 0) = 0
            rw [hinit.1, hinit.2.1]
          rw [hz, mul_zero]
          positivity
        · calc
            _ ≤ δ * MeanQueries I (sizes s) :=
              mul_le_mul_of_nonneg_right (hreach s (by omega)) (hcost s).1
            _ ≤ δ * (l ^ s / 2) := mul_le_mul_of_nonneg_left (hcost s).2 hδ
            _ = _ := by ring
      _ = (δ / 2) * (∑ s ∈ Finset.range L, l ^ s) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (search_source_geometric_sums l hl hl4 L).1
        (by positivity)
  have hafter (m : ℕ) : (∑ k ∈ Finset.range m,
      RetryReach A sizes (L + k) * MeanQueries I (sizes (L + k))) ≤
        (δ * l ^ L / 2) * (4 / (4 - 3 * l)) := by
    calc
      _ ≤ ∑ k ∈ Finset.range m, (δ * l ^ L / 2) * (3 * l / 4) ^ k := by
        apply Finset.sum_le_sum
        intro k _
        have hpow : (3 / 4 : ℝ) ^ k * l ^ k = (3 * l / 4) ^ k := by
          rw [← mul_pow]
          congr 1
          ring
        calc
          _ ≤ (δ * (3 / 4 : ℝ) ^ k) * MeanQueries I (sizes (L + k)) :=
            mul_le_mul_of_nonneg_right (htail k) (hcost (L + k)).1
          _ ≤ (δ * (3 / 4 : ℝ) ^ k) * (l ^ (L + k) / 2) :=
            mul_le_mul_of_nonneg_left (hcost (L + k)).2 (mul_nonneg hδ (by positivity))
          _ = _ := by rw [pow_add, ← hpow]; ring
      _ = (δ * l ^ L / 2) * (∑ k ∈ Finset.range m, (3 * l / 4) ^ k) :=
        by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (search_source_geometric_sums l hl hl4 m).2
        (by positivity)
  have hmono : RetryPhasePrefixCost A sizes n ≤ RetryPhasePrefixCost A sizes (L + n) := by
    unfold RetryPhasePrefixCost
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : n ≤ L + n))
    intro s _ _
    exact hterm s
  have hdecomp : RetryPhasePrefixCost A sizes (L + n) = RetryPhasePrefixCost A sizes L +
      ∑ k ∈ Finset.range n, RetryReach A sizes (L + k) * MeanQueries I (sizes (L + k)) :=
    Finset.sum_range_add _ _ _
  rw [hdecomp] at hmono
  have htotal : RetryPhasePrefixCost A sizes n ≤ (δ * l ^ L / 2) * D := by
    have h := hmono.trans (add_le_add hbefore (hafter n))
    convert! h using 1
    (try dsimp [D])
    ring
  have hscale := search_failure_weighted_scale (Fintype.card I) A.card θ hNr hAr hθ0 hθp hdensity
  calc
    _ ≤ (δ * l ^ L / 2) * D := htotal
    _ ≤ (δ * (l * (1 / Real.sin (2 * θ))) / 2) * D :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLhi hδ) (by norm_num)) hD
    _ = (l / 2 * D) * (δ * (1 / Real.sin (2 * θ))) := by ring
    _ ≤ (l / 2 * D) * (Real.sqrt ((Fintype.card I : ℝ) / A.card) / 2) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by dsimp [SourcePhaseConstant, D]; ring

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the reach-weighted mean iteration
costs have a nonnegative sum bounded by `SourcePhaseConstant l * √(N / t)`. -/
theorem search_source_expected_grover_iterations {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ∃ q : ℝ, HasSum (fun s => RetryReach A (SourceSizes (Fintype.card I) l) s *
      MeanQueries I (SourceSizes (Fintype.card I) l s)) q ∧
      0 ≤ q ∧ q ≤ (SourcePhaseConstant l) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
  have hnonneg (s : ℕ) : 0 ≤ RetryReach A (SourceSizes (Fintype.card I) l) s *
      MeanQueries I (SourceSizes (Fintype.card I) l s) :=
    mul_nonneg (search_retry_prefix hN A _ hsizes s).1 (search_source_phase_mean_bound l hl hl4 A hA hproper s).1
  have hbound (n : ℕ) : (∑ s ∈ Finset.range n,
      RetryReach A (SourceSizes (Fintype.card I) l) s * MeanQueries I (SourceSizes (Fintype.card I) l s)) ≤
      (SourcePhaseConstant l) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := search_source_phase_prefix_bound l hl hl4 A hA hproper n
  have hsummable := summable_of_sum_range_le hnonneg hbound
  exact ⟨_, hsummable.hasSum, tsum_nonneg hnonneg, hsummable.tsum_le_of_sum_range_le hbound⟩

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the terminal iteration-cost series has
a nonnegative sum bounded by the reach-weighted mean series and by `SourcePhaseConstant l *
√(N / t)`. -/
theorem search_source_terminal_iteration_mean {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ∃ q : ℝ, HasSum (TerminalIterationCost A (SourceSizes (Fintype.card I) l)) q ∧
      0 ≤ q ∧ q ≤ (∑' n, RetryReach A (SourceSizes (Fintype.card I) l) n *
        MeanQueries I (SourceSizes (Fintype.card I) l n)) ∧
      q ≤ (SourcePhaseConstant l)*Real.sqrt ((Fintype.card I : ℝ)/A.card) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  let sizes := SourceSizes (Fintype.card I) l
  have hsizes : ∀ n, 0 < sizes n := (search_source_schedule_laws _ hN l hl.le).2.1
  have hterminal (n : ℕ) : 0 ≤ TerminalIterationCost A sizes n := by
    unfold TerminalIterationCost
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg ((search_terminal_stage_law hN A sizes hsizes n).1 x).1 (Nat.cast_nonneg _)
  have hlive (n : ℕ) : 0 ≤ LiveIterationCost A sizes n := by
    unfold LiveIterationCost
    apply Finset.sum_nonneg
    intro h _
    exact mul_nonneg ((search_failure_history_law hN A sizes hsizes n).1 h) (Nat.cast_nonneg _)
  obtain ⟨q0,hq0,hq0nn,hq0bound⟩ := search_source_expected_grover_iterations l hl hl4 A hA hproper
  have hocc (n : ℕ) : 0 ≤ RetryReach A sizes n * MeanQueries I (sizes n) :=
    mul_nonneg (search_retry_prefix hN A sizes hsizes n).1
      (search_source_phase_mean_bound l hl hl4 A hA hproper n).1
  have hprefix (n : ℕ) : (∑ s ∈ Finset.range n, TerminalIterationCost A sizes s) ≤ q0 := by
    have hb := search_truncated_iteration_balance hN A sizes hsizes n
    have ho : RetryPhasePrefixCost A sizes n ≤ q0 := by
      have h := hq0.summable.sum_le_tsum (Finset.range n) (fun k _ => hocc k)
      rw [hq0.tsum_eq] at h
      exact h
    linarith [hlive n]
  have hsum := summable_of_sum_range_le hterminal hprefix
  have hqle := hsum.tsum_le_of_sum_range_le hprefix
  refine ⟨_,hsum.hasSum,tsum_nonneg hterminal,?_,hqle.trans hq0bound⟩
  rw [hq0.tsum_eq]
  exact hqle

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, terminal trace masses are nonnegative,
sum to one, and vanish on traces with unmarked outputs. -/
theorem search_source_terminal_law {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    HasSum (TerminalMass A (SourceSizes (Fintype.card I) l)) 1 ∧
    ∀ x : TerminalTrace I (SourceSizes (Fintype.card I) l),
      0 ≤ TerminalMass A (SourceSizes (Fintype.card I) l) x ∧
      (TerminalOutput x ∉ A → TerminalMass A (SourceSizes (Fintype.card I) l) x = 0) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
  have hp (x : TerminalTrace I (SourceSizes (Fintype.card I) l)) :
      0 ≤ TerminalMass A (SourceSizes (Fintype.card I) l) x ∧
      (TerminalOutput x ∉ A → TerminalMass A (SourceSizes (Fintype.card I) l) x = 0) :=
    (search_terminal_stage_law hN A _ hsizes x.1).1 x.2
  refine ⟨?_,hp⟩
  apply search_nonnegative_trace_sum _ (fun x => (hp x).1) 1
  change HasSum (fun n => ∑ x : TerminalStage I (SourceSizes (Fintype.card I) l) n,
    TerminalStageMass A (SourceSizes (Fintype.card I) l) n x) 1
  simp_rw [(search_terminal_stage_law hN A _ hsizes _).2]
  exact search_source_all_density_termination l hl hl4 A hA hproper

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, summing the stagewise output mass
gives `1 / A.card` at each marked address and zero elsewhere. -/
theorem search_source_final_output_uniform {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) (i : I) :
    HasSum (fun s => RetryOutputMass A (SourceSizes (Fintype.card I) l) s i)
      (if i ∈ A then 1 / (A.card : ℝ) else 0) := by
  have heach := search_stage_output_uniform A hA hproper (SourceSizes (Fintype.card I) l)
  simp_rw [heach]
  by_cases hi : i ∈ A
  · simp only [if_pos hi]
    exact (search_source_all_density_termination l hl hl4 A hA hproper).div_const _
  · simp only [if_neg hi]
    exact hasSum_zero

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the terminal trace law induces the
uniform distribution on marked addresses. -/
theorem search_source_terminal_output {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) (i : I) :
    HasSum (fun x : TerminalTrace I (SourceSizes (Fintype.card I) l) =>
      if TerminalOutput x = i then TerminalMass A (SourceSizes (Fintype.card I) l) x else 0)
      (if i ∈ A then 1/(A.card : ℝ) else 0) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  let sizes := SourceSizes (Fintype.card I) l
  have hsizes : ∀ k, 0 < sizes k := (search_source_schedule_laws _ hN l hl.le).2.1
  apply search_nonnegative_trace_sum
  · intro x
    split_ifs
    · exact ((search_source_terminal_law l hl hl4 A hA hproper).2 x).1
    · exact le_rfl
  · have hrow (n : ℕ) : (∑ x : TerminalStage I sizes n,
        if TerminalOutput ⟨n,x⟩ = i then TerminalMass A sizes ⟨n,x⟩ else 0) = RetryOutputMass A sizes n i := by
      simp only [TerminalOutput, TerminalMass]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact search_terminal_output_marginal hN A sizes hsizes n i
    change HasSum (fun n => ∑ x : TerminalStage I sizes n,
      if TerminalOutput ⟨n,x⟩ = i then TerminalMass A sizes ⟨n,x⟩ else 0) _
    simp_rw [hrow]
    exact search_source_final_output_uniform l hl hl4 A hA hproper i

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the trace-weighted total iteration
cost has a nonnegative sum bounded by the reach-weighted mean series and by
`SourcePhaseConstant l * √(N / t)`. -/
theorem search_source_terminal_cost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (SourceSizes (Fintype.card I) l) =>
      TerminalMass A (SourceSizes (Fintype.card I) l) x *
        (TerminalCost (SourceSizes (Fintype.card I) l) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (∑' n, RetryReach A (SourceSizes (Fintype.card I) l) n *
        MeanQueries I (SourceSizes (Fintype.card I) l n)) ∧
      q ≤ (SourcePhaseConstant l)*Real.sqrt ((Fintype.card I : ℝ)/A.card) := by
  obtain ⟨q,hq,hqnn,hqocc,hqbound⟩ := search_source_terminal_iteration_mean l hl hl4 A hA hproper
  refine ⟨q,?_,hqnn,hqocc,hqbound⟩
  apply search_nonnegative_trace_sum
  · intro x
    exact mul_nonneg ((search_source_terminal_law l hl hl4 A hA hproper).2 x).1 (Nat.cast_nonneg _)
  · exact hq

/-- For `1 < l < 4 / 3` on a nonempty search space, the initial-stage output mass is `1 /
Fintype.card I` at marked addresses and zero elsewhere. -/
theorem search_source_initial_output {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (i : I) :
    RetryOutputMass A (SourceSizes (Fintype.card I) l) 0 i =
      if i ∈ A then 1 / (Fintype.card I : ℝ) else 0 := by
  simp only [RetryOutputMass, RetryReach, Finset.range_zero, Finset.prod_empty, one_mul]
  have hs : SourceSizes (Fintype.card I) l 0 = 1 := by
    norm_num [SourceSizes, SourceWidths]
  rw [hs]
  simp only [Finset.sum_range_one, Nat.cast_one, div_one]
  rw [(search_checked_attempt hN A 0).2.1 i]
  have hz : SearchState A 0 = Uniform I := rfl
  rw [hz, search_uniform_born]

/-- For `1 < l < 4 / 3` on a nonempty search space with every address marked, each terminal
trace has zero mass-weighted Grover iteration cost. -/
theorem search_source_univ_weighted_cost {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (x : TerminalTrace I (SourceSizes (Fintype.card I) l)) :
    TerminalMass (Finset.univ : Finset I) (SourceSizes (Fintype.card I) l) x *
      (TerminalCost (SourceSizes (Fintype.card I) l) x : ℝ) = 0 := by
  by_cases hx : x.1 = 0
  · rcases x with ⟨n,h,j,i⟩
    dsimp at hx
    subst n
    have hj : j.val = 0 := by
      have hjlt := j.isLt
      norm_num [SourceSizes, SourceWidths] at hjlt
      exact hjlt
    simp [TerminalCost, TerminalIterations, HistoryIterations, hj]
  · rw [search_univ_terminal_later hN _ (search_source_schedule_laws _ hN l hl.le).2.1 x hx,
      zero_mul]

/-- For `1 < l < 4 / 3`, the first-success masses sum to one for every nonempty marked set,
including the full search space. -/
theorem search_source_termination_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    HasSum (RetryFirstSuccess A (SourceSizes (Fintype.card I) l)) 1 := by
  by_cases hp : A.card < Fintype.card I
  · exact search_source_all_density_termination l hl hl4 A hA hp
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hN : 0 < Fintype.card I := by simpa using hA
    have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
    change HasSum (fun n => RetryFirstSuccess (Finset.univ : Finset I)
      (SourceSizes (Fintype.card I) l) n) 1
    simp_rw [search_univ_first_success hN _ hsizes]
    exact hasSum_ite_eq 0 1

/-- For `1 < l < 4 / 3` and any nonempty marked set, terminal trace masses form a normalized
nonnegative law supported on marked outputs. -/
theorem search_source_terminal_law_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    HasSum (TerminalMass A (SourceSizes (Fintype.card I) l)) 1 ∧
    ∀ x : TerminalTrace I (SourceSizes (Fintype.card I) l),
      0 ≤ TerminalMass A (SourceSizes (Fintype.card I) l) x ∧
      (TerminalOutput x ∉ A → TerminalMass A (SourceSizes (Fintype.card I) l) x = 0) := by
  have hN : 0 < Fintype.card I := lt_of_lt_of_le hA (Finset.card_le_univ A)
  have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
  have hp (x : TerminalTrace I (SourceSizes (Fintype.card I) l)) :
      0 ≤ TerminalMass A (SourceSizes (Fintype.card I) l) x ∧
      (TerminalOutput x ∉ A → TerminalMass A (SourceSizes (Fintype.card I) l) x = 0) :=
    (search_terminal_stage_law hN A _ hsizes x.1).1 x.2
  refine ⟨?_,hp⟩
  apply search_nonnegative_trace_sum _ (fun x => (hp x).1) 1
  change HasSum (fun n => ∑ x : TerminalStage I (SourceSizes (Fintype.card I) l) n,
    TerminalStageMass A (SourceSizes (Fintype.card I) l) n x) 1
  simp_rw [(search_terminal_stage_law hN A _ hsizes _).2]
  exact search_source_termination_nonempty l hl hl4 A hA

/-- For `1 < l < 4 / 3` and any nonempty marked set, the expected terminal Grover-iteration cost
exists, is nonnegative, and is at most `SourcePhaseConstant l * √(N / t)`. -/
theorem search_source_terminal_cost_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (SourceSizes (Fintype.card I) l) =>
      TerminalMass A (SourceSizes (Fintype.card I) l) x *
        (TerminalCost (SourceSizes (Fintype.card I) l) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (SourcePhaseConstant l)*Real.sqrt ((Fintype.card I : ℝ)/A.card) := by
  have hC := search_source_constant_nonneg l hl hl4
  by_cases hp : A.card < Fintype.card I
  · obtain ⟨q,hq,hq0,_,hb⟩ := search_source_terminal_cost l hl hl4 A hA hp
    exact ⟨q,hq,hq0,hb⟩
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hN : 0 < Fintype.card I := by simpa using hA
    refine ⟨0,?_,le_rfl,by positivity⟩
    simp_rw [search_source_univ_weighted_cost l hl hl4 hN]
    exact hasSum_zero

/-- For `1 < l < 4 / 3` on a nonempty space with every address marked, output mass is uniform at
stage zero and is zero at all later stages. -/
theorem search_source_univ_retry_output {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (n : ℕ) (i : I) :
    RetryOutputMass (Finset.univ : Finset I) (SourceSizes (Fintype.card I) l) n i =
      if n = 0 then 1 / (Fintype.card I : ℝ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simpa using search_source_initial_output l hl hl4 hN Finset.univ i
  · have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
    have hr := search_univ_first_success hN (SourceSizes (Fintype.card I) l) hsizes n
    rw [RetryFirstSuccess, (search_univ_failure hN _ (hsizes n)).1, mul_one, if_neg hn] at hr
    rw [RetryOutputMass, hr, zero_mul, if_neg hn]

/-- For `1 < l < 4 / 3` and any nonempty marked set, the terminal output law is uniform on that
set. See [NayakWu1998]. -/
theorem search_source_terminal_output_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (i : I) :
    HasSum (fun x : TerminalTrace I (SourceSizes (Fintype.card I) l) =>
      if TerminalOutput x = i then TerminalMass A (SourceSizes (Fintype.card I) l) x else 0)
      (if i ∈ A then 1 / (A.card : ℝ) else 0) := by
  by_cases hp : A.card < Fintype.card I
  · exact search_source_terminal_output l hl hl4 A hA hp i
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hN : 0 < Fintype.card I := by simpa using hA
    let sizes := SourceSizes (Fintype.card I) l
    have hsizes : ∀ k, 0 < sizes k := (search_source_schedule_laws _ hN l hl.le).2.1
    apply search_nonnegative_trace_sum
    · intro x
      split_ifs
      · exact ((search_source_terminal_law_nonempty l hl hl4 Finset.univ hA).2 x).1
      · exact le_rfl
    · have hrow (n : ℕ) : (∑ x : TerminalStage I sizes n,
          if TerminalOutput ⟨n,x⟩ = i then TerminalMass Finset.univ sizes ⟨n,x⟩ else 0) =
          RetryOutputMass Finset.univ sizes n i := by
        simp only [TerminalOutput, TerminalMass]
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact search_terminal_output_marginal hN Finset.univ sizes hsizes n i
      change HasSum (fun n => ∑ x : TerminalStage I sizes n,
        if TerminalOutput ⟨n,x⟩ = i then TerminalMass Finset.univ sizes ⟨n,x⟩ else 0) _
      simp_rw [hrow]
      simp only [sizes, search_source_univ_retry_output l hl hl4 hN, Finset.mem_univ, if_true,
          Finset.card_univ]
      exact hasSum_ite_eq 0 _

/-- For `1 < l < 4 / 3`, search spaces of size at least two have parameterized stage ranges of
size at least two at every positive stage. -/
theorem search_source_later_size_ge_two (N k : ℕ) (hN : 2 ≤ N) (hk : 0 < k) :
    2 ≤ SourceSizes N l k := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hroot : 1 < Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N)]
  have hp : 1 < l^k := one_lt_pow₀ hl hk.ne'
  have hw : 1 < SourceWidths N l k := by
    rw [(search_source_schedule_laws N (by omega) l hl.le).1]
    exact lt_min hp hroot
  have h : 1 < Nat.ceil (SourceWidths N l k) := Nat.lt_ceil.mpr (by simpa using hw)
  exact h

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the sum of stage reach probabilities
before stage `n` is at most one plus twice the expected phase-cost prefix. -/
theorem search_source_attempt_prefix_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hp : A.card < Fintype.card I) (n : ℕ) :
    (∑ s ∈ Finset.range n, RetryReach A (SourceSizes (Fintype.card I) l) s) ≤
      1 + 2 * RetryPhasePrefixCost A (SourceSizes (Fintype.card I) l) n := by
  have hN : 0 < Fintype.card I := lt_trans hA hp
  let sizes := SourceSizes (Fintype.card I) l
  have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
  have hterm (s : ℕ) : RetryReach A sizes s ≤
      (if s = 0 then 1 else 0) + 2 * (RetryReach A sizes s * MeanQueries I (sizes s)) := by
    have hr := (search_retry_prefix hN A sizes hsizes s).1
    have hc := (search_source_phase_mean_bound l hl hl4 A hA hp s).1
    by_cases hs : s = 0
    · subst s
      simp only [RetryReach, Finset.range_zero, Finset.prod_empty, ite_true, one_mul]
      linarith
    · rw [if_neg hs, zero_add]
      have hm : 2 ≤ sizes s := search_source_later_size_ge_two l hl hl4 _ s (by omega) (by omega)
      obtain ⟨_,_,_,_,_,hQ,_⟩ := search_randomized_search_contract A hA hp (sizes s) (hsizes s)
      have hmr : (2 : ℝ) ≤ sizes s := by exact_mod_cast hm
      have hmean : 1 ≤ 2 * MeanQueries I (sizes s) := by rw [hQ]; linarith
      nlinarith [mul_le_mul_of_nonneg_left hmean hr]
  calc
    _ ≤ ∑ s ∈ Finset.range n,
        ((if s = 0 then 1 else 0) + 2 * (RetryReach A sizes s * MeanQueries I (sizes s))) :=
      Finset.sum_le_sum (fun s _ => hterm s)
    _ = (∑ s ∈ Finset.range n, (if s = 0 then (1 : ℝ) else 0)) +
        2 * RetryPhasePrefixCost A sizes n := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    _ ≤ _ := by
      simp only [Finset.sum_ite_eq', Finset.mem_range]
      split_ifs <;> linarith

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the expected number of terminal
attempts exists and is at most `1 + 2 * SourcePhaseConstant l * √(N / t)`. -/
theorem search_source_terminal_attempts {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hp : A.card < Fintype.card I) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (SourceSizes (Fintype.card I) l) =>
      TerminalMass A (SourceSizes (Fintype.card I) l) x * ((x.1 + 1 : ℕ) : ℝ)) q ∧
      0 ≤ q ∧ q ≤ 1 + 2 * SourcePhaseConstant l * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have hN : 0 < Fintype.card I := lt_trans hA hp
  let sizes := SourceSizes (Fintype.card I) l
  have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
  have hnn (n : ℕ) : 0 ≤ RetryFirstSuccess A sizes n * ((n : ℝ)+1) :=
    mul_nonneg (search_retry_prefix hN A sizes hsizes n).2.2.2 (by positivity)
  have hb (n : ℕ) : (∑ s ∈ Finset.range n, RetryFirstSuccess A sizes s * ((s : ℝ)+1)) ≤
      1 + 2 * SourcePhaseConstant l * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
    have hc := search_attempt_count_balance hN A sizes hsizes n
    have ht := search_source_attempt_prefix_bound l hl hl4 A hA hp n
    have hi := search_source_phase_prefix_bound l hl hl4 A hA hp n
    have hlive : 0 ≤ (n : ℝ) * RetryReach A sizes n :=
      mul_nonneg (Nat.cast_nonneg n) (search_retry_prefix hN A sizes hsizes n).1
    change (∑ s ∈ Finset.range n, RetryReach A sizes s) ≤ _ at ht
    change RetryPhasePrefixCost A sizes n ≤ _ at hi
    linarith
  have hsum := summable_of_sum_range_le hnn hb
  refine ⟨_,?_,tsum_nonneg hnn,hsum.tsum_le_of_sum_range_le hb⟩
  apply search_nonnegative_trace_sum
  · intro x
    exact mul_nonneg ((search_source_terminal_law l hl hl4 A hA hp).2 x).1 (Nat.cast_nonneg _)
  · change HasSum (fun n => ∑ x : TerminalStage I sizes n,
      TerminalStageMass A sizes n x * ((n+1 : ℕ) : ℝ)) _
    simp_rw [← Finset.sum_mul, (search_terminal_stage_law hN A sizes hsizes _).2, Nat.cast_add,
        Nat.cast_one]
    exact hsum.hasSum

/-- For `1 < l < 4 / 3` and a nonempty proper marked set, the expected cost `c * TerminalCost +
attempts` is nonnegative and at most `(1 + 2 * SourcePhaseConstant l + c *
SourcePhaseConstant l) * √(N / t)`. -/
theorem search_source_terminal_linear_cost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hp : A.card < Fintype.card I) (c : ℕ) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (SourceSizes (Fintype.card I) l) =>
      TerminalMass A (SourceSizes (Fintype.card I) l) x *
        ((c * TerminalCost (SourceSizes (Fintype.card I) l) x + (x.1+1) : ℕ) : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (1 + 2 * SourcePhaseConstant l + (c : ℝ) * (SourcePhaseConstant l)) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  obtain ⟨qi,hi,hi0,_,hib⟩ := search_source_terminal_cost l hl hl4 A hA hp
  obtain ⟨qa,ha,ha0,hab⟩ := search_source_terminal_attempts l hl hl4 A hA hp
  have hAr : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hNr : (A.card : ℝ) ≤ Fintype.card I := by exact_mod_cast (Finset.card_le_univ A)
  have hd : 1 ≤ (Fintype.card I : ℝ) / A.card :=
    (le_div_iff₀ hAr).2 (by simpa only [one_mul] using hNr)
  have hsqrt : 1 ≤ Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
    nlinarith [Real.sqrt_nonneg ((Fintype.card I : ℝ) / A.card),
      Real.sq_sqrt (show 0 ≤ (Fintype.card I : ℝ) / A.card by positivity)]
  refine ⟨(c : ℝ)*qi+qa,?_,by positivity,?_⟩
  · have h := (hi.mul_left (c : ℝ)).add ha
    convert! h using 1
    funext x
    push_cast
    ring
  · have hmul := mul_le_mul_of_nonneg_left hib (Nat.cast_nonneg c)
    nlinarith

/-- For `1 < l < 4 / 3` and any nonempty marked set, the expected cost `c * TerminalCost +
attempts` is nonnegative and satisfies the coefficient bound `(1 + 2 * SourcePhaseConstant l
+ c * SourcePhaseConstant l) * √(N / t)`. -/
theorem search_source_terminal_linear_cost_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (c : ℕ) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (SourceSizes (Fintype.card I) l) =>
      TerminalMass A (SourceSizes (Fintype.card I) l) x *
        ((c * TerminalCost (SourceSizes (Fintype.card I) l) x + (x.1+1) : ℕ) : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (1 + 2 * SourcePhaseConstant l + (c : ℝ) * (SourcePhaseConstant l)) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have hC := search_source_constant_nonneg l hl hl4
  by_cases hp : A.card < Fintype.card I
  · exact search_source_terminal_linear_cost l hl hl4 A hA hp c
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hN : 0 < Fintype.card I := by simpa using hA
    have hNr : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨1,?_,by norm_num,?_⟩
    · have heq (x : TerminalTrace I (SourceSizes (Fintype.card I) l)) :
          TerminalMass Finset.univ (SourceSizes (Fintype.card I) l) x *
            ((c * TerminalCost (SourceSizes (Fintype.card I) l) x + (x.1+1) : ℕ) : ℝ) =
          TerminalMass Finset.univ (SourceSizes (Fintype.card I) l) x := by
        by_cases hx : x.1 = 0
        · have hz := search_source_univ_weighted_cost l hl hl4 hN x
          push_cast
          rw [hx]
          push_cast
          nlinarith [hz]
        · rw [search_univ_terminal_later hN _ (search_source_schedule_laws _ hN l hl.le).2.1 x hx]
          ring
      simp_rw [heq]
      exact (search_source_terminal_law_nonempty l hl hl4 Finset.univ hA).1
    · simp only [Finset.card_univ, div_self hNr, Real.sqrt_one, mul_one]
      have hc : 0 ≤ (c : ℝ) := Nat.cast_nonneg c
      nlinarith [mul_nonneg hc hC]

/-- For `1 < l < 4 / 3` and any nonempty marked set, the expected terminal Boolean-query cost
exists and is at most `(1 + 3 * SourcePhaseConstant l) * √(N / t)`. See [NayakWu1998]. -/
theorem search_source_terminal_boolean_cost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (SourceSizes (Fintype.card I) l) =>
      TerminalMass A (SourceSizes (Fintype.card I) l) x *
        (TerminalBooleanQueries (SourceSizes (Fintype.card I) l) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (1 + 3 * SourcePhaseConstant l) *
        Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have h := search_source_terminal_linear_cost_nonempty l hl hl4 A hA 1
  simpa only [Nat.cast_one, one_mul, Nat.one_mul, TerminalBooleanQueries,
    show 1 + 2 * SourcePhaseConstant l + SourcePhaseConstant l =
      1 + 3 * SourcePhaseConstant l by ring] using h

/-- For `1 < l < 4 / 3` and any nonempty marked set, the expected source-lookup clock exists and
is at most `(1 + 4 * SourcePhaseConstant l) * √(N / t)`. -/
theorem search_source_terminal_lookup_cost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (SourceSizes (Fintype.card I) l) =>
      TerminalMass A (SourceSizes (Fintype.card I) l) x *
        (SourceLookupClock (SourceSizes (Fintype.card I) l) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (1 + 4 * SourcePhaseConstant l) *
        Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have h := search_source_terminal_linear_cost_nonempty l hl hl4 A hA 2
  simpa only [Nat.cast_ofNat, SourceLookupClock,
    show 1 + 2 * SourcePhaseConstant l + 2 * SourcePhaseConstant l =
      1 + 4 * SourcePhaseConstant l by ring] using h

/-- For `1 < l < 4 / 3` and positive `N`, the largest sampled iteration count is at most the
parameterized real width. -/
theorem search_source_largest_sample_le_width (N s : ℕ) (hN : 0 < N) :
    ((SourceSizes N l s - 1 : ℕ) : ℝ) ≤ SourceWidths N l s := by
  have hs := (search_source_schedule_laws N hN l hl.le).2.1 s
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hw : 0 ≤ SourceWidths N l s := by
    rw [(search_source_schedule_laws N hN l hl.le).1]
    exact le_min (pow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  have hc := Nat.ceil_lt_add_one hw
  change (Nat.ceil (SourceWidths N l s) : ℝ) - 1 ≤ _
  linarith

/-- For `1 < l < 4 / 3` and positive `N`, if `l ^ K ≤ l * Real.sqrt N`, the worst iteration
prefix through `K + k` stages is at most `(l / (l - 1) + k) * Real.sqrt N`. -/
theorem search_source_worst_prefix_cap (N K k : ℕ) (hN : 0 < N)
    (hK : l ^ K ≤ l * Real.sqrt N) :
    (WorstPrefixIterations (SourceSizes N l) (K + k) : ℝ) ≤
      (l / (l - 1) + (k : ℝ)) * Real.sqrt N := by
  have ha : 0 < l - 1 := by linarith
  have hbefore : (∑ s ∈ Finset.range K, ((SourceSizes N l s - 1 : ℕ) : ℝ)) ≤
      l ^ K / (l - 1) := by
    calc
      _ ≤ ∑ s ∈ Finset.range K, l ^ s := by
        apply Finset.sum_le_sum
        intro s _
        apply (search_source_largest_sample_le_width l hl hl4 N s hN).trans
        rw [(search_source_schedule_laws N hN l hl.le).1]
        exact min_le_left _ _
      _ ≤ _ := (search_source_geometric_sums l hl hl4 K).1
  have hafter : (∑ s ∈ Finset.range k, ((SourceSizes N l (K + s) - 1 : ℕ) : ℝ)) ≤
      (k : ℝ) * Real.sqrt N := by
    calc
      _ ≤ ∑ _s ∈ Finset.range k, Real.sqrt N := by
        apply Finset.sum_le_sum
        intro s _
        apply (search_source_largest_sample_le_width l hl hl4 N (K + s) hN).trans
        rw [(search_source_schedule_laws N hN l hl.le).1]
        exact min_le_right _ _
      _ = _ := by simp
  have hbefore' : (∑ s ∈ Finset.range K, ((SourceSizes N l s - 1 : ℕ) : ℝ)) ≤
      l / (l - 1) * Real.sqrt N := by
    calc
      _ ≤ l ^ K / (l - 1) := hbefore
      _ ≤ (l * Real.sqrt N) / (l - 1) := div_le_div_of_nonneg_right hK ha.le
      _ = _ := by ring
  simp only [WorstPrefixIterations, Finset.sum_range_add]
  push_cast
  nlinarith only [hbefore', hafter]

/-- For `1 < l < 4 / 3` on a nonempty search space, a common stage offset `K ≤ l / (l - 1) * √N`
gives worst-prefix cost at most `(l / (l - 1) + k) * √N` and reach probability at most `(3 /
4) ^ k` for every nonempty marked set. -/
theorem search_source_uniform_timeout {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) :
    ∃ K : ℕ, (K : ℝ) ≤ l / (l - 1) * Real.sqrt (Fintype.card I) ∧ ∀ k : ℕ,
      (WorstPrefixIterations (SourceSizes (Fintype.card I) l) (K + k) : ℝ) ≤
        (l / (l - 1) + (k : ℝ)) * Real.sqrt (Fintype.card I) ∧
      ∀ A : Finset I, 0 < A.card →
        RetryReach A (SourceSizes (Fintype.card I) l) (K + k) ≤ (3 / 4 : ℝ) ^ k := by
  have ha : 0 < l - 1 := by linarith
  have hNr : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast hN
  have hroot : 1 ≤ Real.sqrt (Fintype.card I) := by
    nlinarith [Real.sqrt_nonneg (Fintype.card I : ℝ),
      Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I))]
  obtain ⟨K, _, hKlo, hKhi⟩ := search_source_first_scale_crossing l hl
    (Real.sqrt (Fintype.card I)) hroot
  have hcount : (K : ℝ) ≤ l / (l - 1) * Real.sqrt (Fintype.card I) := by
    calc
      _ = ∑ _s ∈ Finset.range K, (1 : ℝ) := by simp
      _ ≤ ∑ s ∈ Finset.range K, l ^ s :=
        Finset.sum_le_sum (fun _ _ => one_le_pow₀ hl.le)
      _ ≤ l ^ K / (l - 1) := (search_source_geometric_sums l hl hl4 K).1
      _ ≤ (l * Real.sqrt (Fintype.card I)) / (l - 1) :=
        div_le_div_of_nonneg_right hKhi ha.le
      _ = _ := by ring
  have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
  have hcap (s : ℕ) (hs : K ≤ s) : Real.sqrt (Fintype.card I) ≤
      (SourceSizes (Fintype.card I) l s : ℝ) := by
    have hp : l ^ K ≤ l ^ s := by
      have heq : s = K + (s - K) := by omega
      rw [heq, pow_add]
      exact le_mul_of_one_le_right (pow_nonneg (by linarith) _) (one_le_pow₀ hl.le)
    apply le_trans _ (Nat.le_ceil _)
    rw [(search_source_schedule_laws _ hN l hl.le).1]
    exact le_min (hKlo.trans hp) le_rfl
  refine ⟨K, hcount, ?_⟩
  intro k
  refine ⟨search_source_worst_prefix_cap l hl hl4 _ K k hN hKhi, ?_⟩
  intro A hA
  by_cases hp : A.card < Fintype.card I
  · obtain ⟨θ, hθ0, hθp, hdensity, _⟩ := search_principal_angle A hA hp
    have hc := (search_integer_cap _ _ hA hp θ hθ0 hθp hdensity).2
    exact (search_retry_tail A hA hp θ hθ0 hθp hdensity _ hsizes K
      (fun s hs => hc.trans (hcap s hs)) k).1
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hr := search_univ_first_success hN _ hsizes (K + k)
    rw [RetryFirstSuccess, (search_univ_failure hN _ (hsizes (K + k))).1, mul_one] at hr
    rw [hr]
    split_ifs with hz
    · have hk : k = 0 := by omega
      simp [hk]
    · positivity

end Family

/-- At `l = 6 / 5`, the phase, Boolean-query, lookup, and timeout coefficients evaluate to `9 /
2`, `29 / 2`, `19`, and `6`, respectively. -/
theorem search_source_constants_instance :
    SourcePhaseConstant (6 / 5) = 9 / 2 ∧
      1 + 3 * SourcePhaseConstant (6 / 5) = 29 / 2 ∧
      1 + 4 * SourcePhaseConstant (6 / 5) = 19 ∧
      (6 / 5 : ℝ) / (6 / 5 - 1) = 6 := by
  norm_num [SourcePhaseConstant]

end Qatlib.Concepts.SearchStopping.UnknownCount
