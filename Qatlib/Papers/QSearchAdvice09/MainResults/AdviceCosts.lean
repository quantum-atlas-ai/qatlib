/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSearchAdvice09.MainResults.Basic
public import Qatlib.Papers.QSearchAdvice09.MainResults.Prop32
public import Qatlib.Papers.QSearchAdvice09.MainResults.AmpLaw

@[expose] public section


/-!
# Finite execution costs for advice search

Fixed source: Montanaro, *Quantum search with advice*, arXiv:0908.3066v1,
Appendix A.2, pp.11–13. PDF SHA-256:
`9fb2a2e59e0aa61da9d0cbd7991f8ad24016ff3c365415551ff31944dd25d6a6`.

This module proves `prop_3_2` with its
original signature. The probability of each round is derived from the average
of squared amplitudes. A first-success telescoping identity converts the
finite cost expression to the expected costs of rounds actually reached.
The initial failure factor cancels the apparent singularity as the marked
probability approaches one; subsequent rounds have a geometric failure tail.

Boundary: `alg3QueryModel` is the frozen finite expected-cost expression.
Its final search term is the real value π√n/4, without the integer ceiling
present in the source. Thus this theorem proves both numerical bounds for
that model; full Algorithm 3 resource coverage still requires the sampling,
query ledger, and final exact-search construction with its integer rounding.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Qatlib.Papers.QSearchAdvice09.MainResults

namespace Qatlib.Papers.QSearchAdvice09.MainResults

/-- The average amplification law is the average of actual squared amplitudes. -/
theorem avg_as_sum (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hm : 0 < m) :
    ampAvgSuccessProb p m =
      (1 / (m : ℝ)) * ∑ r ∈ Finset.range m,
        Real.sin ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt p)) ^ 2 := by
  have hs : Real.sin (Real.arcsin (Real.sqrt p)) = Real.sqrt p :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg p]) (Real.sqrt_le_one.mpr hp1.le)
  have hc : Real.cos (Real.arcsin (Real.sqrt p)) = Real.sqrt (1 - p) := by
    rw [Real.cos_arcsin, Real.sq_sqrt hp.le]
  have ht : Real.sin (Real.arcsin (Real.sqrt p)) *
      Real.cos (Real.arcsin (Real.sqrt p)) = Real.sqrt (p * (1 - p)) := by
    rw [hs, hc, Real.sqrt_mul hp.le]
  have hpos : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (by positivity)
  rw [average_amp_success _ m hm (by rw [ht]; exact hpos.ne')]
  unfold ampAvgSuccessProb
  rw [show 8 * (m : ℝ) * Real.sin (Real.arcsin (Real.sqrt p)) *
      Real.cos (Real.arcsin (Real.sqrt p)) =
      8 * (m : ℝ) * Real.sqrt (p * (1 - p)) by rw [← ht]; ring]

/-- A round's success probability lies in the probability interval. -/
theorem avg_mem (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hm : 0 < m) :
    0 ≤ ampAvgSuccessProb p m ∧ ampAvgSuccessProb p m ≤ 1 := by
  rw [avg_as_sum p hp hp1 m hm]
  have hsum : (∑ r ∈ Finset.range m,
      Real.sin ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt p)) ^ 2) ≤ m := by
    calc
      _ ≤ ∑ _r ∈ Finset.range m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        exact Real.sin_sq_le_one _
      _ = m := by simp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · positivity
  · calc
      _ ≤ (1 / (m : ℝ)) * m := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := by field_simp

/-- The first amplification round consists of sampling the prepared state. -/
theorem avg_one (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ampAvgSuccessProb p 1 = p := by
  rw [avg_as_sum p hp hp1 1 (by omega)]
  simp only [Nat.cast_one, div_one, one_mul, Finset.range_one, Finset.sum_singleton,
    Nat.cast_zero, mul_zero, zero_add]
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg p])
    (Real.sqrt_le_one.mpr hp1.le), Real.sq_sqrt hp.le]

/-- Beyond the spectral threshold every amplification round succeeds at least one quarter. -/
theorem avg_quarter (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hm : 0 < m)
    (h : 1 ≤ 2 * (m : ℝ) * Real.sqrt (p * (1 - p))) :
    1 / 4 ≤ ampAvgSuccessProb p m := by
  unfold ampAvgSuccessProb
  have hd : 0 < 8 * (m : ℝ) * Real.sqrt (p * (1 - p)) := by positivity
  have hs := Real.sin_le_one (4 * (m : ℝ) * Real.arcsin (Real.sqrt p))
  have hdiv : Real.sin (4 * (m : ℝ) * Real.arcsin (Real.sqrt p)) /
      (8 * (m : ℝ) * Real.sqrt (p * (1 - p))) ≤ 1 / 4 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  linarith

/-- Failure products describe the probability of reaching each execution round. -/
def reach (P : ℕ → ℝ) (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (1 - P i)

/-- The first-success cost sum equals the expected sum of costs of reached rounds. -/
theorem cost_telescope (P c : ℕ → ℝ) (N : ℕ) (F : ℝ) :
    (∑ j ∈ Finset.range N, reach P j * P j * ∑ i ∈ Finset.range (j + 1), c i) +
      reach P N * ((∑ i ∈ Finset.range N, c i) + F) =
    (∑ i ∈ Finset.range N, reach P i * c i) + reach P N * F := by
  have hmain : ∀ N : ℕ,
      (∑ j ∈ Finset.range N, reach P j * P j * ∑ i ∈ Finset.range (j + 1), c i) +
        reach P N * (∑ i ∈ Finset.range N, c i) =
      ∑ i ∈ Finset.range N, reach P i * c i := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      simp only [Finset.sum_range_succ] at ih
      have hr : reach P (N + 1) = reach P N * (1 - P N) := by
        simp [reach, Finset.prod_range_succ]
      rw [hr]
      linear_combination ih
  linear_combination hmain N

/-- Reach probabilities are nonnegative. -/
theorem reach_nonneg (P : ℕ → ℝ) (hP1 : ∀ i, P i ≤ 1) (j : ℕ) :
    0 ≤ reach P j := by
  apply Finset.prod_nonneg
  intro i _
  linarith [hP1 i]

/-- Reaching a later round requires failure of the first round. -/
theorem reach_first (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) : reach P j ≤ 1 - P 0 := by
  induction j, hj using Nat.le_induction with
  | base => simp [reach]
  | succ j hj ih =>
    have hrec : reach P (j + 1) = reach P j * (1 - P j) := by
      simp [reach, Finset.prod_range_succ]
    rw [hrec]
    calc
      _ ≤ reach P j * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [hP0 j]) (reach_nonneg P hP1 j)
      _ ≤ 1 - P 0 := by simpa using ih

/-- The first-round failure factor is retained in the geometric tail. -/
theorem reach_decay (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hq : ∀ i, j0 ≤ i → 1 / 4 ≤ P i) (t : ℕ) :
    reach P (j0 + t) ≤ (1 - P 0) * (3 / 4) ^ t := by
  induction t with
  | zero => simpa using reach_first P hP0 hP1 j0 hj0
  | succ t ih =>
    have hrec : reach P (j0 + (t + 1)) = reach P (j0 + t) * (1 - P (j0 + t)) := by
      rw [← Nat.add_assoc]
      simp [reach, Finset.prod_range_succ]
    rw [hrec, pow_succ, ← mul_assoc]
    apply mul_le_mul ih
    · linarith [hq (j0 + t) (by omega)]
    · linarith [hP1 (j0 + t)]
    · exact mul_nonneg (by linarith [hP1 0]) (by positivity)

/-- A finite nonnegative geometric series is bounded by its infinite sum. -/
theorem geom_bound (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, r ^ i ≤ 1 / (1 - r) := by
  rw [geom_sum_eq (ne_of_lt hr1)]
  have heq : (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) := by
    field_simp [sub_ne_zero.mpr hr1.ne, sub_ne_zero.mpr hr1.ne']
    ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith [pow_nonneg hr0 N]

/-- The prefix has only one round without the initial failure factor. -/
theorem reach_prefix (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (j : ℕ) :
    (∑ i ∈ Finset.range j, reach P i * algThreeK ^ i) ≤
      1 + (1 - P 0) * ∑ i ∈ Finset.range j, algThreeK ^ i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    by_cases hj : j = 0
    · subst j
      simp [reach]
      linarith [hP1 0]
    · have hterm := mul_le_mul_of_nonneg_right
        (reach_first P hP0 hP1 j (by omega))
          (pow_nonneg (by norm_num [algThreeK] : (0 : ℝ) ≤ algThreeK) j)
      linarith

/-- Weighted geometric round costs have a uniformly bounded prefix and tail. -/
theorem reach_cost_sum (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hq : ∀ i, j0 ≤ i → 1 / 4 ≤ P i) (N : ℕ) :
    (∑ i ∈ Finset.range N, reach P i * algThreeK ^ i) ≤
      1 + (1 - P 0) * algThreeK ^ j0 *
        (1 / (algThreeK - 1) + 1 / (1 - 3 * algThreeK / 4)) := by
  have hk : 0 ≤ algThreeK := by norm_num [algThreeK]
  have hf : 0 ≤ 1 - P 0 := by linarith [hP1 0]
  have hpre := reach_prefix P hP0 hP1 j0
  have hgeo : (∑ i ∈ Finset.range j0, algThreeK ^ i) ≤
      algThreeK ^ j0 / (algThreeK - 1) := by
    rw [geom_sum_eq (by norm_num [algThreeK] : algThreeK ≠ 1)]
    apply div_le_div_of_nonneg_right _ (by norm_num [algThreeK])
    linarith
  have htail : (∑ t ∈ Finset.range N, reach P (j0 + t) * algThreeK ^ (j0 + t)) ≤
      (1 - P 0) * algThreeK ^ j0 / (1 - 3 * algThreeK / 4) := by
    calc
      _ ≤ ∑ t ∈ Finset.range N,
          ((1 - P 0) * algThreeK ^ j0) * (3 * algThreeK / 4) ^ t := by
        apply Finset.sum_le_sum
        intro t _
        calc
          _ ≤ ((1 - P 0) * (3 / 4) ^ t) * algThreeK ^ (j0 + t) :=
            mul_le_mul_of_nonneg_right (reach_decay P hP0 hP1 j0 hj0 hq t)
              (pow_nonneg hk _)
          _ = _ := by rw [pow_add, show 3 * algThreeK / 4 = (3 / 4) * algThreeK by ring,
            mul_pow]; ring
      _ = ((1 - P 0) * algThreeK ^ j0) *
          ∑ t ∈ Finset.range N, (3 * algThreeK / 4) ^ t := by rw [Finset.mul_sum]
      _ ≤ ((1 - P 0) * algThreeK ^ j0) * (1 / (1 - 3 * algThreeK / 4)) :=
        mul_le_mul_of_nonneg_left
          (geom_bound _ (by norm_num [algThreeK]) (by norm_num [algThreeK]) N)
          (mul_nonneg hf (pow_nonneg hk _))
      _ = _ := by ring
  have hext : (∑ i ∈ Finset.range N, reach P i * algThreeK ^ i) ≤
      ∑ i ∈ Finset.range (j0 + N), reach P i * algThreeK ^ i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro i _ _
    exact mul_nonneg (reach_nonneg P hP1 i) (pow_nonneg hk _)
  rw [Finset.sum_range_add] at hext
  have hpre' : (∑ i ∈ Finset.range j0, reach P i * algThreeK ^ i) ≤
      1 + (1 - P 0) * (algThreeK ^ j0 / (algThreeK - 1)) := by
    exact hpre.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hgeo hf))
  calc
    _ ≤ (1 + (1 - P 0) * (algThreeK ^ j0 / (algThreeK - 1))) +
        (1 - P 0) * algThreeK ^ j0 / (1 - 3 * algThreeK / 4) :=
      hext.trans (add_le_add hpre' htail)
    _ = _ := by ring

/-- The remaining search is bounded after multiplying by its reach probability. -/
theorem reach_power (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i) (hP1 : ∀ i, P i ≤ 1)
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hq : ∀ i, j0 ≤ i → 1 / 4 ≤ P i)
    (N : ℕ) (hN : 1 ≤ N) :
    reach P N * algThreeK ^ N ≤ (1 - P 0) * algThreeK ^ j0 := by
  have hk : 0 ≤ algThreeK := by norm_num [algThreeK]
  have hf : 0 ≤ 1 - P 0 := by linarith [hP1 0]
  by_cases hnj : N ≤ j0
  · apply mul_le_mul (reach_first P hP0 hP1 N hN)
      (pow_le_pow_right₀ algThreeK_bounds.1.le hnj) (pow_nonneg hk _) hf
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (by omega : j0 ≤ N)
    calc
      _ ≤ ((1 - P 0) * (3 / 4) ^ t) * algThreeK ^ (j0 + t) :=
        mul_le_mul_of_nonneg_right (reach_decay P hP0 hP1 j0 hj0 hq t)
          (pow_nonneg hk _)
      _ = ((1 - P 0) * algThreeK ^ j0) * (3 * algThreeK / 4) ^ t := by
        rw [pow_add, show 3 * algThreeK / 4 = (3 / 4) * algThreeK by ring, mul_pow]
        ring
      _ ≤ ((1 - P 0) * algThreeK ^ j0) * 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_one₀ (by norm_num [algThreeK]) (by norm_num [algThreeK]))
          (mul_nonneg hf (pow_nonneg hk _))
      _ = _ := by ring

/-- The amplification schedule crosses the quarter-success threshold with controlled overshoot. -/
theorem threshold (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ j0 : ℕ, 1 ≤ j0 ∧
      algThreeK ^ j0 ≤ algThreeK / Real.sqrt (p * (1 - p)) ∧
      ∀ i, j0 ≤ i → 1 / 4 ≤ ampAvgSuccessProb p (Nat.floor (algThreeK ^ i)) := by
  let s := Real.sqrt (p * (1 - p))
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = p * (1 - p) := Real.sq_sqrt (by positivity)
  have hs1 : s ≤ 1 / 2 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hx : (1 : ℝ) ≤ 1 / s := (le_div_iff₀ hs).mpr (by linarith)
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hx algThreeK_bounds.1
  refine ⟨j + 1, by omega, ?_, ?_⟩
  · rw [pow_succ]
    calc
      _ ≤ (1 / s) * algThreeK :=
        mul_le_mul_of_nonneg_right hj (by norm_num [algThreeK])
      _ = _ := by ring
  · intro i hi
    have hki : 1 / s < algThreeK ^ i :=
      hj'.trans_le (pow_le_pow_right₀ algThreeK_bounds.1.le hi)
    have hfloor : algThreeK ^ i < (Nat.floor (algThreeK ^ i) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hmul : 1 < algThreeK ^ i * s := (div_lt_iff₀ hs).mp hki
    have hmul' : algThreeK ^ i * s < ((Nat.floor (algThreeK ^ i) : ℝ) + 1) * s :=
      mul_lt_mul_of_pos_right hfloor hs
    have hm : 0 < Nat.floor (algThreeK ^ i) :=
      Nat.floor_pos.mpr (one_le_pow₀ algThreeK_bounds.1.le)
    apply avg_quarter p hp hp1 _ hm
    change 1 ≤ 2 * (Nat.floor (algThreeK ^ i) : ℝ) * s
    nlinarith

/-- The log-based stopping index brackets the uniform-search scale. -/
theorem stop_bracket (n : ℕ) (hn : 0 < n) :
    let J := Nat.floor (Real.logb algThreeK (Real.sqrt (n : ℝ)))
    algThreeK ^ J ≤ Real.sqrt (n : ℝ) ∧
      Real.sqrt (n : ℝ) < algThreeK ^ (J + 1) := by
  let J := Nat.floor (Real.logb algThreeK (Real.sqrt (n : ℝ)))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hl : 0 ≤ Real.logb algThreeK (Real.sqrt (n : ℝ)) :=
    Real.logb_nonneg algThreeK_bounds.1 (Real.one_le_sqrt.mpr hnR)
  have hlo : (J : ℝ) ≤ Real.logb algThreeK (Real.sqrt (n : ℝ)) := Nat.floor_le hl
  have hhi : Real.logb algThreeK (Real.sqrt (n : ℝ)) < ((J + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one (Real.logb algThreeK (Real.sqrt (n : ℝ)))
  constructor
  · have h := (Real.le_logb_iff_rpow_le algThreeK_bounds.1 hs).mp hlo
    simpa only [Real.rpow_natCast] using h
  · have h := (Real.logb_lt_iff_lt_rpow algThreeK_bounds.1 hs).mp hhi
    simpa only [Real.rpow_natCast] using h

/-- The finite first-success model counts precisely the rounds reached by the execution. -/
theorem model_cost (n : ℕ) (p : ℝ) :
    let P := fun i => ampAvgSuccessProb p (Nat.floor (algThreeK ^ i))
    let J := Nat.floor (Real.logb algThreeK (Real.sqrt (n : ℝ)))
    alg3QueryModel algThreeK p n =
      (∑ i ∈ Finset.range (J + 1), reach P i *
        ((((Nat.floor (algThreeK ^ i) : ℕ) : ℝ) + 3) / 2)) +
      reach P (J + 1) * (Real.pi / 4 * Real.sqrt (n : ℝ)) := by
  dsimp only
  unfold alg3QueryModel alg3IterationCost iterCount
  simpa only [reach] using
    cost_telescope (fun i => ampAvgSuccessProb p (Nat.floor (algThreeK ^ i)))
      (fun i => (((Nat.floor (algThreeK ^ i) : ℕ) : ℝ) + 3) / 2)
      (Nat.floor (Real.logb algThreeK (Real.sqrt (n : ℝ))) + 1)
      (Real.pi / 4 * Real.sqrt (n : ℝ))

/-- The finite expected cost has the advice-sensitive square-root bound. -/
theorem model_advice (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    alg3QueryModel algThreeK p n ≤ 83 / Real.sqrt p + 4 / 3 := by
  let P := fun i => ampAvgSuccessProb p (Nat.floor (algThreeK ^ i))
  let J := Nat.floor (Real.logb algThreeK (Real.sqrt (n : ℝ)))
  let c := fun i => (((Nat.floor (algThreeK ^ i) : ℕ) : ℝ) + 3) / 2
  have hk : 0 ≤ algThreeK := by norm_num [algThreeK]
  have hm : ∀ i, 0 < Nat.floor (algThreeK ^ i) :=
    fun i => Nat.floor_pos.mpr (one_le_pow₀ algThreeK_bounds.1.le)
  have hP0 : ∀ i, 0 ≤ P i := fun i => (avg_mem p hp hp1 _ (hm i)).1
  have hP1 : ∀ i, P i ≤ 1 := fun i => (avg_mem p hp hp1 _ (hm i)).2
  have hP : P 0 = p := by simpa [P] using avg_one p hp hp1
  obtain ⟨j0, hj0, hpow, hq⟩ := threshold p hp hp1
  have hstop := (stop_bracket n hn).2
  change Real.sqrt (n : ℝ) < algThreeK ^ (J + 1) at hstop
  have hc : ∀ i, c i ≤ 2 * algThreeK ^ i := by
    intro i
    have hfloor := Nat.floor_le (pow_nonneg hk i)
    have hone := one_le_pow₀ algThreeK_bounds.1.le (n := i)
    dsimp only [c]
    linarith
  have hsum : (∑ i ∈ Finset.range (J + 1), reach P i * c i) ≤
      2 * (1 + (1 - P 0) * algThreeK ^ j0 *
        (1 / (algThreeK - 1) + 1 / (1 - 3 * algThreeK / 4))) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (J + 1), 2 * (reach P i * algThreeK ^ i) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left (hc i) (reach_nonneg P hP1 i)
      _ = 2 * ∑ i ∈ Finset.range (J + 1), reach P i * algThreeK ^ i := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (reach_cost_sum P hP0 hP1 j0 hj0 hq (J + 1)) (by norm_num)
  have hres : reach P (J + 1) * (Real.pi / 4 * Real.sqrt (n : ℝ)) ≤
      (Real.pi / 4) * ((1 - P 0) * algThreeK ^ j0) := by
    calc
      _ = (Real.pi / 4) * (reach P (J + 1) * Real.sqrt (n : ℝ)) := by ring
      _ ≤ (Real.pi / 4) * (reach P (J + 1) * algThreeK ^ (J + 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hstop.le (reach_nonneg P hP1 _)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (reach_power P hP0 hP1 j0 hj0 hq (J + 1) (by omega)) (by positivity)
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (by positivity)
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hcancel : (1 - p) / Real.sqrt (p * (1 - p)) ≤ 1 / Real.sqrt p := by
    have hf : 0 ≤ 1 - p := by linarith
    have hsq : ((1 - p) * Real.sqrt p) ^ 2 ≤ Real.sqrt (p * (1 - p)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hp.le, Real.sq_sqrt (by positivity)]
      nlinarith [mul_nonneg hp.le hf]
    have hlin := (sq_le_sq₀ (mul_nonneg hf hsp.le) hs.le).mp hsq
    apply (div_le_div_iff₀ hs hsp).mpr
    simpa only [one_mul] using hlin
  have hfpow : (1 - P 0) * algThreeK ^ j0 ≤ algThreeK / Real.sqrt p := by
    rw [hP]
    calc
      _ ≤ (1 - p) * (algThreeK / Real.sqrt (p * (1 - p))) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
      _ = algThreeK * ((1 - p) / Real.sqrt (p * (1 - p))) := by ring
      _ ≤ algThreeK * (1 / Real.sqrt p) := mul_le_mul_of_nonneg_left hcancel hk
      _ = _ := by ring
  let C : ℝ := 2 * (1 / (algThreeK - 1) + 1 / (1 - 3 * algThreeK / 4)) + Real.pi / 4
  have hC : 0 ≤ C := by
    dsimp only [C]
    have : 0 < Real.pi := Real.pi_pos
    norm_num [algThreeK]
    positivity
  have hconst : algThreeK * C ≤ 40 := by
    dsimp only [C]
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    norm_num [algThreeK]
    linarith
  have hmodel := model_cost n p
  change alg3QueryModel algThreeK p n =
    (∑ i ∈ Finset.range (J + 1), reach P i * c i) +
      reach P (J + 1) * (Real.pi / 4 * Real.sqrt (n : ℝ)) at hmodel
  have hmain : alg3QueryModel algThreeK p n ≤ 2 + 40 / Real.sqrt p := by
    calc
      _ ≤ 2 + ((1 - P 0) * algThreeK ^ j0) * C := by
        rw [hmodel]
        dsimp only [C]
        linarith [hsum, hres]
      _ ≤ 2 + (algThreeK / Real.sqrt p) * C :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hfpow hC)
      _ = 2 + (algThreeK * C) / Real.sqrt p := by ring
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hconst hsp.le)
  have hinv : (1 : ℝ) ≤ 1 / Real.sqrt p :=
    (le_div_iff₀ hsp).mpr (by simpa using Real.sqrt_le_one.mpr hp1.le)
  simp only [div_eq_mul_inv] at hinv hmain ⊢
  linarith

/-- The deterministic truncation gives the uniform-search branch. -/
theorem model_uniform (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    alg3QueryModel algThreeK p n ≤ 53 * Real.sqrt (n : ℝ) := by
  let P := fun i => ampAvgSuccessProb p (Nat.floor (algThreeK ^ i))
  let J := Nat.floor (Real.logb algThreeK (Real.sqrt (n : ℝ)))
  have hk : 0 ≤ algThreeK := by norm_num [algThreeK]
  have hm : ∀ i, 0 < Nat.floor (algThreeK ^ i) :=
    fun i => Nat.floor_pos.mpr (one_le_pow₀ algThreeK_bounds.1.le)
  have hP0 : ∀ i, 0 ≤ P i := fun i => (avg_mem p hp hp1 _ (hm i)).1
  have hP1 : ∀ i, P i ≤ 1 := fun i => (avg_mem p hp hp1 _ (hm i)).2
  have hr : ∀ i, reach P i ≤ 1 := prod_one_sub_le_one P hP0 hP1
  have hmodel := model_cost n p
  have hupper : alg3QueryModel algThreeK p n ≤
      roundCost algThreeK (J + 1) + Real.pi / 4 * Real.sqrt (n : ℝ) := by
    rw [hmodel]
    apply add_le_add
    · unfold roundCost
      apply Finset.sum_le_sum
      intro i _
      have h : 0 ≤ (((Nat.floor (algThreeK ^ i) : ℕ) : ℝ) + 3) / 2 := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hr i) h
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right (hr (J + 1)) (by positivity :
        0 ≤ Real.pi / 4 * Real.sqrt (n : ℝ))
  have hstop := (stop_bracket n hn).1
  change algThreeK ^ J ≤ Real.sqrt (n : ℝ) at hstop
  have hround := roundCost_le (J + 1)
  have hpw : algThreeK ^ (J + 1) ≤ algThreeK * Real.sqrt (n : ℝ) := by
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left hstop hk
  have hdiv := div_le_div_of_nonneg_right hpw (by norm_num [algThreeK] : 0 ≤ algThreeK - 1)
  have hcoef : algThreeK / (algThreeK - 1) + Real.pi / 4 ≤ 53 := by
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    norm_num [algThreeK]
    linarith
  calc
    _ ≤ algThreeK * Real.sqrt (n : ℝ) / (algThreeK - 1) +
        Real.pi / 4 * Real.sqrt (n : ℝ) := hupper.trans (add_le_add (hround.trans hdiv) le_rfl)
    _ = (algThreeK / (algThreeK - 1) + Real.pi / 4) * Real.sqrt (n : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)

end Qatlib.Papers.QSearchAdvice09.MainResults
