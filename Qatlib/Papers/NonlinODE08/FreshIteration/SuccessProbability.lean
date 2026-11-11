/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Mathlib.Analysis.MeanInequalities

/-!
# SuccessProbability — success probability of one iteration round and the `m`-round chain

Leyton--Osborne, *A quantum algorithm to solve nonlinear differential equations*,
fixed arXiv:0812.4423v1.

Source location: Appendix A.2, Proposition 1 and its proof, equations (28)--(29).

The paper runs `m` rounds, each with success probability per trial `p = ε²/2`.
For one round with `N` trials and threshold `k = λN`, Hoeffding's inequality
(one-sided, from the shared `ProbabilityCore.Concentration` infrastructure) gives

  `P(failure) ≤ exp(−2 N (p − λ)²)`.

Requiring the per-round failure to be at most `1/m` and using independent rounds
gives `P(all m rounds succeed) ≥ (1 − 1/m)^m`; the paper uses `m ≥ 6` to
conclude `(1 − 1/m)^m ≥ 1/3`.  The last inequality is proved here from the
AM--GM monotonicity of `(1 − 1/n)^n`, with the `m = 6` endpoint checked exactly.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open scoped BigOperators

namespace Qatlib.Papers.NonlinODE08.FreshIteration

/-! ### One-round Bernoulli law and the Hoeffding tail -/

/-- The per-trial Bernoulli law of Algorithm 1: a trial succeeds with
probability `p`. -/
def trialLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FinDist Bool where
  prob b := if b then p else 1 - p
  nonneg b := by
    cases b
    · simpa using sub_nonneg.mpr hp1
    · simpa using hp0
  sum_one := by
    rw [Fintype.sum_bool]
    simp

/-- Indicator of one successful trial, as a real-valued statistic. -/
def successIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- Number of successes in a finite record of trials. -/
def successCount {N : ℕ} (ω : Fin N → Bool) : ℝ := ∑ i, successIndicator (ω i)

/-- The expectation of the Bernoulli indicator is `p`. -/
theorem trialLaw_expect_indicator (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (trialLaw p hp0 hp1).expect successIndicator = p := by
  simp [FinDist.expect, trialLaw, successIndicator]

/-- The expected number of successes in `N` independent trials is `N p`. -/
theorem trialLaw_expect_count (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (independent (fun _ : Fin N => trialLaw p hp0 hp1)).expect
      (fun ω => successCount ω) = (N : ℝ) * p := by
  have h :=
    Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation
      (fun _ : Fin N => trialLaw p hp0 hp1) (fun _ => (1 : ℝ)) (fun _ => successIndicator)
  have h' : (independent (fun _ : Fin N => trialLaw p hp0 hp1)).expect
      (fun ω => weightedSum (fun _ => (1 : ℝ)) (fun _ => successIndicator) ω) =
      (N : ℝ) * p := by
    rw [h]
    simp [trialLaw_expect_indicator, Finset.sum_const, Finset.card_univ]
  simpa only [successCount, weightedSum, one_mul] using h'

/-- The success count is nonnegative. -/
theorem successCount_nonneg {N : ℕ} (ω : Fin N → Bool) : 0 ≤ successCount ω := by
  apply Finset.sum_nonneg
  intro i _
  unfold successIndicator
  split <;> norm_num

/-- The success count is at most the number of trials. -/
theorem successCount_le {N : ℕ} (ω : Fin N → Bool) : successCount ω ≤ (N : ℝ) := by
  calc
    successCount ω ≤ ∑ _ : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      unfold successIndicator
      split <;> norm_num
    _ = (N : ℝ) := by simp

/-- Paper Appendix A.2, the displayed Hoeffding bound: with `N` trials, success
probability `p` and failure threshold `k = λN`, the failure probability is at
most `exp(−2N(p−λ)²)`.  This is the one-sided Hoeffding inequality applied to
the actual independent product law. -/
theorem bernoulli_tail (N : ℕ) (hN : 0 < N) {p lam : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hlam : lam < p) :
    eventMass (independent (fun _ : Fin N => trialLaw p hp0 hp1))
      (fun ω => successCount ω ≤ lam * (N : ℝ)) ≤
      Real.exp (-2 * (N : ℝ) * (p - lam) ^ 2) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hu : 0 < (N : ℝ) * (p - lam) := mul_pos hNpos (sub_pos.mpr hlam)
  have hS : 0 < ∑ i : Fin N, (1 : ℝ) ^ 2 * ((1 : ℝ) - 0) ^ 2 := by
    simpa [Finset.sum_const, Finset.card_univ] using hNpos
  have hf : ∀ i : Fin N, ∀ x : Bool, successIndicator x ∈ Set.Icc (0 : ℝ) 1 := by
    intro i x
    cases x <;> simp [successIndicator]
  have h := independent_weighted_hoeffding_signed
    (fun _ : Fin N => trialLaw p hp0 hp1) (fun _ => (1 : ℝ)) (fun _ => successIndicator)
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) ((N : ℝ) * (p - lam)) (-1)
    (fun _ => by norm_num) hf hu (by norm_num) hS
  have hexp : (independent (fun _ : Fin N => trialLaw p hp0 hp1)).expect
      (fun ω => weightedSum (fun _ => (1 : ℝ)) (fun _ => successIndicator) ω) = (N : ℝ) * p := by
    simpa only [successCount, weightedSum, one_mul] using trialLaw_expect_count N p hp0 hp1
  have hevent : (fun ω : Fin N → Bool => successCount ω ≤ lam * (N : ℝ)) =
      (fun ω => (N : ℝ) * (p - lam) ≤ (-1 : ℝ) *
        (weightedSum (fun _ => (1 : ℝ)) (fun _ => successIndicator) ω -
          (independent (fun _ : Fin N => trialLaw p hp0 hp1)).expect
            (fun ω => weightedSum (fun _ => (1 : ℝ)) (fun _ => successIndicator) ω))) := by
    funext ω
    rw [hexp]
    simp only [successCount, weightedSum, one_mul, neg_one_mul]
    apply propext
    constructor <;> intro h' <;> nlinarith
  calc
    eventMass (independent (fun _ : Fin N => trialLaw p hp0 hp1))
        (fun ω => successCount ω ≤ lam * (N : ℝ))
        = eventMass (independent (fun _ : Fin N => trialLaw p hp0 hp1))
            (fun ω => (N : ℝ) * (p - lam) ≤ (-1 : ℝ) *
              (weightedSum (fun _ => (1 : ℝ)) (fun _ => successIndicator) ω -
                (independent (fun _ : Fin N => trialLaw p hp0 hp1)).expect
                  (fun ω => weightedSum (fun _ => (1 : ℝ)) (fun _ => successIndicator) ω))) := by
          simp only [hevent]
    _ ≤ Real.exp (-2 * ((N : ℝ) * (p - lam)) ^ 2 /
          ∑ i : Fin N, (1 : ℝ) ^ 2 * ((1 : ℝ) - 0) ^ 2) := h
    _ = Real.exp (-2 * (N : ℝ) * (p - lam) ^ 2) := by
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, sub_zero, one_pow]
      field_simp [hNne]

/-! ### The `m`-round success chain -/

/-- AM--GM monotonicity of the per-round success lower bound:
`(1 − 1/n)^n ≤ (1 − 1/(n+1))^(n+1)`.  This is the sequence used by the paper
when it multiplies the `m` per-round success probabilities. -/
theorem one_sub_inv_pow_monotone {n : ℕ} (hn : 1 ≤ n) :
    (1 - 1 / (n : ℝ)) ^ n ≤ (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hnp1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hp1 : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hnpos]
    exact_mod_cast hn
  have hw1 : 0 ≤ (n : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
  have hw2 : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  have hsum : (n : ℝ) / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) = 1 := by
    field_simp
    push_cast
    ring
  have ham := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 hp1 (by norm_num) hsum
    (p₁ := 1 - 1 / (n : ℝ)) (p₂ := (1 : ℝ))
  have hrhs : (n : ℝ) / ((n + 1 : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) +
      1 / ((n + 1 : ℕ) : ℝ) * 1 = 1 - 1 / ((n + 1 : ℕ) : ℝ) := by
    field_simp
    push_cast
    ring
  have ham0 : (1 - 1 / (n : ℝ)) ^ ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) / ((n + 1 : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) +
        1 / ((n + 1 : ℕ) : ℝ) * 1 := by
    simpa only [Real.one_rpow, mul_one] using ham
  have ham' : (1 - 1 / (n : ℝ)) ^ ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤
      1 - 1 / ((n + 1 : ℕ) : ℝ) :=
    ham0.trans (le_of_eq hrhs)
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hp1 _) ham' (n + 1)
  have hden : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hmul : (n : ℝ) / ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) = (n : ℝ) :=
    div_mul_cancel₀ (n : ℝ) hden
  have hexp : ((1 - 1 / (n : ℝ)) ^ ((n : ℝ) / ((n + 1 : ℕ) : ℝ))) ^ (n + 1) =
      (1 - 1 / (n : ℝ)) ^ n := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp1]
    rw [hmul, Real.rpow_natCast]
  rwa [hexp] at hpow

/-- For `m ≥ 6` the paper's product lower bound is at least `1/3`. -/
theorem one_sub_inv_pow_ge_third {m : ℕ} (hm : 6 ≤ m) :
    (1 / 3 : ℝ) ≤ (1 - 1 / (m : ℝ)) ^ m := by
  have hmono : ∀ k : ℕ, 6 ≤ k → (1 - 1 / (6 : ℝ)) ^ 6 ≤ (1 - 1 / (k : ℝ)) ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
        exact ih.trans (one_sub_inv_pow_monotone (by omega))
  have h6 : (1 / 3 : ℝ) ≤ (1 - 1 / (6 : ℝ)) ^ 6 := by norm_num
  exact h6.trans (hmono m hm)

/-- If each of the `m` independent rounds succeeds with probability at least
`1 − 1/m`, the probability that all rounds succeed is at least `1/3` for `m ≥ 6`.
The `Finset` product is the paper's product of per-round success probabilities. -/
theorem product_success_ge_third (m : ℕ) (hm : 6 ≤ m) (q : ℕ → ℝ)
    (hq : ∀ j, 1 ≤ j → j ≤ m → 1 - 1 / (m : ℝ) ≤ q j) :
    (1 / 3 : ℝ) ≤ ∏ j ∈ Finset.Icc 1 m, q j := by
  have hm1 : 1 ≤ m := by omega
  have hbase : 0 ≤ 1 - 1 / (m : ℝ) := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast (by omega : 0 < m))]
    exact_mod_cast hm1
  have hprod : (1 - 1 / (m : ℝ)) ^ m ≤ ∏ j ∈ Finset.Icc 1 m, q j := by
    have hcard : (Finset.Icc 1 m).card = m := by
      rw [Nat.card_Icc]
      omega
    have hconst : (1 - 1 / (m : ℝ)) ^ m =
        ∏ _x ∈ Finset.Icc 1 m, (1 - 1 / (m : ℝ)) := by
      rw [Finset.prod_const, hcard]
    rw [hconst]
    apply Finset.prod_le_prod₀
    · intro j hj
      exact hbase
    · intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
      exact hq j hj1 hjm
  exact (one_sub_inv_pow_ge_third hm).trans hprod

end Qatlib.Papers.NonlinODE08.FreshIteration
