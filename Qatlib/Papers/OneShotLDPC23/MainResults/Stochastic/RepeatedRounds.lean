/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneShotLDPC23.MainResults.Model.BinaryWeight

set_option backward.isDefEq.respectTransparency false

/-!
# OneShotLDPC23.MainResults.Stochastic.RepeatedRounds — Theorems 3.5 and 3.6

Fixed paper: **arXiv:2306.12470v2**, §3.3, pp. 10–11.

* `theorem_3_5` is the deterministic multi-round statement: if the data and
  syndrome error weights in every round are bounded by `R n` and `S n` with
  `R, S` satisfying (1), then the residual reduced weight after every round is
  at most `(αR + βS)/(1−α) · n`.  Proof: the induction of p. 10, with the
  budget implication of (1) supplied by the lemma
  `Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy.repeatedNoise_source_budget`
  and the round induction by
  `Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy.repeatedNoise_stable`.
* `theorem_3_5_finite` is the same induction restricted to rounds `0 … M−1`;
  it is what the stochastic corollary needs, and it is proved directly here.
* `corollary_3_6` adds the union bound over rounds, reusing the lemma
  `Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy.correlated_round_failure_bound`
  (no independence between rounds is assumed, exactly as in the paper).

Boundary: the probability space is an arbitrary finite `Ω` with a nonnegative
mass function (`p`); the paper's `Pr` is this finite mass.  The decoder is
deterministic, encoded by the per-round step hypothesis `hstep`.
-/

set_option autoImplicit false

open Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy

namespace Qatlib.Papers.OneShotLDPC23.MainResults.Stochastic

open scoped BigOperators

/-- The fixed point of the one-round recursion of Theorem 3.5:
`L = (αR + βS)/(1−α)`. -/
noncomputable def roundBound (α β R S : ℝ) : ℝ := (α * R + β * S) / (1 - α)

/-- **Source Theorem 3.5** (arXiv:2306.12470v2, §3.3 p. 10, eq. (2)).
Consider errors `(eᵢ, Dᵢ)` on rounds `i = 1, 2, …` decoded with fresh syndrome
measurements.  If `|eᵢ| ≤ R n` and `|Dᵢ| ≤ S n` for every round, with `R, S`
satisfying (1), then the residual reduced weight after round `i` satisfies
`|e′ᵢ|_R ≤ (αR + βS)/(1−α) · n`.

Reuses: `repeatedNoise_source_budget` (turns (1) into the round budget) and
`repeatedNoise_stable` (the deterministic induction). -/
theorem theorem_3_5 (α β R S A B C n : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ : 0 ≤ β)
    (hA : 0 < A) (hB : 0 < B)
    (hR0 : 0 ≤ R) (hS0 : 0 ≤ S) (hn : 0 ≤ n)
    (hReq : R ≤ (1 - α) * C / (2 * A))
    (hSeq : S ≤ (1 - α) * C / (2 * (β * A + (1 - α) * B)))
    (residual data syndrome : ℕ → ℝ)
    (hzero : residual 0 = 0)
    (hdata : ∀ i, data i ≤ R * n)
    (hsyndrome : ∀ i, syndrome i ≤ S * n)
    (hstep : ∀ i, A * (residual i + data i) + B * syndrome i ≤ C * n →
      residual (i + 1) ≤ α * (residual i + data i) + β * syndrome i) :
    ∀ i, residual i ≤ roundBound α β R S * n := by
  have hbudget : A * (roundBound α β R S + R) + B * S ≤ C := by
    simpa [roundBound] using
      repeatedNoise_source_budget α β A B C R S hα1 hβ hA hB hReq hSeq
  have hstable : ∀ i, residual i ≤ roundBound α β R S * n := by
    simpa [roundBound] using
      repeatedNoise_stable α β R S A B C n hα0 hα1 hβ hR0 hS0 (le_of_lt hA) (le_of_lt hB)
        hn hbudget residual data syndrome hzero hdata hsyndrome hstep
  exact hstable

/-- Finite-round form of Theorem 3.5: the induction only consumes rounds
`0, …, M−1`, so it applies conditionally to a finite error history. -/
theorem theorem_3_5_finite (α β R S A B C n : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ : 0 ≤ β)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR0 : 0 ≤ R) (hS0 : 0 ≤ S) (hn : 0 ≤ n)
    (hbudget : A * (roundBound α β R S + R) + B * S ≤ C)
    (residual data syndrome : ℕ → ℝ)
    (hzero : residual 0 = 0)
    (M : ℕ)
    (hdata : ∀ i, i < M → data i ≤ R * n)
    (hsyndrome : ∀ i, i < M → syndrome i ≤ S * n)
    (hstep : ∀ i, A * (residual i + data i) + B * syndrome i ≤ C * n →
      residual (i + 1) ≤ α * (residual i + data i) + β * syndrome i) :
    residual M ≤ roundBound α β R S * n := by
  have hden : 0 < 1 - α := by linarith
  have hL0 : 0 ≤ roundBound α β R S := by
    unfold roundBound
    exact div_nonneg (add_nonneg (mul_nonneg hα0 hR0) (mul_nonneg hβ hS0)) hden.le
  -- the recursion's budget holds at every step of the good history
  have hstepM : ∀ i ≤ M, residual i ≤ roundBound α β R S * n := by
    intro i
    induction i with
    | zero => intro _; rw [hzero]; exact mul_nonneg hL0 hn
    | succ k ih =>
      intro hk
      have hbud : A * (residual k + data k) + B * syndrome k ≤ C * n := by
        have h1 : residual k ≤ roundBound α β R S * n := ih (Nat.le_of_lt hk)
        have h2 : data k ≤ R * n := hdata k hk
        have h3 : syndrome k ≤ S * n := hsyndrome k hk
        calc A * (residual k + data k) + B * syndrome k
            ≤ A * (roundBound α β R S * n + R * n) + B * (S * n) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) hA
              · exact mul_le_mul_of_nonneg_left h3 hB
          _ = (A * (roundBound α β R S + R) + B * S) * n := by ring
          _ ≤ C * n := mul_le_mul_of_nonneg_right hbudget hn
      calc residual (k + 1) ≤ α * (residual k + data k) + β * syndrome k := hstep k hbud
        _ ≤ α * (roundBound α β R S * n + R * n) + β * (S * n) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (add_le_add (ih (Nat.le_of_lt hk)) (hdata k hk)) hα0
              · exact mul_le_mul_of_nonneg_left (hsyndrome k hk) hβ
        _ = roundBound α β R S * n := by
              unfold roundBound
              field_simp
              ring
  exact hstepM M le_rfl

/-- For a nonnegative finite mass, the mass of a union of two events is at
most the sum of the two masses. -/
theorem sum_filter_or_le {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (A B : Ω → Prop) [DecidablePred A] [DecidablePred B] :
    (Finset.univ.filter fun ω => A ω ∨ B ω).sum p ≤
      (Finset.univ.filter A).sum p + (Finset.univ.filter B).sum p := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro ω _
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB, hp ω]

/-- **Source Corollary 3.6** (arXiv:2306.12470v2, §3.3 p. 10).
Let `{(eᵢ, Dᵢ)}_{i=1}^{M}` be randomly distributed data and syndrome errors,
possibly correlated, with `Pr(|eᵢ| > R n) ≤ e^{−an}` and
`Pr(|Dᵢ| > S n) ≤ e^{−bn}`.  Then the final residual error satisfies
`Pr(|e′_M|_R > (αR+βS)/(1−α) · n) ≤ M (e^{−an} + e^{−bn})`.

Reuses: `correlated_round_failure_bound` for the union bound over rounds and
`theorem_3_5_finite` for the conditional deterministic residual bound. -/
theorem corollary_3_6 {Ω : Type*} [Fintype Ω]
    (α β R S A B C n a b : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ : 0 ≤ β)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR0 : 0 ≤ R) (hS0 : 0 ≤ S) (hn : 0 ≤ n)
    (hbudget : A * (roundBound α β R S + R) + B * S ≤ C)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (M : ℕ)
    (residual data syndrome : ℕ → Ω → ℝ)
    (hzero : ∀ ω, residual 0 ω = 0)
    (hstep : ∀ ω i, A * (residual i ω + data i ω) + B * syndrome i ω ≤ C * n →
      residual (i + 1) ω ≤ α * (residual i ω + data i ω) + β * syndrome i ω)
    (hdata_tail : ∀ i : ℕ,
      (Finset.univ.filter fun ω => R * n < data i ω).sum p ≤ Real.exp (-(a * n)))
    (hsyndrome_tail : ∀ i : ℕ,
      (Finset.univ.filter fun ω => S * n < syndrome i ω).sum p ≤ Real.exp (-(b * n))) :
    (Finset.univ.filter fun ω => roundBound α β R S * n < residual M ω).sum p ≤
      M * (Real.exp (-(a * n)) + Real.exp (-(b * n))) := by
  classical
  -- one bad round: a too-large data or syndrome error
  let bad : Fin M → Ω → Prop :=
    fun i ω => R * n < data (i : ℕ) ω ∨ S * n < syndrome (i : ℕ) ω
  have hbad_mass : ∀ i : Fin M,
      (Finset.univ.filter (bad i)).sum p ≤
        Real.exp (-(a * n)) + Real.exp (-(b * n)) := by
    intro i
    have h1 := hdata_tail (i : ℕ)
    have h2 := hsyndrome_tail (i : ℕ)
    calc (Finset.univ.filter (bad i)).sum p
        ≤ (Finset.univ.filter fun ω => R * n < data (i : ℕ) ω).sum p +
          (Finset.univ.filter fun ω => S * n < syndrome (i : ℕ) ω).sum p :=
          sum_filter_or_le p hp _ _
      _ ≤ Real.exp (-(a * n)) + Real.exp (-(b * n)) := add_le_add h1 h2
  have hunion := correlated_round_failure_bound M p hp bad
    (fun _ => Real.exp (-(a * n)) + Real.exp (-(b * n))) hbad_mass
  -- the bad event contains every history with a too-large final residual
  have hsubset : (Finset.univ.filter fun ω => roundBound α β R S * n < residual M ω) ⊆
      (Finset.univ.filter fun ω => ∃ i : Fin M, bad i ω) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    by_contra hcon
    push Not at hcon
    have hdata' : ∀ i, i < M → data i ω ≤ R * n := by
      intro i hi
      have h' := hcon ⟨i, hi⟩
      simp only [bad, not_or, not_lt] at h'
      exact h'.1
    have hsyn' : ∀ i, i < M → syndrome i ω ≤ S * n := by
      intro i hi
      have h' := hcon ⟨i, hi⟩
      simp only [bad, not_or, not_lt] at h'
      exact h'.2
    have := theorem_3_5_finite α β R S A B C n hα0 hα1 hβ hA hB hR0 hS0 hn hbudget
      (fun i => residual i ω) (fun i => data i ω) (fun i => syndrome i ω) (hzero ω) M
      hdata' hsyn' (hstep ω)
    linarith
  calc (Finset.univ.filter fun ω => roundBound α β R S * n < residual M ω).sum p
      ≤ (Finset.univ.filter fun ω => ∃ i : Fin M, bad i ω).sum p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun ω _ _ => hp ω)
    _ ≤ ∑ i : Fin M, (Real.exp (-(a * n)) + Real.exp (-(b * n))) := hunion
    _ = M * (Real.exp (-(a * n)) + Real.exp (-(b * n))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Qatlib.Papers.OneShotLDPC23.MainResults.Stochastic
