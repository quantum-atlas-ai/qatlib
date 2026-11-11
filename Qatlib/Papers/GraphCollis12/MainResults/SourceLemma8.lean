/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphCollis12.MainResults.SourceBasicLemmas

set_option backward.isDefEq.respectTransparency false

/-!
# GraphCollis12 — Lemma 8 (concentration of `α*(G)` on random graphs)

Fixed source: arXiv:1204.1527v1, §5, Lemma 8 (pp.6-7):

> Lemma 8. For arbitrary `p ∈ (0,1]` and `t ≥ 40 n log n`,
>   `Pr_{G∼μ_{n,p}}[α*(G) ≥ t] ≤ n^{-14n} + 2 exp(-t² / (200 n² p))`.

The proof (p.7) bounds the expected number `Y_t` of independent sets `S` with
`deg(S) ≥ t` by a union bound, splits the sum at `x₀ = min(⌊t/(5np)⌋, n)`, and
applies the Drukh–Mansour Chernoff bound (paper Lemma 3) to bound
`Pr[deg(S) ≥ t : |S| = i]` for large `|S|`.  The union bound then gives
`Pr[α*(G) ≥ t] ≤ E[Y_t] ≤ exp(-7t/20) + 2 exp(-t²/(200 n² p))`, and
`exp(-7t/20) ≤ n^{-14n}` for `t ≥ 40 n log n`.

This file fixes the exact statement and the (fully proved) measure-theoretic
infrastructure: the model weights are nonnegative on `(0,1]`, and `μ_{n,p}` is
monotone in the event.  The Chernoff/union-bound core is recorded as a
`Prop`-valued definition; its proof is a substantive gap.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.GraphCollis12.MainResults

/-- Model weights are nonnegative for `p ∈ (0,1]`. -/
theorem muWeight_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (G : SimpleGraph (Fin n)) : 0 ≤ muWeight p G := by
  unfold muWeight
  have hp : 0 ≤ p := le_of_lt hp0
  have hq : 0 ≤ 1 - p := by linarith
  exact mul_nonneg (pow_nonneg hp _) (pow_nonneg hq _)

/-- `μ_{n,p}` is monotone in the event, for `p ∈ (0,1]`. -/
theorem muPr_mono {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {E E' : SimpleGraph (Fin n) → Prop} (h : ∀ G, E G → E' G) :
    muPr p E ≤ muPr p E' := by
  unfold muPr
  refine Finset.sum_le_sum ?_
  intro G _
  by_cases hE : E G
  · have hE' : E' G := h G hE
    simp [hE, hE']
  · by_cases hE' : E' G
    · simp [hE, hE', muWeight_nonneg hp0 hp1 G]
    · simp [hE, hE']

/-- Each event probability is nonnegative. -/
theorem muPr_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (E : SimpleGraph (Fin n) → Prop) : 0 ≤ muPr p E := by
  unfold muPr
  refine Finset.sum_nonneg ?_
  intro G _
  by_cases hE : E G
  · simp [hE, muWeight_nonneg hp0 hp1 G]
  · simp [hE]

/-- **Lemma 8** (arXiv:1204.1527v1, §5, pp.6-7).  For `p ∈ (0,1]`, `n ≥ 1`, and
`t ≥ 40 n log n`, the `μ_{n,p}`-probability that `α*(G) ≥ t` is at most
`n^{-14n} + 2 exp(-t²/(200 n² p))`.

Proof route (paper p.7):
1. `Pr[α* ≥ t] ≤ E[Y_t]` where `Y_t = #{independent S : deg(S) ≥ t}`;
2. `E[Y_t] ≤ Σ_{i=1}^{x₀} exp(i log n + 3 n i p - t) + Σ_{i=x₀+1}^{n} exp(i log n - p i²/4)`,
   with `x₀ = min(⌊t/(5np)⌋, n)`, using Chernoff (paper Lemma 3) for the
   `Pr[deg(S) ≥ t : |S| = i]` factor;
3. split bound: `≤ exp(-7t/20) + 2 exp(-p x₀²/8) ≤ exp(-7t/20) + 2 exp(-t²/(200 n² p))`;
4. `exp(-7t/20) ≤ n^{-14n}` since `t ≥ 40 n log n` gives `7t/20 ≥ 14 n log n`.

**Status: statement registered as a `Prop`-valued definition; the proof is a
substantive gap** (the paper's union bound, size split, Chernoff step and
binomial estimates are not yet mechanised). -/
def lemma8 (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (t : ℝ) (ht : 40 * (n : ℝ) * Real.log (n : ℝ) ≤ t) : Prop :=
  muPr p (fun (G : SimpleGraph (Fin n)) => t ≤ (alphaStar G : ℝ)) ≤
    (n : ℝ) ^ (-(14 * (n : ℝ))) + 2 * Real.exp (-(t ^ 2) / (200 * (n : ℝ) ^ 2 * p))

end Qatlib.Papers.GraphCollis12.MainResults
