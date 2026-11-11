/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Schrodinger25 — mollifier derivative bound (Lemma 3.1)

Fixed paper version: arXiv:2505.00370.  Source statement: Lemma 3.1, p. 16,
eq. (3.3).

For the one-dimensional mollifier `η` of (3.2) (a `C_c^∞` bump), the paper
proves

  `|η^{(k)}(p)| ≲ C(k) := 20^k k! e^{−2k} (2k)^{2k}`,  `∀ p ∈ ℝ`.   (3.3)

The proof (p. 16) writes `θ = Cη` in the form

  `θ^{(k)}(p) = Q_k(p) e^{−t} t^{2k}`,  `t = 1/(1−p²) ∈ (1,∞)`,  `|p| < 1`,

where `Q_k` is the polynomial produced by the recursion
`Q_0 = 1`, `Q_{k+1} = (1−p²)² Q_k' + 2p(2k−1−2kp²)Q_k`, and proves the
coefficient bound `|Q_k(p)| ≤ 20^k k!`.  The estimate then follows from the
one-variable extremum fact that `e^{−t} t^{2k}` is maximal at `t = 2k`.

This module proves that extremum fact in full (`exp_neg_mul_pow_le`) and then
derives (3.3) from the paper's two structural facts (the `Q_k`-representation
of `θ^{(k)}` and the coefficient bound), which are stated as hypotheses since
the explicit polynomial recursion is not formalised in the paper layer.

Paper source for the extremum step: p. 16, lines "Since `e^{−t} t^{2k}`
achieves the maximum value at `t = 2k` when `t > 1`, we have
`|θ^{(k)}(p)| ≤ |Q_k(p)| e^{−2k}(2k)^{2k}`."
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Schrodinger25.MainResults.Initialization

/-- Extremum fact used in the proof of Lemma 3.1: for every `t ≥ 0` and every
`k`, `e^{−t} t^{2k} ≤ e^{−2k} (2k)^{2k}` (the function `t ↦ e^{−t} t^{2k}` is
maximal at `t = 2k`).  Proved from `log x ≤ x − 1` applied to
`x = t/(2k)`, i.e. the concavity of the logarithm. -/
theorem exp_neg_mul_pow_le (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) * t ^ (2 * k) ≤ Real.exp (-(2 * (k : ℝ))) * ((2 * (k : ℝ)) ^ (2 * k)) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · -- `t = 0`: both sides reduce, the left side is `0` for `k > 0`
    subst h0
    by_cases hk : k = 0
    · subst hk
      simp
    · have h2k : 2 * k ≠ 0 := by omega
      simp [zero_pow h2k]
      positivity
  · -- `t > 0`
    by_cases hk : k = 0
    · subst hk
      simpa using ht
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have h2k : (0 : ℝ) < 2 * (k : ℝ) := by positivity
      set x : ℝ := t / (2 * (k : ℝ)) with hxdef
      have hx : 0 < x := div_pos hpos h2k
      have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
      have hmul : 2 * (k : ℝ) * Real.log x ≤ 2 * (k : ℝ) * (x - 1) :=
        mul_le_mul_of_nonneg_left hlog h2k.le
      have hxsub : 2 * (k : ℝ) * (x - 1) = t - 2 * (k : ℝ) := by
        rw [hxdef]
        field_simp
      have hpowlog : Real.log (x ^ (2 * k)) ≤ t - 2 * (k : ℝ) := by
        rw [Real.log_pow]
        push_cast
        linarith
      have hxpow : x ^ (2 * k) ≤ Real.exp (t - 2 * (k : ℝ)) := by
        rw [← Real.exp_log (by positivity : 0 < x ^ (2 * k))]
        exact Real.exp_le_exp.mpr hpowlog
      have ht_eq : t = 2 * (k : ℝ) * x := by
        rw [hxdef]
        field_simp
      calc Real.exp (-t) * t ^ (2 * k)
          = ((2 * (k : ℝ)) ^ (2 * k)) * (x ^ (2 * k) * Real.exp (-t)) := by
              rw [ht_eq, mul_pow]
              ring
        _ ≤ ((2 * (k : ℝ)) ^ (2 * k))
              * (Real.exp (t - 2 * (k : ℝ)) * Real.exp (-t)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right hxpow (Real.exp_pos _).le
        _ = Real.exp (-(2 * (k : ℝ))) * ((2 * (k : ℝ)) ^ (2 * k)) := by
              rw [← Real.exp_add]
              have hsum : t - 2 * (k : ℝ) + -t = -(2 * (k : ℝ)) := by ring
              rw [hsum]
              ring

/-- **Lemma 3.1** (p. 16, (3.3)), reduced form.

Let `θ = Cη` be the renormalised mollifier and suppose `θ` has the paper's
representation `|θ^{(k)}(p)| ≤ Q_k(p) e^{−t} t^{2k}` with `t = 1/(1−p²)` on
`|p| < 1`, with the coefficient bound `|Q_k(p)| ≤ 20^k k!` from the recursion
for `Q_k` (p. 16).  Then the derivative bound (3.3) holds:

  `|θ^{(k)}(p)| ≤ 20^k k! e^{−2k} (2k)^{2k}`.

The paper's `≲` is realised here by the constant of the `Q_k` bound: the
paper's proof produces `|Q_k(p)| ≤ 20^k k!` "up to a universal multiplicative
constant", which is absorbed in the paper's `≲`. -/
theorem lemma_three_one_mollifier_derivative_bound
    (θ : ℝ → ℝ) (Q : ℕ → ℝ → ℝ) (k : ℕ)
    (hform : ∀ p : ℝ, |p| < 1 →
      |iteratedDeriv k θ p| ≤ Q k p * Real.exp (-(1 / (1 - p ^ 2))) * (1 / (1 - p ^ 2)) ^ (2 * k))
    (hQbound : ∀ p : ℝ, |p| < 1 → Q k p ≤ (20 : ℝ) ^ k * (k.factorial : ℝ))
    (p : ℝ) (hp : |p| < 1) :
    |iteratedDeriv k θ p|
      ≤ (20 : ℝ) ^ k * (k.factorial : ℝ) * Real.exp (-(2 * (k : ℝ))) * ((2 * (k : ℝ)) ^ (2 * k)) := by
  obtain ⟨hp1, hp2⟩ := abs_lt.mp hp
  have hsq : p ^ 2 < 1 := by
    have h1 : 0 < 1 - p := by linarith
    have h2 : 0 < 1 + p := by linarith
    nlinarith [mul_pos h1 h2]
  have hdec : 0 < 1 - p ^ 2 := by linarith
  set t : ℝ := 1 / (1 - p ^ 2) with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  have h1 := exp_neg_mul_pow_le k t ht.le
  have hform' : |iteratedDeriv k θ p|
      ≤ Q k p * (Real.exp (-t) * t ^ (2 * k)) := by
    have := hform p hp
    simpa [← htdef, mul_assoc] using this
  have hQ : Q k p ≤ (20 : ℝ) ^ k * (k.factorial : ℝ) := hQbound p hp
  have hexp_nonneg : 0 ≤ Real.exp (-t) * t ^ (2 * k) :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le _)
  have hstep : Q k p * (Real.exp (-t) * t ^ (2 * k))
      ≤ ((20 : ℝ) ^ k * (k.factorial : ℝ)) * (Real.exp (-t) * t ^ (2 * k)) :=
    mul_le_mul_of_nonneg_right hQ hexp_nonneg
  have hstep2 : ((20 : ℝ) ^ k * (k.factorial : ℝ)) * (Real.exp (-t) * t ^ (2 * k))
      ≤ ((20 : ℝ) ^ k * (k.factorial : ℝ))
          * (Real.exp (-(2 * (k : ℝ))) * ((2 * (k : ℝ)) ^ (2 * k))) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hfinal : ((20 : ℝ) ^ k * (k.factorial : ℝ))
        * (Real.exp (-(2 * (k : ℝ))) * ((2 * (k : ℝ)) ^ (2 * k)))
      = (20 : ℝ) ^ k * (k.factorial : ℝ) * Real.exp (-(2 * (k : ℝ)))
        * ((2 * (k : ℝ)) ^ (2 * k)) := by ring
  linarith

end Qatlib.Papers.Schrodinger25.MainResults.Initialization
