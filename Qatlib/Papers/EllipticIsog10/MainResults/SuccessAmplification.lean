/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 4.4: repetition amplifies the success probability of Algorithm 1

Paper: Childs, Jao, Soukharev, *Constructing elliptic curve isogenies in quantum
subexponential time*, arXiv:1012.4019v3, Corollary 4.4 (§4.1).

Algorithm 1 runs the for loop over `ℓ = L(1/4z)` candidate vectors.  By
Proposition 4.3 a single iteration produces an `𝓕`-smooth ideal with
probability at least `1/ℓ`, and the iterations are independent.  The success
probability of the whole loop is therefore

`1 - (1 - 1/ℓ)^ℓ > 1 - 1/e`,

which is the content of Corollary 4.4.

This module formalizes the probability estimate.  It proves the general
geometric tail bound `(1 - p)^n ≤ e^{-np}` (valid for `0 ≤ p ≤ 1`), specialises
it to `p = 1/ℓ`, and concludes the `1 - 1/e` lower bound.  The modelling of the
loop as independent trials and the identification `ℓ = L(1/4z)` are not
formalized; see the PR notes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

/-- **Geometric tail bound.** If each of `n` independent trials fails with
probability `1 - p` (with `0 ≤ p ≤ 1`), the probability that all `n` fail,
`(1 - p)^n`, is at most `e^{-n p}`.  This is the standard inequality
`1 - p ≤ e^{-p}` raised to the `n`-th power. -/
theorem all_fail_bound (p : ℝ) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ Real.exp (-(n : ℝ) * p) := by
  have hbase : 0 ≤ 1 - p := by linarith
  have hstep : (1 - p) ^ n ≤ Real.exp (-p) ^ n :=
    pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg p) n
  have hexp : Real.exp (-p) ^ n = Real.exp (-(n : ℝ) * p) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc (1 - p) ^ n ≤ Real.exp (-p) ^ n := hstep
    _ = Real.exp (-(n : ℝ) * p) := hexp

/-- **Corollary 4.4, iteration failure bound.** With `ℓ ≥ 1` candidate vectors,
each of which independently succeeds with probability `1/ℓ`, the probability
that every candidate fails is at most `e^{-1}`. -/
theorem iteration_failure_bound (l : ℕ) (hl : 1 ≤ l) :
    (1 - (1 : ℝ) / (l : ℝ)) ^ l ≤ (Real.exp 1)⁻¹ := by
  have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hinv1 : (1 : ℝ) / (l : ℝ) ≤ 1 := by
    rw [div_le_one₀ hlpos]
    exact_mod_cast hl
  have hbound := all_fail_bound ((1 : ℝ) / (l : ℝ)) hinv1 l
  have hexp : Real.exp (-(l : ℝ) * ((1 : ℝ) / (l : ℝ))) = (Real.exp 1)⁻¹ := by
    have harg : -(l : ℝ) * ((1 : ℝ) / (l : ℝ)) = -1 := by
      field_simp
    rw [harg, Real.exp_neg]
  rw [hexp] at hbound
  exact hbound

/-- **Corollary 4.4.** Under GRH, Algorithm 1's loop of `ℓ = L(1/4z)`
independent iterations, each succeeding with probability at least `1/ℓ`,
succeeds with probability at least `1 - 1/e`. -/
theorem cor4_4_success_lower (l : ℕ) (hl : 1 ≤ l) :
    (1 : ℝ) - (Real.exp 1)⁻¹ ≤ 1 - (1 - (1 : ℝ) / (l : ℝ)) ^ l := by
  have h := iteration_failure_bound l hl
  linarith

end Qatlib.Papers.EllipticIsog10.MainResults
