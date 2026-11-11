/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# GateCost — c005 of SteadyState20

Fixed source: arXiv:2008.07133v2 (Quantum **5**, 420 (2021)), Section 3.1, p. 7,
Eq. (13):

`N_g = O(t + t log t + 2N + (2N+1)^k / (g^{1+1/p} ε_τ^{1/p} ε_p^{1/2}))`,

where `g` is the Liouvillian gap, `k` the locality order of the block operator `M`,
`p` the Suzuki–Trotter order, and `ε_τ`, `ε_p` the Trotter and QPE success errors.
The paper then observes that, when `1/g` grows only as a power law in the system size,
the total gate count grows polynomially in `N`.

Formalisation:

* `gateCost` is the paper's right-hand side, written with real powers
  `g^{1+1/p}`, `ε_τ^{1/p}`, `ε_p^{1/2}` (`p` is a natural number; the powers are
  `Real.rpow`).
* `gateCost_nonneg` records positivity of the expression under the physical
  hypotheses `0 < g`, `0 < ε_τ`, `0 < ε_p`.
* `gateCost_le_polynomial` is the polynomial-growth statement: if the whole
  inverse denominator `g^{-(1+1/p)} ε_τ^{-1/p} ε_p^{-1/2}` is bounded by a polynomial
  `C (N+1)^s` — which is exactly what a power-law gap and bounded errors supply — then
  `N_g ≤ (t + t log t + 2N) + C (N+1)^s (2N+1)^k`, a polynomial bound in `N`.

The paper states Eq. (13) with `O(·)` notation; the formal statements below avoid
asymptotic notation and give the underlying exact expression and an explicit
polynomial bound, which is the quantitative content used downstream (claim c001).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SteadyState20.MainResults.GateCost

/-- Paper Eq. (13) (arXiv:2008.07133v2, Sec. 3.1, p. 7): the total gate count of the
NESS solver, including the QPE register cost `t + t log t`, the state-preparation cost
`2N`, and the Hamiltonian-simulation (Suzuki–Trotter) cost
`(2N+1)^k / (g^{1+1/p} ε_τ^{1/p} ε_p^{1/2})`. -/
def gateCost (N t k p : ℕ) (g ετ εp : ℝ) : ℝ :=
  (t : ℝ) + (t : ℝ) * Real.log (t : ℝ) + 2 * (N : ℝ) +
    ((2 * (N : ℝ) + 1) ^ k) /
      (g ^ (1 + 1 / (p : ℝ)) * ετ ^ (1 / (p : ℝ)) * εp ^ ((1 : ℝ) / 2))

/-- Paper Eq. (13), p. 7: every summand of the gate count is nonnegative under the
physical hypotheses `0 < g`, `0 < ε_τ`, `0 < ε_p`; in particular `N_g ≥ 0`. -/
theorem gateCost_nonneg (N t k p : ℕ) {g ετ εp : ℝ}
    (hg : 0 < g) (hετ : 0 < ετ) (hεp : 0 < εp) :
    0 ≤ gateCost N t k p g ετ εp := by
  unfold gateCost
  have hden : (0 : ℝ) <
      g ^ (1 + 1 / (p : ℝ)) * ετ ^ (1 / (p : ℝ)) * εp ^ ((1 : ℝ) / 2) := by
    have h1 : (0 : ℝ) < g ^ (1 + 1 / (p : ℝ)) := Real.rpow_pos_of_pos hg _
    have h2 : (0 : ℝ) < ετ ^ (1 / (p : ℝ)) := Real.rpow_pos_of_pos hετ _
    have h3 : (0 : ℝ) < εp ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hεp _
    exact mul_pos (mul_pos h1 h2) h3
  have hlog : (0 : ℝ) ≤ (t : ℝ) * Real.log (t : ℝ) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      have : (0 : ℝ) ≤ Real.log (t : ℝ) := Real.log_nonneg ht1
      positivity
  have hterm : (0 : ℝ) ≤
      ((2 * (N : ℝ) + 1) ^ k) /
        (g ^ (1 + 1 / (p : ℝ)) * ετ ^ (1 / (p : ℝ)) * εp ^ ((1 : ℝ) / 2)) :=
    div_nonneg (by positivity) (le_of_lt hden)
  have : (0 : ℝ) ≤ 2 * (N : ℝ) := by positivity
  linarith

/-- Paper Eq. (13) and the polynomial-growth discussion (Sec. 3.1, p. 7): if the
inverse simulation denominator is bounded by a polynomial `C (N+1)^s` (the situation
produced by a power-law Liouvillian gap together with bounded Trotter and QPE errors),
then the gate count obeys the explicit polynomial bound
`N_g ≤ t + t log t + 2N + C (N+1)^s (2N+1)^k`. -/
theorem gateCost_le_polynomial (N t k p : ℕ) {g ετ εp C : ℝ} {s : ℕ}
    (hg : 0 < g) (hετ : 0 < ετ) (hεp : 0 < εp) (hC : 0 ≤ C)
    (hden : 1 /
        (g ^ (1 + 1 / (p : ℝ)) * ετ ^ (1 / (p : ℝ)) * εp ^ ((1 : ℝ) / 2))
        ≤ C * ((N : ℝ) + 1) ^ s) :
    gateCost N t k p g ετ εp ≤
      (t : ℝ) + (t : ℝ) * Real.log (t : ℝ) + 2 * (N : ℝ) +
        ((2 * (N : ℝ) + 1) ^ k) * (C * ((N : ℝ) + 1) ^ s) := by
  unfold gateCost
  have hdiv : ((2 * (N : ℝ) + 1) ^ k) /
        (g ^ (1 + 1 / (p : ℝ)) * ετ ^ (1 / (p : ℝ)) * εp ^ ((1 : ℝ) / 2))
      = ((2 * (N : ℝ) + 1) ^ k) *
        (1 / (g ^ (1 + 1 / (p : ℝ)) * ετ ^ (1 / (p : ℝ)) * εp ^ ((1 : ℝ) / 2))) := by
    ring
  rw [hdiv]
  have hpow : (0 : ℝ) ≤ (2 * (N : ℝ) + 1) ^ k := by positivity
  have hmul := mul_le_mul_of_nonneg_left hden hpow
  linarith

end Qatlib.Papers.SteadyState20.MainResults.GateCost
