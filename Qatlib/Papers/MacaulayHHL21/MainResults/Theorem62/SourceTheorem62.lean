/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 6.2 — coupon-collector sampling from the solution superposition

Fixed paper: arXiv:2111.00405, Theorem 6.2 on p.16.

Statement (verbatim): *Let `r = O((|S|/d) log(|S|/ε))`. Measuring `r` copies of the quantum
superposition state in Problem 6.1, the set `S` can be computed with probability at least
`1 − ε`.*

The paper's proof is the coupon-collector argument: for `0 ≤ d ≤ |S|`, the probability that a
fixed `x ∈ S` is seen in one measurement is at least `d/(2|S|)`; after `r` independent
measurements the probability of never seeing `x` is at most `(1 − d/(2|S|))^r ≤
exp(−dr/(2|S|))`, and the union bound over the `|S|` elements gives failure probability at
most `|S|·exp(−dr/(2|S|)) ≤ ε` for `r ≥ (2|S|/d) log(|S|/ε)`.

We model the per-sample success probability as an abstract `p` with `d/(2|S|) ≤ p ≤ 1`;
everything after that point (the exponential bound, the union bound, and the choice of `r`)
is proved below.  A full stochastic model of the measurement distribution is not built.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Theorem62

open Qatlib.Papers.MacaulayHHL21.MainResults

/-- **Theorem 6.2** (arXiv:2111.00405, p.16), union-bound form: if a single measurement sees
a fixed element with probability `p ≥ d/(2|S|)`, then after `r ≥ (2|S|/d)·log(|S|/ε)`
measurements the union-bound failure probability `|S|·(1−p)^r` is at most `ε`. -/
theorem theorem62_unionBound
    {N d r : ℕ} {ε p : ℝ}
    (hN : 0 < N) (hd : d ≤ N)
    (hp_ge : (d : ℝ) / (2 * (N : ℝ)) ≤ p) (hp_le : p ≤ 1)
    (hε : 0 < ε)
    (hr : (N : ℝ) * Real.log ((N : ℝ) / ε) ≤ (d : ℝ) * (r : ℝ) / 2) :
    (N : ℝ) * (1 - p) ^ r ≤ ε := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx0 : (0 : ℝ) ≤ (d : ℝ) / (2 * (N : ℝ)) := by positivity
  have hp0 : (0 : ℝ) ≤ 1 - p := by linarith
  -- `1 - p ≤ exp(-d/(2N))`
  have h1 : (1 - p) ≤ Real.exp (-((d : ℝ) / (2 * (N : ℝ)))) := by
    have hexp := Real.add_one_le_exp (-((d : ℝ) / (2 * (N : ℝ))))
    linarith
  -- raise to the `r`-th power
  have h2 : (1 - p) ^ r ≤ Real.exp (-((d : ℝ) / (2 * (N : ℝ)))) ^ r :=
    pow_le_pow_left₀ hp0 h1 r
  have h3 : Real.exp (-((d : ℝ) / (2 * (N : ℝ)))) ^ r =
      Real.exp (-((d : ℝ) * (r : ℝ) / (2 * (N : ℝ)))) := by
    rw [← Real.exp_nat_mul (-((d : ℝ) / (2 * (N : ℝ)))) r]
    congr 1
    push_cast
    field_simp
  -- the hypothesis on `r` controls the exponent
  have hlog : Real.log ((N : ℝ) / ε) ≤ (d : ℝ) * (r : ℝ) / (2 * (N : ℝ)) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
    nlinarith [hr]
  have h5 : Real.exp (-((d : ℝ) * (r : ℝ) / (2 * (N : ℝ)))) ≤
      Real.exp (-Real.log ((N : ℝ) / ε)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h6 : Real.exp (-Real.log ((N : ℝ) / ε)) = ε / (N : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  calc (N : ℝ) * (1 - p) ^ r
      ≤ (N : ℝ) * Real.exp (-((d : ℝ) / (2 * (N : ℝ)))) ^ r :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (N : ℝ) * Real.exp (-((d : ℝ) * (r : ℝ) / (2 * (N : ℝ)))) := by rw [h3]
    _ ≤ (N : ℝ) * Real.exp (-Real.log ((N : ℝ) / ε)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = ε := by
        rw [h6]
        field_simp

/-- **Theorem 6.2** (arXiv:2111.00405, p.16), success form: with `r ≥ (2|S|/d)·log(|S|/ε)`
measurements, `|S|` elements are all collected with probability at least `1 − ε`
(complement of the union bound). -/
theorem theorem62_successProbability
    {N d r : ℕ} {ε p : ℝ}
    (hN : 0 < N) (hd : d ≤ N)
    (hp_ge : (d : ℝ) / (2 * (N : ℝ)) ≤ p) (hp_le : p ≤ 1)
    (hε : 0 < ε)
    (hr : (N : ℝ) * Real.log ((N : ℝ) / ε) ≤ (d : ℝ) * (r : ℝ) / 2) :
    1 - ε ≤ 1 - (N : ℝ) * (1 - p) ^ r := by
  have h := theorem62_unionBound hN hd hp_ge hp_le hε hr
  linarith

end Qatlib.Papers.MacaulayHHL21.MainResults.Theorem62
