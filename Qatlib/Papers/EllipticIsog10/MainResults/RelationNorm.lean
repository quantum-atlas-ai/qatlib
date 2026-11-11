/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 4.5: the relation vector has small `ℓ¹` norm

Paper: Childs, Jao, Soukharev, *Constructing elliptic curve isogenies in quantum
subexponential time*, arXiv:1012.4019v3, Proposition 4.5 (§4.1).

Algorithm 1 returns a relation vector `z = a - v`, where `v` is the sampled
exponent vector and `a` is the exponent vector of the reduced ideal `a_v` over
the factor base.  Proposition 4.5 proves

`|z|₁ < (C + 1) ln|Δ|`

from the two input bounds

* `|v|₁ ≤ C ln|Δ|` (the constraint imposed in Algorithm 1), and
* `|a|₁ < log₂ √(|Δ|/3) < ln|Δ|` (the reduced ideal's norm, [8, Prop. 9.1.7]).

This module formalizes the arithmetic: the `ℓ¹` triangle inequality for the
difference of two integer vectors, the base-change estimate
`log₂ √x < ln x` for `x > 1`, and the resulting `(C + 1) ln|Δ|` bound.  The
factorisation model that yields `|a|₁ < log₂ √(|Δ|/3)` is kept as an explicit
hypothesis; see the PR notes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

open scoped BigOperators

noncomputable section

/-- The `ℓ¹` norm of an integer vector `z : ι → ℤ`, as the sum of the absolute
values of its coordinates. -/
def l1 {ι : Type*} [Fintype ι] (z : ι → ℤ) : ℝ := ∑ i, |(z i : ℝ)|

/-- **Proposition 4.5, triangle step.**  For integer vectors `a`, `v`, the `ℓ¹`
norm of `z = a - v` is at most `|a|₁ + |v|₁`, because each coordinate obeys
`|a_i - v_i| ≤ |a_i| + |v_i|`. -/
theorem l1_sub_le {ι : Type*} [Fintype ι] (a v : ι → ℤ) :
    l1 (a - v) ≤ l1 a + l1 v := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hco : (((a - v) i : ℤ) : ℝ) = (a i : ℝ) - (v i : ℝ) := by
    simp [Pi.sub_apply]
  rw [hco]
  calc |(a i : ℝ) - (v i : ℝ)|
      = |(a i : ℝ) + -(v i : ℝ)| := by ring_nf
    _ ≤ |(a i : ℝ)| + |-(v i : ℝ)| := abs_add_le _ _
    _ = |(a i : ℝ)| + |(v i : ℝ)| := by rw [abs_neg]

/-- **Base-change estimate.**  For `x > 1`, the base-`2` logarithm of `√x` is
strictly below the natural logarithm of `x`, since
`log₂ √x = ln x / (2 ln 2)` and `1/(2 ln 2) < 1` (because `2 ln 2 = ln 4 > 1`).
This is the source's step `log₂ √(|Δ|/3) < ln|Δ|`. -/
theorem logb_two_sqrt_lt_log (x : ℝ) (hx : 1 < x) :
    Real.logb 2 (Real.sqrt x) < Real.log x := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  -- `2 * ln 2 = ln 4 > 1`, hence `1 / (2 ln 2) < 1`.
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have he : Real.exp 1 < 4 := by
      have h9 := Real.exp_one_lt_d9
      linarith
    have h := Real.log_lt_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hcoef : (1 : ℝ) / (2 * Real.log 2) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  unfold Real.logb
  rw [Real.log_sqrt hx0.le]
  have hrewrite : Real.log x / 2 / Real.log 2 = Real.log x * (1 / (2 * Real.log 2)) := by
    field_simp
  rw [hrewrite]
  calc Real.log x * (1 / (2 * Real.log 2)) < Real.log x * 1 :=
        mul_lt_mul_of_pos_left hcoef hlogx
    _ = Real.log x := by ring

/-- **Proposition 4.5.**  Suppose `z = a - v` with `|v|₁ ≤ C ln|Δ|` and
`|a|₁ ≤ log₂ √(|Δ|/3)`, where `x = |Δ| > 3`.  Then
`|z|₁ < (C + 1) ln|Δ|`. -/
theorem prop4_5_relation_bound {ι : Type*} [Fintype ι] (a v : ι → ℤ)
    (C : ℝ) {x : ℝ} (hx : 3 < x)
    (hv : l1 v ≤ C * Real.log x)
    (ha : l1 a ≤ Real.logb 2 (Real.sqrt (x / 3))) :
    l1 (a - v) < (C + 1) * Real.log x := by
  have hx1 : 1 < x / 3 := by linarith
  have hx0 : 0 < x := by linarith
  have hchain : Real.logb 2 (Real.sqrt (x / 3)) < Real.log x := by
    have h1 := logb_two_sqrt_lt_log (x / 3) hx1
    have h2 : Real.log (x / 3) < Real.log x :=
      Real.log_lt_log (by linarith) (by linarith)
    exact lt_trans h1 h2
  have ha' : l1 a < Real.log x := lt_of_le_of_lt ha hchain
  calc l1 (a - v) ≤ l1 a + l1 v := l1_sub_le a v
    _ < Real.log x + C * Real.log x := by linarith
    _ = (C + 1) * Real.log x := by ring

end

end Qatlib.Papers.EllipticIsog10.MainResults
