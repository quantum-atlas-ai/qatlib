/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults — exponent arithmetic behind the paper's stated bounds

Le Gall and Nishimura, fixed arXiv:1310.3898v1.
PDF SHA-256 1d042e95c69668deb534b7bc64dacdbeab9ccd52d8c325d88efc1728fd339971.

Section 2 fixes the literature hypothesis `ω < 2.373` and introduces
`α = sup{k | ω(1,k,1) = 2}` together with `β = (ω-2)/(1-α)`.  The proofs of
Theorem 4.2 and Theorem 4.3 rewrite their exponents using `β * (1-α) = ω - 2`, and
Section 1 quotes the decimal upper bounds `2.458` and `2.687`.

This module checks those arithmetic steps, taking the paper's quoted literature
hypotheses as explicit hypotheses rather than deriving them:
* `(5+ω)/3 ≤ 2.458` — Theorem 4.2's "`≤ O(2^{0.640ℓ} n^{2.458})`";
* `(3+ω)/2 ≤ 2.687` — the Duan–Pettie bound quoted in Section 1 and Theorem 4.3;
* `5/2 + (2β-2αβ-1)/6 = (5+ω)/3` — the step turning Theorem 4.2's
  `n^{5/2 + (2β-2αβ-1)/6 + (4-αβ)μ/6}` into `n^{(5+ω)/3 + 0.640μ}`;
* `(5+β-αβ)/2 = (3+ω)/2` — the corresponding step for Theorem 4.3.

Boundary: `ω`, `α` and `β` are `ℚ`-valued parameters constrained by the relations the
paper quotes; no quantum algorithm, running time or rectangular matrix
multiplication exponent is modelled.  The decimal constants `0.640 = (4-αβ)/6` and
`0.960 = 1 - αβ/4` depend on the numeric value of `αβ` (about `0.16`) and are *not*
derived from the paper's stated inequalities, so they are not claimed here; likewise
Theorem 4.1's exponent `(12-6αβ+β)/(5-2αβ)` is only below `2.473` for small `α`, so
that numeric clause is not claimed.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMatSemiring13.MainResults

/-- Theorem 4.2: with `ω ≤ 2.373`, the dense-input exponent `(5+ω)/3` of the
existence dominance product is at most `2.458`. -/
theorem dense_dominance_exponent_le {ω : ℚ} (hω : ω ≤ 2373 / 1000) :
    (5 + ω) / 3 ≤ 2458 / 1000 := by
  linarith

/-- Section 1 and Theorem 4.3: with `ω ≤ 2.373`, the classical exponent `(3+ω)/2`
is at most `2.687`. -/
theorem classical_exponent_le {ω : ℚ} (hω : ω ≤ 2373 / 1000) :
    (3 + ω) / 2 ≤ 2687 / 1000 := by
  linarith

/-- Theorem 4.2, exponent rewriting: from `β * (1-α) = ω - 2`, the paper's
`5/2 + (2β - 2αβ - 1)/6` equals `(5+ω)/3`.  This is the step that turns the
minimized complexity `n^{5/2 + (2β-2αβ-1)/6 + (4-αβ)μ/6}` into
`n^{(5+ω)/3 + 0.640μ}`. -/
theorem theorem42_exponent_identity {α β ω : ℚ} (hβ : β * (1 - α) = ω - 2) :
    5 / 2 + (2 * β - 2 * α * β - 1) / 6 = (5 + ω) / 3 := by
  linear_combination ((1 / 3 : ℚ)) * hβ

/-- Theorem 4.3, exponent rewriting: from `β * (1-α) = ω - 2`, the paper's
`(5 + β - αβ)/2` equals `(3+ω)/2`, the classical Duan–Pettie exponent. -/
theorem theorem43_exponent_identity {α β ω : ℚ} (hβ : β * (1 - α) = ω - 2) :
    (5 + β - α * β) / 2 = (3 + ω) / 2 := by
  linear_combination ((1 / 2 : ℚ)) * hβ

end Qatlib.Papers.QMatSemiring13.MainResults
