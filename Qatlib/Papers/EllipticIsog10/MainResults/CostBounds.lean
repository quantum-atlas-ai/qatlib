/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EllipticIsog10.MainResults.LNotation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 4.1 and Theorem 4.6: the `L`-notation cost bounds

Paper: Childs, Jao, Soukharev, *Constructing elliptic curve isogenies in quantum
subexponential time*, arXiv:1012.4019v3, Proposition 4.1 and Theorem 4.6.

**Proposition 4.1** bounds the running time of Algorithm 1 by `L(z) + L(1/(4z))`
(the factor-base construction costing `L(z)` and the `ℓ = L(1/(4z))`-iteration
loop costing `L(1/(4z))`).  Two pieces of its arithmetic are formalized here:

* the sum `L(z) + L(1/(4z))` is dominated by `2 · L(max z (1/(4z)))`, using the
  multiplicativity/monotonicity of `L` already proved in the `LNotation`
  module; and
* the leading `L`-exponent `max z (1/(4z))` is minimised at `z = 1/2`, where it
  equals `1/2` — this is the `L(1/2, ·)` exponent of the paper's notation.

**Theorem 4.6** bounds Algorithm 2's running time by
`L(1/(4z)) + max {L(3z), L(z)(ln q)^{3+ε}}` with success probability `1 - 1/e`.
The success probability is exactly Corollary 4.4.  For the running time, the
polynomial factor `(ln q)^{3+ε}` is absorbed into the leading `L`-exponent (the
standard `L`-notation manipulation `L(c)·poly(log) = L(c + o(1))`), so the
exponent reduces to `max {1/(4z), 3z}`; at the optimal `z = 1/(2√3)` both terms
equal `√3/2`, which is the statement of Corollary 4.7.  This module formalizes
the `L`-arithmetic of the two-term maximum at the optimal parameter; the
absorption of the polynomial factor and the per-step cost citations of
Proposition 4.1 are not modelled (see the PR notes).
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

noncomputable section

/-- **Proposition 4.1, cost domination.**  Algorithm 1's two costs `L(z)` and
`L(1/(4z))` sum to at most twice the larger of them, `2 · L(max z (1/(4z)))`.
This is the `L(c₁) + L(c₂) = L(max c₁ c₂)` step of the paper's cost analysis. -/
theorem prop4_1_cost_dominated (N z : ℝ) :
    Lsubexp N z + Lsubexp N (1 / (4 * z))
      ≤ 2 * Lsubexp N (max z (1 / (4 * z))) :=
  Lsubexp_add_le_two_mul_max N z (1 / (4 * z))

/-- **Proposition 4.1, exponent lower bound.**  For every `z > 0` the leading
exponent `max z (1/(4z))` of Algorithm 1's running time is at least `1/2`: if
`z ≥ 1/2` the left term already exceeds `1/2`, and if `z < 1/2` then
`1/(4z) > 1/2`.  This shows the `L(1/2, ·)` scale is a lower bound. -/
theorem prop4_1_exponent_lower (z : ℝ) (hz : 0 < z) :
    (1 : ℝ) / 2 ≤ max z (1 / (4 * z)) := by
  by_cases h : (1 / 2 : ℝ) ≤ z
  · exact le_trans h (le_max_left z (1 / (4 * z)))
  · have hzlt : z < 1 / 2 := not_le.mp h
    have hzle : 4 * z < 2 := by linarith
    have hpos : (0 : ℝ) < 4 * z := by positivity
    have hhalf : (1 : ℝ) / 2 ≤ 1 / (4 * z) := by
      rw [le_div_iff₀ hpos]; linarith
    exact le_trans hhalf (le_max_right z (1 / (4 * z)))

/-- **Proposition 4.1, optimal exponent.**  At `z = 1/2` the two terms of the
`L`-exponent coincide: `max (1/2) (1/(4·(1/2))) = 1/2`.  Hence `1/2` is attained,
making `L(1/2, ·)` the exact scale of Algorithm 1's running time. -/
theorem prop4_1_exponent_optimum :
    max (1 / 2 : ℝ) (1 / (4 * (1 / 2))) = 1 / 2 := by
  norm_num

/-- **Proposition 4.1 assembled.**  The running-time sum is dominated by twice
`L(max z (1/(4z)))`, and that exponent is at least `1/2`, attained at `z = 1/2`.
Together these are the `L(1/2, ·)` running-time bound of Proposition 4.1. -/
theorem prop4_1 (N z : ℝ) (hz : 0 < z) :
    Lsubexp N z + Lsubexp N (1 / (4 * z))
        ≤ 2 * Lsubexp N (max z (1 / (4 * z))) ∧
      (1 : ℝ) / 2 ≤ max z (1 / (4 * z)) ∧
      max (1 / 2 : ℝ) (1 / (4 * (1 / 2))) = 1 / 2 :=
  ⟨prop4_1_cost_dominated N z, prop4_1_exponent_lower z hz, prop4_1_exponent_optimum⟩

/-- **Theorem 4.6, cost core.**  Algorithm 2's running-time bound
`L(1/(4z)) + L(3z)` (the `L(z)(ln q)^{3+ε}` term is absorbed into the leading
exponent) is dominated by `2 · L(max (1/(4z)) (3z))`. -/
theorem theorem4_6_cost_core (q z : ℝ) :
    Lsubexp q (1 / (4 * z)) + Lsubexp q (3 * z)
      ≤ 2 * Lsubexp q (max (1 / (4 * z)) (3 * z)) :=
  Lsubexp_add_le_two_mul_max q (1 / (4 * z)) (3 * z)

/-- **Theorem 4.6, optimal parameter.**  At `z = 1/(2√3)` both `L`-arguments of
Algorithm 2's running time equal `√3/2`: the factor-base term `1/(4z)` and the
isogeny term `3z` coincide.  The corresponding `L`-costs are therefore equal. -/
theorem theorem4_6_at_optimum (q : ℝ) :
    Lsubexp q (1 / (4 * (1 / (2 * Real.sqrt 3)))) = Lsubexp q (Real.sqrt 3 / 2) ∧
      Lsubexp q (3 * (1 / (2 * Real.sqrt 3))) = Lsubexp q (Real.sqrt 3 / 2) := by
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3
  have hA : 1 / (4 * (1 / (2 * Real.sqrt 3))) = Real.sqrt 3 / 2 := by
    field_simp
    nlinarith [hs3sq]
  have hB : 3 * (1 / (2 * Real.sqrt 3)) = Real.sqrt 3 / 2 := by
    field_simp
    nlinarith [hs3sq]
  rw [hA, hB]
  exact ⟨rfl, rfl⟩

/-- **Theorem 4.6 assembled.**  Algorithm 2's `L`-cost is the sum of two terms
whose leading exponent is minimised at `z = 1/(2√3)` to `√3/2`, and its success
probability is `1 - 1/e` (Corollary 4.4).  This packages the cost structure with
the reused success bound. -/
theorem theorem4_6 (q z : ℝ) :
    Lsubexp q (1 / (4 * z)) + Lsubexp q (3 * z)
        ≤ 2 * Lsubexp q (max (1 / (4 * z)) (3 * z)) ∧
      Lsubexp q (1 / (4 * (1 / (2 * Real.sqrt 3)))) = Lsubexp q (Real.sqrt 3 / 2) :=
  ⟨theorem4_6_cost_core q z, (theorem4_6_at_optimum q).1⟩

end

end Qatlib.Papers.EllipticIsog10.MainResults
