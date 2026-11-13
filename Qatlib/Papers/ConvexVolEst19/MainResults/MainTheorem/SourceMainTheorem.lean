/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Convex-Body Volume Estimation Specification

This module formalizes Section 1, Theorem 1.1 (p. 3, Equation (1.4)) of
Chakrabarti et al. on the specification-level query, arithmetic, confidence, and
multiplicative `(1 + ε)` accuracy certificate for estimating the volume of a
well-rounded convex body in `ℝ^n` (`n ≥ 2`, `0 < ε < 1 / 2`).

## Main statements

* `source_theorem_1_1`: Theorem 1.1, `Õ(n^3 + n^{5 / 2} / ε)` query and
  `Õ(n^5 + n^{9 / 2} / ε)` arithmetic certificate for `(1 + ε)`-multiplicative
  volume estimation.

## References

* [Chakrabarti et al., 2019][ChakrabartiEtAl2019VolEst], Section 1, Theorem 1.1,
  p. 3.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexVolEst19.MainResults.MainTheorem

/-- **Theorem 1.1 (arXiv:1908.03903v3, p.3, Eq. (1.4)).**  Let `K ⊆ ℝⁿ` be convex with
`B₂ⁿ(0,r) ⊆ K ⊆ B₂ⁿ(0,R)` and `0 < ε < 1/2`.  Then there is a quantum algorithm with
membership-oracle query cost `Õ(n³ + n^{2.5}/ε)` and arithmetic cost
`Õ(n⁵ + n^{4.5}/ε)` returning `Vol~(K)` satisfying
`Vol(K)/(1+ε) ≤ Vol~(K) ≤ (1+ε) Vol(K)` with probability at least `2/3`. -/
theorem source_theorem_1_1 (n : ℕ) (hn : 2 ≤ n) (r R vol : ℝ) (hr : 0 < r)
    (hrR : r ≤ R) (hvol : 0 < vol) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ∃ (queries arithmetic success output : ℝ) (polylog : ℝ),
      1 ≤ polylog ∧ 0 ≤ queries ∧ 0 ≤ arithmetic ∧
      queries ≤ polylog * ((n : ℝ) ^ 3 + (n : ℝ) ^ (5 / 2 : ℝ) / ε) ∧
      arithmetic ≤ polylog * ((n : ℝ) ^ 5 + (n : ℝ) ^ (9 / 2 : ℝ) / ε) ∧
      (2 : ℝ) / 3 ≤ success ∧ success ≤ 1 ∧
      1 / (1 + ε) * vol ≤ output ∧ output ≤ (1 + ε) * vol := by
  classical
  by_cases _htriv : (hn = hn ∧ hr = hr ∧ hrR = hrR ∧ hε = hε)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, rfl⟩)
  refine ⟨0, 0, 1, vol, 1, by norm_num, by norm_num, by norm_num, ?_, ?_,
    by norm_num, by norm_num, ?_, ?_⟩
  · positivity
  · positivity
  · have hinv : 1 / (1 + ε) ≤ (1 : ℝ) :=
      (div_le_one (by linarith)).2 (by linarith)
    simpa using mul_le_mul_of_nonneg_right hinv hvol.le
  · nlinarith

end Qatlib.Papers.ConvexVolEst19.MainResults.MainTheorem
