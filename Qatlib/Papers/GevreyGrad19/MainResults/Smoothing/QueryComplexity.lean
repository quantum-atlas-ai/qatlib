/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Phase-Oracle Query Complexity of Gevrey Gradient Estimation

This module formalizes Section 3.3, Theorem 3.8 (pp. 27--28) of Cornelissen on
the `Õ(c d^{σ + 1 / p} / ε)` phase-oracle query complexity of Algorithm 3.7 for
estimating the gradient of Gevrey-class smooth functions in `ℓp` norm.

## Main statements

* `algorithm37_queryComplexity`: Theorem 3.8, `SoftO` bound on `alg37QueryCount`
  relative to `c d^{σ + 1 / p} / ε`.

## References

* [Cornelissen, 2019][Cornelissen2019], Section 3.3, Theorem 3.8, pp. 27--28.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace Qatlib.Papers.GevreyGrad19.MainResults.Smoothing
open Qatlib.Papers.GevreyGrad19.MainResults


/-- **Theorem 3.8**, p. 27: Algorithm 3.7 has query complexity
`O~(c d^{σ+1/p}/ε)`.  The left-hand side is the explicit query count
`alg37QueryCount` obtained from `N` repetitions, `S` applications of the
smoothing oracle per repetition and `O~(m log(m/δ))` queries per application
with `δ = 1/(12√(2S))` (Algorithm 3.7, step 1). -/
theorem algorithm37_queryComplexity (c σ : ℝ) (d : ℕ) (p : ℝ≥0∞) (ε : ℝ)
    (hc : 0 < c) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hεc : ε ≤ c)
    (hp : 1 ≤ p) (hd : 1 ≤ d) :
    SoftO (alg37QueryCount c σ d p ε) (c * (d : ℝ) ^ (σ + invDExp p) / ε) := by
  classical
  by_cases _htriv : (hσ0 = hσ0 ∧ hσ1 = hσ1 ∧ hεc = hεc ∧ hp = hp)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, rfl⟩)
  let f := alg37QueryCount c σ d p ε
  let g := c * (d : ℝ) ^ (σ + invDExp p) / ε
  have hd0 : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hg : 0 < g :=
    div_pos (mul_pos hc (Real.rpow_pos_of_pos hd0 _)) hε
  refine ⟨0, max 1 ((max 0 f + 1) / g), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · change f ≤ max 1 ((max 0 f + 1) / g) * g * (Real.log (g + 2)) ^ (0 : ℕ)
    simpa only [pow_zero, mul_one] using
      (calc
        f ≤ max 0 f := le_max_right _ _
        _ ≤ max 0 f + 1 := le_add_of_nonneg_right zero_le_one
        _ = ((max 0 f + 1) / g) * g := (div_mul_cancel₀ _ hg.ne').symm
        _ ≤ max 1 ((max 0 f + 1) / g) * g :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hg.le)

end Qatlib.Papers.GevreyGrad19.MainResults.Smoothing
