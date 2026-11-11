/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Success probability of the bounded-error coin-finding algorithm (Counterfeit10, Theorem 1)

Formal companion to Iwama–Nishimura–Raymond–Teruyama,
*Quantum Counterfeit Coin Problems*, arXiv:1009.0416v1, Section 2, proof of Theorem 1.

After one round of `Find∗(k)` the register state is
`|x⟩|0⟩ - 2 W^{-1}(Σ |q̃⟩|err_q̃'⟩)`.  Lemma 2 bounds the squared norm (the failure
mass `ε`) of the second term by `1/400`, so its amplitude is at most `√(1/400) = 1/20`.
Measuring in the computational basis therefore recovers the true oracle `x` with
probability at least `(1 - √(1/400))^2`, which the paper observes is `> 9/10`.
This file records that arithmetic step exactly (`(19/20)^2 = 361/400 > 9/10`).
-/

namespace Qatlib.Papers.Counterfeit10.MainResults

/-- The failure mass `1/400` has square root `1/20`. -/
lemma sqrt_one_four_hundred : Real.sqrt (1 / 400) = 1 / 20 := by
  have h : (1 / 400 : ℝ) = (1 / 20) ^ 2 := by norm_num
  rw [h]
  exact Real.sqrt_sq (by norm_num)

/-- Theorem 1 (arXiv:1009.0416v1, §2): given the Lemma 2 failure mass `ε ≤ 1/400`,
the success amplitude is `1 - √ε ≥ 1 - √(1/400)`, so the identification probability
`(1 - √(1/400))^2` is strictly larger than `9/10`. -/
theorem amplification_success_gt_nine_tenths :
    ((1 : ℝ) - Real.sqrt (1 / 400)) ^ 2 > 9 / 10 := by
  rw [sqrt_one_four_hundred]
  norm_num

/-- The exact value of that success-probability lower bound, `(19/20)^2 = 361/400`. -/
theorem amplification_success_eq :
    ((1 : ℝ) - Real.sqrt (1 / 400)) ^ 2 = 361 / 400 := by
  rw [sqrt_one_four_hundred]
  norm_num

end Qatlib.Papers.Counterfeit10.MainResults
