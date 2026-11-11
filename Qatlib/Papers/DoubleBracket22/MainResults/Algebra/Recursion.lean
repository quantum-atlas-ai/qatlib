/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DoubleBracket22.MainResults.Model.DoubleBracketModel

set_option backward.isDefEq.respectTransparency false

/-!
# DoubleBracket22 — Lemma 10 (recursion for the recursive discretization)

Source: arXiv:2206.11772v4, Lemma 10, Eqs. (127)–(128), printed p. 27.

For `a ≠ 0` and real `b`, the closed form `α_k = ((1+a)^k − 1)/a · b` solves
the affine recursion `α_{k+1} = (1+a)α_k + b` and starts at `α_0 = 0`.
Proved here by the paper's direct algebraic induction (Eqs. (129)–(132)).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius BigOperators

namespace Qatlib.Papers.DoubleBracket22.MainResults.Algebra

/-- Lemma 10, Eq. (127)–(128), p. 27. With `a ≠ 0`, the sequence
`α_k = ((1+a)^k − 1)/a · b` satisfies `α_{k+1} = (1+a)α_k + b` for every
`k ≥ 0`, and `α_0 = 0`. -/
theorem lemma10_recursion (a b : ℝ) (ha : a ≠ 0) :
    (∀ k : ℕ,
        ((1 + a) ^ (k + 1) - 1) / a * b = (1 + a) * (((1 + a) ^ k - 1) / a * b) + b) ∧
      ((1 + a) ^ 0 - 1) / a * b = 0 := by
  constructor
  · intro k
    rw [pow_succ]
    field_simp
    ring
  · simp

end Qatlib.Papers.DoubleBracket22.MainResults.Algebra
