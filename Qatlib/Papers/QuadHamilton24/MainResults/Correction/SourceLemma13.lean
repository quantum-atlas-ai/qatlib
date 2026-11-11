/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 13 (relative error of the reconstructed velocity)

Source: arXiv:2404.07303, Appendix A, Lemma 13 and (A.1)–(A.3), page 51.

The source bounds the per-component error of the reconstructed solution in the
`b = 0` case by
`‖Πᵢ (x(T) − x̂)‖ ≤ (m e³ / (k+1)!) ‖Πᵢ x(T)‖ ≤ ε ‖Πᵢ x(T)‖`,
and then chooses `i` to be the `q̇ᵢ` component, which gives (A.1)
`|q̇ᵢ − q̇̂ᵢ| ≤ ε q̇ᵢ`.

We formalise the component-wise step exactly: the per-component bound (A.2) together
with the source's parameter choice (A.3) implies the relative bound (A.1).  For a
complex scalar component the norm is `|·|`, so this is the literal statement.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

/-- **Lemma 13 (A.2)–(A.3) ⇒ (A.1).**  If every component of the error is bounded by
`(m e³/(k+1)!)` times that component of `x`, and the source's parameter choice makes
that factor at most `ε`, then the component-wise relative error is at most `ε`. -/
theorem lemma13_componentRelativeError
    {ι : Type*} (m k : ℕ) (ε : ℝ) (x xhat : ι → ℂ) (i : ι)
    (hbound : ‖x i - xhat i‖ ≤
      (m * Real.exp 3 / ((Nat.factorial (k + 1) : ℕ) : ℝ)) * ‖x i‖)
    (hchoose : (m * Real.exp 3 / ((Nat.factorial (k + 1) : ℕ) : ℝ)) ≤ ε) :
    ‖x i - xhat i‖ ≤ ε * ‖x i‖ := by
  refine hbound.trans (mul_le_mul_of_nonneg_right hchoose (norm_nonneg _))

/-- **Lemma 13, componentwise form (A.1).**  With `q̇ᵢ` the `i`-th entry of `x(T)` and
`q̇̂ᵢ` the corresponding entry of the approximation, the premise (A.2)–(A.3) gives
`|q̇ᵢ − q̇̂ᵢ| ≤ ε q̇ᵢ` when `q̇ᵢ ≥ 0` (so that `‖q̇ᵢ‖ = q̇ᵢ`). -/
theorem lemma13_velocityRelativeError
    (m k : ℕ) (ε qdot qdotHat : ℝ) (hq : 0 ≤ qdot)
    (hbound : ‖qdot - qdotHat‖ ≤
      (m * Real.exp 3 / ((Nat.factorial (k + 1) : ℕ) : ℝ)) * ‖qdot‖)
    (hchoose : (m * Real.exp 3 / ((Nat.factorial (k + 1) : ℕ) : ℝ)) ≤ ε) :
    |qdot - qdotHat| ≤ ε * qdot := by
  have hreal : ‖(qdot - qdotHat : ℝ)‖ = |qdot - qdotHat| := Real.norm_eq_abs _
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hq] at hbound
  calc |qdot - qdotHat| ≤
        (m * Real.exp 3 / ((Nat.factorial (k + 1) : ℕ) : ℝ)) * qdot := hbound
    _ ≤ ε * qdot := mul_le_mul_of_nonneg_right hchoose hq

end Qatlib.Papers.QuadHamilton24.MainResults
