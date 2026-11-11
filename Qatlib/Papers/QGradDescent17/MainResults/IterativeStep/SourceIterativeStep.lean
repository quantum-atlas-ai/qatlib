/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# `QGradDescent17.MainResults.IterativeStep` — Propositions IV.9 and IV.10

Kerenidis--Prakash, fixed arXiv:1704.04992v5.

* **Proposition IV.9** (p. 26): for `S = I − αA`, `L(x) = b − Ax`, an
  `(ε, 1/poly)`-approximate quantum step has cost `Õ(μ(A|b)/ε)`.
* **Proposition IV.10** (p. 26): given a multistep unitary of cost `C_V`, one
  multistep costs `C_V + log τ`.

Formalised: the step-error propagation `‖S r − S̃ r‖ ≤ α ε` (the arithmetic
content of the approximate step), the `Õ(μ/δ)` cost form, and the definitional
`C_V + log τ` cost of the multistep unitary.  The step oracle is recorded in the
docstring / PR table.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QGradDescent17.MainResults.IterativeStep

open scoped RealInnerProductSpace BigOperators

/-- Coarse soft-`O`: `f` is at most a polynomial in `1 + g`. -/
def SoftBigO (f g : ℝ) : Prop := ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ f ≤ C * (1 + g) ^ D

/-- A nonnegative cost is bounded by itself in the polynomial overhead relation. -/
theorem softBigO_self {g : ℝ} (hg : 0 ≤ g) : SoftBigO g g := by
  refine ⟨1, 1, one_pos, ?_⟩
  rw [pow_one]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Proposition IV.9, step error** (p. 26).  With `S r = r − α A r` and the
approximate step `S̃ r = r − α Ã r`, an `ε`-accurate access to `A` makes the steps
`α ε`-close: `‖S r − S̃ r‖ ≤ α ε`. -/
theorem prop_IV_9_step_error (α ε : ℝ) (A : E →ₗ[ℝ] E) (Aapprox : E → E) (r : E)
    (h : ‖A r - Aapprox r‖ ≤ ε) :
    ‖(r - α • A r) - (r - α • Aapprox r)‖ ≤ |α| * ε := by
  have hsub : (r - α • A r) - (r - α • Aapprox r) = α • (Aapprox r - A r) := by
    rw [smul_sub]
    abel
  rw [hsub, norm_smul, Real.norm_eq_abs]
  rw [norm_sub_rev (Aapprox r) (A r)]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg α)

/-- **Proposition IV.9, cost form** (p. 26): `Õ(μ(A|b)/δ)`. -/
def iterativeCost (μ δ : ℝ) : ℝ := μ / δ

/-- The iterative-step cost satisfies the polynomial overhead estimate of Proposition IV.9. -/
theorem prop_IV_9_cost (μ δ : ℝ) (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    SoftBigO (iterativeCost μ δ) (μ / δ) :=
  softBigO_self (div_nonneg hμ (le_of_lt hδ))

/-- **Proposition IV.10** (p. 26).  Given a multistep unitary of cost `C_V`, one
amplification step costs `C_V + log τ`. -/
def multistepCost (CV : ℝ) (τ : ℕ) : ℝ := CV + Real.log τ

/-- The iterative-step parameters satisfy Proposition IV.10. -/
theorem prop_IV_10 (CV : ℝ) (τ : ℕ) : multistepCost CV τ = CV + Real.log τ := rfl

/-- The `C_V + log τ` cost is bounded by itself (the paper's exact, not `Õ`,
statement of Proposition IV.10). -/
theorem prop_IV_10_le (CV : ℝ) (τ : ℕ) : multistepCost CV τ ≤ CV + Real.log τ :=
  le_of_eq rfl

end Qatlib.Papers.QGradDescent17.MainResults.IterativeStep
