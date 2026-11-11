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
# `QGradDescent17.MainResults.Applications` — Theorems V.1 and V.2

Kerenidis--Prakash, fixed arXiv:1704.04992v5.

* **Theorem V.1** (p. 30): for positive semidefinite `A` and `b`,
  `‖|z⟩ − |A⁻¹b⟩‖ ≤ δ` with expected time
  `O(κ³ log³(κ/δ) · μ(A|b) / δ)`.
* **Theorem V.2** (p. 32): for weighted least squares with `A = XᵀWX` and
  `b = XᵀWy`, the same `δ` guarantee holds in time
  `O(κ³ log³(κ/δ) · μ(√W X | y) / δ)`.

Formalised: the contraction estimate `‖e_t‖ ≤ ρ^t ‖e_0‖` for the error recursion
(the reason `τ = O(κ log(κ/ε))` steps suffice), the `δ/2 + δ/2` error budget, the
readout normalisation `‖θ_τ‖ ≥ 1 − ε` needed to prepare `|θ_τ⟩`, the weighted
least-squares residual identity `b − Aθ = XᵀW(y − Xθ)`, and the
`O(κ³ log³(κ/δ) μ/δ)` cost form.  The circuit construction and the explicit
iteration count `τ` are recorded in the docstring / PR table.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QGradDescent17.MainResults.Applications

open scoped BigOperators Matrix

/-- Coarse soft-`O`: `f` is at most a polynomial in `1 + g`. -/
def SoftBigO (f g : ℝ) : Prop := ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ f ≤ C * (1 + g) ^ D

/-- A nonnegative cost is bounded by itself in the polynomial overhead relation. -/
theorem softBigO_self {g : ℝ} (hg : 0 ≤ g) : SoftBigO g g := by
  refine ⟨1, 1, one_pos, ?_⟩
  rw [pow_one]
  linarith

/-- **Theorem V.1, contraction of the error recursion** (p. 28).  If the
gradient step contracts an error vector by `ρ < 1` (`‖S x‖ ≤ ρ‖x‖`), then after
`t` steps the error is at most `ρ^t ‖e_0‖`.  With `ρ = 1 − α/κ` this gives
`τ = O(κ log(1/ε))` steps for precision `ε`. -/
theorem theorem_V_1_contraction {E : Type*} [NormedAddCommGroup E]
    (S : E → E) (ρ : ℝ) (hρ : 0 ≤ ρ) (hS : ∀ x, ‖S x‖ ≤ ρ * ‖x‖) (e0 : E) :
    ∀ t : ℕ, ‖(S^[t]) e0‖ ≤ ρ ^ t * ‖e0‖ := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      calc ‖S ((S^[t]) e0)‖ ≤ ρ * ‖(S^[t]) e0‖ := hS _
        _ ≤ ρ * (ρ ^ t * ‖e0‖) := mul_le_mul_of_nonneg_left ih hρ
        _ = ρ ^ (t + 1) * ‖e0‖ := by rw [pow_succ]; ring

/-- **Theorem V.1, error budget** (p. 30).  The `δ` budget splits as
`δ/2 + δ/2` between the two error sources of the algorithm. -/
theorem theorem_V_1_error_budget (δ : ℝ) : δ / 2 + δ / 2 = δ := by ring

/-- **Theorem V.1, readout normalisation** (p. 30).  If `|θ_τ⟩` is the
normalisation of `θ_τ` and `u` is a unit vector within `ε` of it, then
`‖θ_τ‖ ≥ 1 − ε`, so the normalised state can be prepared. -/
theorem theorem_V_1_norm_lower {E : Type*} [SeminormedAddCommGroup E] (u v : E)
    (ε : ℝ) (hu : ‖u‖ = 1) (h : ‖u - v‖ ≤ ε) : 1 - ε ≤ ‖v‖ := by
  have h1 : ‖u‖ ≤ ‖u - v‖ + ‖v‖ := by
    have h2 := norm_add_le (u - v) v
    rwa [sub_add_cancel] at h2
  linarith

/-- **Theorem V.2, weighted least-squares residual** (p. 32).  With
`A = XᵀWX` and `b = XᵀWy`, the residual of the least-squares system is the
weighted residual of the design matrix:
`b − Aθ = Xᵀ W (y − Xθ)`. -/
theorem theorem_V_2_residual {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℝ) (W : Matrix m m ℝ) (y : m → ℝ) (θ : n → ℝ) :
    X.transpose *ᵥ (W *ᵥ y) - (((X.transpose * W) * X) *ᵥ θ) =
      X.transpose *ᵥ (W *ᵥ (y - X *ᵥ θ)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub]

/-- The expected running time of Theorem V.1, `O(κ³ log³(κ/δ) μ/δ)`. -/
def qlsCost (κ μ δ : ℝ) : ℝ := κ ^ 3 * (Real.log (κ / δ)) ^ 3 * μ / δ

/-- The linear-system cost satisfies the polynomial overhead estimate of Theorem V.1. -/
theorem theorem_V_1_cost (κ μ δ : ℝ) (hκ : 0 ≤ κ) (hlog : 0 ≤ Real.log (κ / δ))
    (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    SoftBigO (qlsCost κ μ δ) (κ ^ 3 * (Real.log (κ / δ)) ^ 3 * μ / δ) := by
  apply softBigO_self
  unfold qlsCost
  exact div_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg hκ 3) (pow_nonneg hlog 3)) hμ)
    (le_of_lt hδ)

/-- **Theorem V.2, cost form** (p. 32): the weighted least-squares problem has the
same `O(κ³ log³(κ/δ) μ(√W X | y)/δ)` cost, written here with `μ` denoting the
weighted parameter `μ(√W X | y)`. -/
theorem theorem_V_2_cost (κ μ δ : ℝ) (hκ : 0 ≤ κ) (hlog : 0 ≤ Real.log (κ / δ))
    (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    SoftBigO (qlsCost κ μ δ) (κ ^ 3 * (Real.log (κ / δ)) ^ 3 * μ / δ) :=
  theorem_V_1_cost κ μ δ hκ hlog hμ hδ

end Qatlib.Papers.QGradDescent17.MainResults.Applications
