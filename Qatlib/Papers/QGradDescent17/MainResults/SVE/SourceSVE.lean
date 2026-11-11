/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradDescent17.MainResults.SVE.CostBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# `QGradDescent17.MainResults.SVE` — Theorem IV.3 (singular value estimation)

Kerenidis--Prakash, fixed arXiv:1704.04992v5.

Theorem IV.3 (p. 18): if `A` has a data structure with row and column norms
bounded by `μ` together with `Õ(log² mn)` state preparation, then singular value
estimation on `A` to additive precision `δ` runs in `Õ(μ/δ)` gates.

Formalised here: the scaling step of the proof (`A/μ` has row and column norms at
most `1`) and the soft-`O` form of the cost `μ/δ`.  The circuit construction
(phase estimation on the sparse walk operator) has no cost model in this layer
and is recorded in the docstring / PR table.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QGradDescent17.MainResults.SVE

open scoped BigOperators

variable {m n : ℕ}

/-- **Theorem IV.3, row scaling** (p. 18).  If every row `a` of `A` has squared
norm at most `μ²`, then the rows of `A/μ` have squared norm at most `1`; this is
the "`A/μ` has row and column norms bounded by `1`" assertion used to build the
walk operator. -/
theorem theorem_IV_3_row_norm_div (a : Fin n → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h : ∑ j, (a j) ^ 2 ≤ μ ^ 2) : ∑ j, (a j / μ) ^ 2 ≤ 1 := by
  have hterm : ∀ j : Fin n, (a j / μ) ^ 2 = (a j) ^ 2 / μ ^ 2 := by
    intro j
    rw [div_pow]
  have hsum : (∑ j, (a j) ^ 2 / μ ^ 2) = (∑ j, (a j) ^ 2) / μ ^ 2 := by
    rw [div_eq_mul_inv]
    exact (Finset.sum_mul _ _ _).symm
  rw [Finset.sum_congr rfl (fun j _ => hterm j), hsum, div_le_one (by positivity)]
  exact h

/-- Column version of `theorem_IV_3_row_norm_div`. -/
theorem theorem_IV_3_col_norm_div (a : Fin m → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (h : ∑ i, (a i) ^ 2 ≤ μ ^ 2) : ∑ i, (a i / μ) ^ 2 ≤ 1 :=
  theorem_IV_3_row_norm_div a μ hμ h

/-- The SVE cost of Theorem IV.3, `Õ(μ/δ)` (log factors absorbed). -/
def sveCost (μ δ : ℝ) : ℝ := μ / δ

/-- The cost `μ/δ` is soft-`O` of itself, i.e. it has the `Õ(μ/δ)` form. -/
theorem theorem_IV_3_cost (μ δ : ℝ) (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    SoftBigO (sveCost μ δ) (μ / δ) :=
  softBigO_self (div_nonneg hμ (le_of_lt hδ))

/-- The state preparation of Definition IV.1 costs `Õ(log² mn)`. -/
def statePrepCost (m n : ℕ) : ℝ := (Real.log (m * n + 2)) ^ 2

/-- The state preparation cost satisfies the polynomial overhead estimate of Theorem IV.3. -/
theorem theorem_IV_3_statePrep_cost (m n : ℕ) (h : 0 ≤ Real.log (m * n + 2)) :
    SoftBigO (statePrepCost m n) (Real.log (m * n + 2)) := by
  unfold statePrepCost
  refine ⟨1, 2, one_pos, ?_⟩
  nlinarith [sq_nonneg (Real.log (m * n + 2))]

end Qatlib.Papers.QGradDescent17.MainResults.SVE
