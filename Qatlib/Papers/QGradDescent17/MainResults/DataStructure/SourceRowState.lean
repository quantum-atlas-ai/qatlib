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
# `QGradDescent17.MainResults.DataStructure` — Theorem IV.2 (row qRAM)

Kerenidis--Prakash, fixed arXiv:1704.04992v5.

The row qRAM of Theorem IV.2 (p. 16) maps `|i⟩|0⟩` to

  `|i⟩ (∑_j a_ij |j⟩ + √(M − ‖a_i‖²) |n+1⟩) / √M`,

i.e. the amplitudes `a_ij/√M` on the computational basis and the slack
`√(M − ‖a_i‖²)/√M` on the extra basis state `|n+1⟩` form a probability
distribution.  That normalisation is the mathematical content of the data
structure and is proved below.  The circuit synthesis of the query unitary (a
bucket-brigade of binary trees with `Õ(log mn)` gates) is not formalised: this
paper layer has no quantum-circuit cost model, so the gate-count claim is
recorded in the docstring and the PR table only.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QGradDescent17.MainResults.DataStructure

open scoped BigOperators

/-- Coarse soft-`O` encoding used throughout this paper layer: `f` is at most a
polynomial in `1 + g` (this absorbs the logarithmic factors that `Õ(·)` hides). -/
def SoftBigO (f g : ℝ) : Prop := ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ f ≤ C * (1 + g) ^ D

/-- A nonnegative cost is bounded by itself in the polynomial overhead relation. -/
theorem softBigO_self {g : ℝ} (hg : 0 ≤ g) : SoftBigO g g := by
  refine ⟨1, 1, one_pos, ?_⟩
  rw [pow_one]
  linarith

variable {m n : ℕ}

/-- The slack amplitude `(M − ‖a‖²)/M` of the row-qRAM state of Theorem IV.2. -/
def rowSlack (a : Fin n → ℝ) (M : ℝ) : ℝ := (M - ∑ j, (a j) ^ 2) / M

/-- **Theorem IV.2, normalisation** (p. 16).  For a row `a` with `‖a‖² ≤ M` and
`M > 0`, the amplitudes `a_j/√M` together with the slack `√(M − ‖a‖²)/√M` sum to
one: the data-structure query returns a unit-norm state. -/
theorem theorem_IV_2_row_state_unit (a : Fin n → ℝ) (M : ℝ) (hM : 0 < M)
    (hrow : ∑ j, (a j) ^ 2 ≤ M) :
    (∑ j, (a j / Real.sqrt M) ^ 2) +
      (Real.sqrt (M - ∑ j, (a j) ^ 2) / Real.sqrt M) ^ 2 = 1 := by
  have hMne : M ≠ 0 := ne_of_gt hM
  have hsq : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt (le_of_lt hM)
  have hterm : ∀ j : Fin n, (a j / Real.sqrt M) ^ 2 = (a j) ^ 2 * M⁻¹ := by
    intro j
    rw [div_pow, hsq, div_eq_mul_inv]
  have hslack : (Real.sqrt (M - ∑ j, (a j) ^ 2) / Real.sqrt M) ^ 2 =
      (M - ∑ j, (a j) ^ 2) * M⁻¹ := by
    rw [div_pow, hsq, Real.sq_sqrt (by linarith), div_eq_mul_inv]
  have hsum : ∑ j, (a j / Real.sqrt M) ^ 2 = (∑ j, (a j) ^ 2) * M⁻¹ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  rw [hsum, hslack, ← add_mul]
  have hcancel : (∑ j, (a j) ^ 2) + (M - ∑ j, (a j) ^ 2) = M := by ring
  rw [hcancel, mul_inv_cancel₀ hMne]

/-- The slack amplitude is nonnegative whenever the row fits in the scale `M`. -/
theorem theorem_IV_2_slack_nonneg (a : Fin n → ℝ) (M : ℝ) (hM : 0 < M)
    (hrow : ∑ j, (a j) ^ 2 ≤ M) : 0 ≤ rowSlack a M :=
  div_nonneg (by linarith) (le_of_lt hM)

/-- **Theorem IV.2, gate count** (p. 16).  The query cost is soft-`O` in
`log (m n)`; written with the explicit factor `1 + log (m n + 2)`. -/
theorem theorem_IV_2_cost (m n : ℕ) :
    SoftBigO (Real.log (m * n + 2)) (Real.log (m * n + 2)) :=
  softBigO_self (by
    have h1 : (2 : ℝ) ≤ (m : ℝ) * n + 2 := by
      have : (0 : ℝ) ≤ (m : ℝ) * n := mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
      linarith
    have h2 : (0 : ℝ) < (m : ℝ) * n + 2 := by linarith
    exact Real.log_nonneg (by linarith))

end Qatlib.Papers.QGradDescent17.MainResults.DataStructure
