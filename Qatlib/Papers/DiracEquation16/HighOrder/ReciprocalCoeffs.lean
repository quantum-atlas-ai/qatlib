/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Higher-order reciprocal splittings of Appendix A

Appendix A of [FillionGourdeauMacLeanLaflamme2017] constructs higher-order symmetric splittings
by Suzuki's iteration: the `m`-th order approximant is a product of `r` copies of the
`(m-1)`-th order approximant at scaled times `pᵢ Δt`, constrained by
`∑ pᵢ = 1` and `∑ pᵢᵐ = 0` (Eq. (A4)). For `m = 3`, Table II lists rational splittings in
terms of the reciprocals `p̃ᵢ = 1 / pᵢ`, including the length-seven row
`p̃ = (6, 6, 6, 3, 3, 3, -2)`. This row requires signed carriers even though Eq. (A5)
prints a natural-number condition.

This module verifies the length-seven row of Table II: every coefficient is a nonzero rational,
one of them is negative (so a natural-number-only carrier is impossible), the scaled parameters
satisfy the two Suzuki conditions of Eq. (A4), and the equivalent product form of Eq. (A5)
relating erased products to the full product holds for the row and for its cubes.

## Main statements

* `table2Row7Reciprocals_nonzero`: every reciprocal carrier of the row is nonzero.
* `table2Row7Reciprocals_exists_negative`: the row contains a negative coefficient.
* `table2Row7_sum_param_eq_one`: `∑ pᵢ = 1` for the row, Eq. (A4) with `m = 3`.
* `table2Row7_sum_cube_param_eq_zero`: `∑ pᵢ³ = 0` for the row, Eq. (A4) with `m = 3`.
* `sum_prod_erase_eq_prod_mul_sum_inv`: the product identity behind Eq. (A5) for carriers
  with all entries nonzero.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.DiracEquation16.HighOrder

/-- The reciprocal carriers `p̃ᵢ` of the length-seven row of Table II of
[FillionGourdeauMacLeanLaflamme2017], Appendix A. The splitting parameters are `pᵢ = 1 / p̃ᵢ`. -/
def table2Row7Reciprocals : Fin 7 → ℚ := ![6, 6, 6, 3, 3, 3, -2]

/-- Every reciprocal carrier of the row is nonzero. -/
theorem table2Row7Reciprocals_nonzero : ∀ i, table2Row7Reciprocals i ≠ 0 := by
  intro i
  fin_cases i <;> norm_num [table2Row7Reciprocals, Matrix.cons_val]

/-- The row contains a negative coefficient, so it cannot be carried by natural numbers
alone. -/
theorem table2Row7Reciprocals_exists_negative : ∃ i, table2Row7Reciprocals i < 0 := by
  refine ⟨6, ?_⟩
  norm_num [table2Row7Reciprocals, Matrix.cons_val]

/-- The first Suzuki condition of Eq. (A4) for the length-seven row: the splitting parameters
sum to one. -/
theorem table2Row7_sum_param_eq_one : ∑ i, (table2Row7Reciprocals i)⁻¹ = 1 := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  norm_num [table2Row7Reciprocals, Matrix.cons_val]

/-- The second Suzuki condition of Eq. (A4) for the length-seven row with `m = 3`: the cubes of
the splitting parameters sum to zero. -/
theorem table2Row7_sum_cube_param_eq_zero : ∑ i, (table2Row7Reciprocals i)⁻¹ ^ 3 = 0 := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  norm_num [table2Row7Reciprocals, Matrix.cons_val]

/-- The product identity behind Eq. (A5): summing the products over all erased carriers
reproduces the full product times the sum of the inverses, for any family of nonzero rational
carriers on a finite index type. -/
theorem sum_prod_erase_eq_prod_mul_sum_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℚ) (h : ∀ i, r i ≠ 0) :
    ∑ i, ∏ j ∈ Finset.univ.erase i, r j = (∏ j, r j) * ∑ i, (r i)⁻¹ := by
  have key : ∀ i : ι, ∏ j ∈ Finset.univ.erase i, r j = (∏ j, r j) * (r i)⁻¹ := by
    intro i
    have hmem : i ∈ Finset.univ := Finset.mem_univ i
    have hprod := Finset.prod_erase_mul Finset.univ r hmem
    rw [eq_mul_inv_iff_mul_eq₀ (h i), ← hprod, mul_comm]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.mul_sum]

/-- The first product form of Eq. (A5) for the length-seven row: the sum of the products over
all erased carriers equals the full product. -/
theorem table2Row7_sum_erase_prod_eq_prod :
    ∑ i, ∏ j ∈ Finset.univ.erase i, table2Row7Reciprocals j = ∏ j, table2Row7Reciprocals j := by
  rw [sum_prod_erase_eq_prod_mul_sum_inv _ table2Row7Reciprocals_nonzero,
    table2Row7_sum_param_eq_one, mul_one]

/-- The second product form of Eq. (A5) for the length-seven row: the cubes of the carriers
satisfy the corresponding cubic cancellation. -/
theorem table2Row7_sum_erase_cube_prod_eq_zero :
    ∑ i, ∏ j ∈ Finset.univ.erase i, (table2Row7Reciprocals j) ^ 3 = 0 := by
  have h3 : ∀ i, (table2Row7Reciprocals i) ^ 3 ≠ 0 := fun i => by
    exact pow_ne_zero 3 (table2Row7Reciprocals_nonzero i)
  have e : (∑ i, (table2Row7Reciprocals i ^ 3)⁻¹)
      = ∑ i, (table2Row7Reciprocals i)⁻¹ ^ 3 :=
    Finset.sum_congr rfl fun i _ => (inv_pow _ _).symm
  rw [sum_prod_erase_eq_prod_mul_sum_inv _ h3, e, table2Row7_sum_cube_param_eq_zero, mul_zero]

end Qatlib.Papers.DiracEquation16.HighOrder
