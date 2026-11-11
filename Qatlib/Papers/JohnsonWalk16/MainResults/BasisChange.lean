/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Leading matrix couplings for Johnson-graph search

This module defines the explicit leading matrices `H0old`, `H0new`, and `HprimeLead` appearing
in the perturbative discussion of Johnson-graph search in [Wong2016]. It compares their
specified coupling entries and proves normalization of the displayed vector `rvec` for `n ≥ 6`.

## Main statements

* `single_column_normalized`: proves that `rvec` is a unit vector with zero marked coordinate.
* `change_of_basis_enables_perturbation`: combines the vanishing old coupling with the two
  nonzero displayed couplings.

## References

* [Wong, 2016][Wong2016]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.JohnsonWalk16.MainResults.BasisChange

/-- The diagonal four-dimensional leading matrix with entries `-1`, `-γ * n`, `-γ * (2 * n)`,
and `-γ * (3 * n)`. -/
def H0old (γ n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ -1, 0, 0, 0;
      0, -(γ * n), 0, 0;
      0, 0, -(γ * (2 * n)), 0;
      0, 0, 0, -(γ * (3 * n)) ]

/-- Every off-diagonal entry of `H0old γ n` vanishes. -/
theorem old_leading_diagonal (γ n : ℝ) :
    ∀ i j : Fin 4, i ≠ j → H0old γ n i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [H0old]

/-- The entry of `H0old γ n` from coordinate zero to coordinate three vanishes. -/
theorem old_leading_d0_d3 (γ n : ℝ) : H0old γ n 0 3 = 0 := by
  simp [H0old]

/-- The explicit four-dimensional leading matrix in the new coordinates, including the coupling
`-γ * sqrt (3 * n)` between coordinates zero and three. -/
def H0new (γ n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ -1, 0, 0, -(γ * Real.sqrt (3 * n));
      0, -(γ * (3 * n - 9)), 0, 0;
      0, 0, -(γ * (2 * n - 17)), -(γ * (-2 * Real.sqrt (2 * n)));
      -(γ * Real.sqrt (3 * n)), 0, -(γ * (-2 * Real.sqrt (2 * n))), -(γ * (n - 2)) ]

/-- The coordinate-zero to coordinate-three entry of `H0new γ n` equals `-(γ * sqrt (3 * n))`. -/
theorem new_leading_d0_r_double_prime (γ n : ℝ) :
    H0new γ n 0 3 = -(γ * Real.sqrt (3 * n)) := by
  simp [H0new]

/-- For nonzero `γ` and positive `n`, the coordinate-zero to coordinate-three entry of `H0new γ
n` is nonzero. -/
theorem new_leading_d0_r_double_prime_ne_zero {γ n : ℝ} (hγ : γ ≠ 0) (hn : 0 < n) :
    H0new γ n 0 3 ≠ 0 := by
  rw [new_leading_d0_r_double_prime]
  have h3 : 0 < Real.sqrt (3 * n) := Real.sqrt_pos.2 (by positivity)
  exact neg_ne_zero.mpr (mul_ne_zero hγ h3.ne')

/-- The explicit truncated four-dimensional matrix containing the displayed inverse-square-root
corrections to the new-coordinate couplings. -/
def HprimeLead (γ n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ -1, -(γ * (3 * Real.sqrt 6 / Real.sqrt n)), 0,
        -(γ * (Real.sqrt (3 * n) - 3 * Real.sqrt 3 / (2 * Real.sqrt n)));
      -(γ * (3 * Real.sqrt 6 / Real.sqrt n)), -(γ * (3 * n - 9)), 0, 0;
      0, 0, -(γ * (2 * n - 17)),
        -(γ * (-(2 * Real.sqrt (2 * n)) + 13 * Real.sqrt 2 / Real.sqrt n));
      -(γ * (Real.sqrt (3 * n) - 3 * Real.sqrt 3 / (2 * Real.sqrt n))), 0,
        -(γ * (-(2 * Real.sqrt (2 * n)) + 13 * Real.sqrt 2 / Real.sqrt n)),
        -(γ * (n - 2)) ]

/-- The coordinate-zero to coordinate-one entry of `HprimeLead γ n` equals `-(γ * (3 * sqrt 6 /
sqrt n))`. -/
theorem perturbation_d0_r_coupling (γ n : ℝ) :
    HprimeLead γ n 0 1 = -(γ * (3 * Real.sqrt 6 / Real.sqrt n)) := by
  simp [HprimeLead]

/-- For nonzero `γ` and positive `n`, the coordinate-zero to coordinate-one entry of `HprimeLead
γ n` is nonzero. -/
theorem perturbation_d0_r_coupling_ne_zero {γ n : ℝ} (hγ : γ ≠ 0) (hn : 0 < n) :
    HprimeLead γ n 0 1 ≠ 0 := by
  rw [perturbation_d0_r_coupling]
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hn' : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn
  have hratio : 0 < 3 * Real.sqrt 6 / Real.sqrt n := by positivity
  exact neg_ne_zero.mpr (mul_ne_zero hγ hratio.ne')

/-- The displayed four-coordinate vector with first entry zero and remaining entries determined
by the square-root formulas in `n`. -/
def rvec (n : ℝ) : Fin 4 → ℝ :=
  ![0, Real.sqrt (18 / (n ^ 2 + 2)),
    Real.sqrt (18 / (n ^ 2 + 2)) * Real.sqrt ((n - 4) / 2),
    Real.sqrt (18 / (n ^ 2 + 2)) * Real.sqrt ((n - 4) * (n - 5) / 18)]

/-- The first coordinate of `rvec n` equals zero. -/
theorem rvec_d0_component (n : ℝ) : rvec n 0 = 0 := by
  simp [rvec]

/-- For `n ≥ 6`, the sum of the squared coordinates of `rvec n` equals one. -/
theorem rvec_normalized {n : ℝ} (hn : 6 ≤ n) :
    ∑ i : Fin 4, rvec n i ^ 2 = 1 := by
  have h4 : (0 : ℝ) ≤ n - 4 := by linarith
  have h5 : (0 : ℝ) ≤ n - 5 := by linarith
  have hden : (n : ℝ) ^ 2 + 2 ≠ 0 := by positivity
  simp [rvec, Fin.sum_univ_four, mul_pow, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 18),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt h4,
    Real.sq_sqrt (mul_nonneg h4 h5),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n ^ 2 + 2)]
  field_simp [hden]
  ring

/-- For `n ≥ 6`, `rvec n` has first coordinate zero and squared coordinate sum one. -/
theorem single_column_normalized {n : ℝ} (hn : 6 ≤ n) :
    rvec n 0 = 0 ∧ ∑ i : Fin 4, rvec n i ^ 2 = 1 :=
  ⟨rvec_d0_component n, rvec_normalized hn⟩

/-- For nonzero `γ` and `n ≥ 6`, the old matrix's `(0, 3)` entry vanishes while the new matrix's
`(0, 3)` entry and the corrected matrix's `(0, 1)` entry are nonzero, as in the coupling
comparison of [Wong2016]. -/
theorem change_of_basis_enables_perturbation {γ n : ℝ} (hγ : γ ≠ 0) (hn : 6 ≤ n) :
    H0old γ n 0 3 = 0 ∧ H0new γ n 0 3 ≠ 0 ∧ HprimeLead γ n 0 1 ≠ 0 :=
  ⟨old_leading_d0_d3 γ n, new_leading_d0_r_double_prime_ne_zero hγ (by linarith),
    perturbation_d0_r_coupling_ne_zero hγ (by linarith)⟩

end Qatlib.Papers.JohnsonWalk16.MainResults.BasisChange
