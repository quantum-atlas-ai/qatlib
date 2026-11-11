/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Level shifts and second order spectral estimates

`levelShifted` lowers one selected diagonal value, and the associated lemmas describe its effect
on values, degeneracy, and the total sum. `perturbedEigenvalue` adds a second order correction
formed from squared off diagonal entries and diagonal differences.

The module proves elementary properties of this estimate, including its value for a zero off
diagonal row and a lower bound when all relevant diagonal differences are nonnegative. The
scalar setup count `N + (N - 1)` is compared with the cubic count `N^3`. See [BaskaranEtAl2023].

## Main statements

* `levelShifted_breaks_degeneracy`: If distinct indices have equal diagonal values, shifting one
  by `m*xi` with positive `xi` and `m ≥ 1` makes their shifted values different.
* `diagonal_le_perturbedEigenvalue`: If every relevant diagonal difference is nonnegative, the
  spectral estimate is at least the selected diagonal entry.
* `perturbedSetupCost_lt_classical`: For `N ≥ 2`, the setup count `N + (N - 1)` is strictly less
  than the cubic count `N^3`.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HHLManyBody22.PerturbEstimate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal function obtained by replacing `d i0` with `d i0 - m*xi`. -/
def levelShifted (d : ι → ℝ) (i0 : ι) (m : ℕ) (xi : ℝ) : ι → ℝ :=
  Function.update d i0 (d i0 - (m : ℝ) * xi)

omit [Fintype ι] in

/-- At the selected index, the shifted value is `d i0 - m*xi`. -/
theorem levelShifted_self (d : ι → ℝ) (i0 : ι) (m : ℕ) (xi : ℝ) :
    levelShifted d i0 m xi i0 = d i0 - (m : ℝ) * xi := by
  simp [levelShifted]

omit [Fintype ι] in

/-- At every index different from `i0`, the level shift leaves the diagonal value unchanged. -/
theorem levelShifted_apply_of_ne {d : ι → ℝ} {i0 j : ι} (m : ℕ) (xi : ℝ)
    (hj : j ≠ i0) : levelShifted d i0 m xi j = d j := by
  simp [levelShifted, hj]

omit [Fintype ι] in

/-- For positive `xi` and `m ≥ 1`, the selected shifted value is strictly smaller than its
original value. -/
theorem levelShifted_lt_self (d : ι → ℝ) (i0 : ι) (m : ℕ) (xi : ℝ)
    (hxi : 0 < xi) (hm : 1 ≤ m) : levelShifted d i0 m xi i0 < d i0 := by
  rw [levelShifted_self]
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  nlinarith

omit [Fintype ι] in

/-- For positive `xi` and `m ≥ 1`, the selected shifted value differs from its original value. -/
theorem levelShifted_ne_self (d : ι → ℝ) (i0 : ι) (m : ℕ) (xi : ℝ)
    (hxi : 0 < xi) (hm : 1 ≤ m) : levelShifted d i0 m xi i0 ≠ d i0 :=
  ne_of_lt (levelShifted_lt_self d i0 m xi hxi hm)

omit [Fintype ι] in

/-- If distinct indices have equal diagonal values, shifting one by `m*xi` with positive `xi`
and `m ≥ 1` makes their shifted values different. -/
theorem levelShifted_breaks_degeneracy {d : ι → ℝ} {i j : ι} (m : ℕ) (xi : ℝ)
    (hij : i ≠ j) (hdeg : d i = d j) (hxi : 0 < xi) (hm : 1 ≤ m) :
    levelShifted d i m xi i ≠ levelShifted d i m xi j := by
  rw [levelShifted_self, levelShifted_apply_of_ne m xi hij.symm, ← hdeg]
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlt : d i - (m : ℝ) * xi < d i := by nlinarith
  exact ne_of_lt hlt

/-- The sum of all shifted diagonal values is the original sum minus `m*xi`. -/
theorem sum_levelShifted (d : ι → ℝ) (i0 : ι) (m : ℕ) (xi : ℝ) :
    (∑ j, levelShifted d i0 m xi j) = (∑ j, d j) - (m : ℝ) * xi := by
  have hsplit : (∑ j, levelShifted d i0 m xi j)
      = (∑ j ∈ Finset.univ.erase i0, levelShifted d i0 m xi j)
        + levelShifted d i0 m xi i0 :=
    (Finset.sum_erase_add (Finset.univ) (levelShifted d i0 m xi)
      (Finset.mem_univ i0)).symm
  have hcongr : (∑ j ∈ Finset.univ.erase i0, levelShifted d i0 m xi j)
      = (∑ j ∈ Finset.univ.erase i0, d j) :=
    Finset.sum_congr rfl (fun j hj =>
      levelShifted_apply_of_ne m xi (Finset.ne_of_mem_erase hj))
  have hsum := Finset.sum_erase_add (Finset.univ) d (Finset.mem_univ i0)
  rw [hsplit, hcongr, levelShifted_self]
  linarith

/-- The correction term `(b i j)^2 / (b i i - b j j)`. -/
def perturbationTerm (b : ι → ι → ℝ) (i j : ι) : ℝ :=
  (b i j) ^ 2 / (b i i - b j j)

/-- The diagonal value `b i i` plus the sum of correction terms over indices different from `i`. -/
def perturbedEigenvalue (b : ι → ι → ℝ) (i : ι) : ℝ :=
  b i i + ∑ j ∈ Finset.univ.erase i, perturbationTerm b i j

/-- Expands the spectral estimate as the diagonal entry plus the sum of squared off diagonal
entries divided by diagonal differences. -/
theorem perturbedEigenvalue_def (b : ι → ι → ℝ) (i : ι) :
    perturbedEigenvalue b i =
      b i i + ∑ j ∈ Finset.univ.erase i, (b i j) ^ 2 / (b i i - b j j) := rfl

/-- If all off diagonal entries in row `i` are zero, the spectral estimate equals `b i i`. -/
theorem perturbedEigenvalue_of_offdiag_zero (b : ι → ι → ℝ) (i : ι)
    (h : ∀ j, j ≠ i → b i j = 0) : perturbedEigenvalue b i = b i i := by
  unfold perturbedEigenvalue perturbationTerm
  have hzero : (∑ j ∈ Finset.univ.erase i, (b i j) ^ 2 / (b i i - b j j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j (Finset.ne_of_mem_erase hj)]
    simp
  rw [hzero, add_zero]

/-- The set of indices different from `i` has cardinality `Fintype.card ι - 1`. See
[BaskaranEtAl2023]. -/
theorem perturbation_num_terms (i : ι) :
    (Finset.univ.erase i).card = Fintype.card ι - 1 :=
  Finset.card_erase_of_mem (Finset.mem_univ i)

/-- If all relevant diagonal differences are nonnegative, the sum of correction terms is
nonnegative. -/
theorem perturbation_sum_nonneg (b : ι → ι → ℝ) (i : ι)
    (h : ∀ j ∈ Finset.univ.erase i, 0 ≤ b i i - b j j) :
    0 ≤ ∑ j ∈ Finset.univ.erase i, perturbationTerm b i j := by
  apply Finset.sum_nonneg
  intro j hj
  unfold perturbationTerm
  exact div_nonneg (sq_nonneg _) (h j hj)

/-- If every relevant diagonal difference is nonnegative, the spectral estimate is at least the
selected diagonal entry. -/
theorem diagonal_le_perturbedEigenvalue (b : ι → ι → ℝ) (i : ι)
    (h : ∀ j ∈ Finset.univ.erase i, 0 ≤ b i i - b j j) :
    b i i ≤ perturbedEigenvalue b i := by
  unfold perturbedEigenvalue
  linarith [perturbation_sum_nonneg b i h]

/-- The natural number setup count `N + (N - 1)`. -/
def perturbedSetupCost (N : ℕ) : ℕ := N + (N - 1)

/-- The natural number cubic diagonalization count `N^3`. -/
def classicalDiagonalizationCost (N : ℕ) : ℕ := N ^ 3

/-- For `N ≥ 2`, the setup count `N + (N - 1)` is strictly less than the cubic count `N^3`. -/
theorem perturbedSetupCost_lt_classical (N : ℕ) (hN : 2 ≤ N) :
    perturbedSetupCost N < classicalDiagonalizationCost N := by
  unfold perturbedSetupCost classicalDiagonalizationCost
  have hN0 : 0 < N := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hN
  have hN1 : 1 ≤ N := Nat.le_trans (by norm_num : 1 ≤ 2) hN
  have h2 : N + (N - 1) < 2 * N := by
    have hlt : N - 1 < N := Nat.sub_lt hN0 (by norm_num : 0 < 1)
    have := Nat.add_lt_add_left hlt N
    simpa [two_mul] using this
  have h3 : 2 * N ≤ N * (N * N) := by
    have hNN : N ≤ N * N := by
      calc N = N * 1 := (Nat.mul_one N).symm
        _ ≤ N * N := Nat.mul_le_mul_left N hN1
    calc 2 * N ≤ N * N := Nat.mul_le_mul_right N hN
      _ ≤ N * (N * N) := Nat.mul_le_mul_left N hNN
  calc N + (N - 1) < 2 * N := h2
    _ ≤ N * (N * N) := h3
    _ = N ^ 3 := by ring

/-- For natural `N ≥ 2`, its real value is strictly less than its cube. -/
theorem perturbedCost_lt_classical_real (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) < (N : ℝ) ^ 3 := by
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx0 : 0 < (N : ℝ) := by linarith
  have hx1 : (1 : ℝ) < (N : ℝ) := by linarith
  have hx2 : 1 < (N : ℝ) ^ 2 := by
    have hpos1 : 0 < (N : ℝ) - 1 := by linarith
    have hpos2 : 0 < (N : ℝ) + 1 := by linarith
    have hprod : 0 < ((N : ℝ) - 1) * ((N : ℝ) + 1) := mul_pos hpos1 hpos2
    nlinarith
  calc (N : ℝ) = (N : ℝ) * 1 := (mul_one _).symm
    _ < (N : ℝ) * (N : ℝ) ^ 2 := mul_lt_mul_of_pos_left hx2 hx0
    _ = (N : ℝ) ^ 3 := by ring

end Qatlib.Papers.HHLManyBody22.PerturbEstimate
