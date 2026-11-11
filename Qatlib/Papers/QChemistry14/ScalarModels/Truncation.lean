/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions

/-!
# Scalar truncation budgets

The module bounds finite sums of removed real coefficients by their absolute coefficient mass.
It combines a uniform coefficient threshold with cardinality bounds to obtain an ε budget for
the scalar truncation estimates in quantum chemistry. See [McCleanEtAl2014].

## Main statements

* `eigenvalue_shift_le_removed_sum`: bounds the absolute sum by the sum of absolute values.
* `eigenvalue_shift_le_epsilon`: uses the threshold ε divided by the removed count.
* `removed_sum_le_epsilon_of_m4`: uses an M⁴ upper bound on the removed count.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.Truncation

open Finset
open scoped BigOperators

variable {ι : Type*}

/-- The absolute value of a finite sum of removed real coefficients is at most the sum of their
absolute values. This scalar triangle inequality supports the truncation estimate in Eqs.
(22)–(24) of [McCleanEtAl2014]. -/
theorem eigenvalue_shift_le_removed_sum (h : ι → ℝ) (Hrem : Finset ι) :
    |∑ i ∈ Hrem, h i| ≤ ∑ i ∈ Hrem, |h i| :=
  Finset.abs_sum_le_sum_abs h Hrem

/-- If every removed coefficient has absolute value less than `δ`, their total absolute mass is
at most the removed count times `δ`. -/
theorem removed_sum_le_card_mul (h : ι → ℝ) (Hrem : Finset ι) {δ : ℝ}
    (hsmall : ∀ i ∈ Hrem, |h i| < δ) :
    ∑ i ∈ Hrem, |h i| ≤ (Hrem.card : ℝ) * δ := by
  have hstep : ∑ i ∈ Hrem, |h i| ≤ ∑ _i ∈ Hrem, δ := by
    apply Finset.sum_le_sum
    intro i hi
    exact le_of_lt (hsmall i hi)
  calc
    ∑ i ∈ Hrem, |h i| ≤ ∑ _i ∈ Hrem, δ := hstep
    _ = (Hrem.card : ℝ) * δ := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- For a nonempty removed set, a threshold at most `ε / Hrem.card` bounds the absolute
coefficient sum by `ε`. -/
theorem eigenvalue_shift_le_epsilon (h : ι → ℝ) (Hrem : Finset ι) {δ ε : ℝ}
    (hsmall : ∀ i ∈ Hrem, |h i| < δ) (hcard : 0 < Hrem.card)
    (hδeps : δ ≤ ε / (Hrem.card : ℝ)) :
    |∑ i ∈ Hrem, h i| ≤ ε := by
  have h1 := eigenvalue_shift_le_removed_sum h Hrem
  have h2 := removed_sum_le_card_mul h Hrem hsmall
  have hc : (0 : ℝ) < (Hrem.card : ℝ) := by exact_mod_cast hcard
  have hmul : (Hrem.card : ℝ) * δ ≤ ε := by
    calc
      (Hrem.card : ℝ) * δ ≤ (Hrem.card : ℝ) * (ε / (Hrem.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hδeps (le_of_lt hc)
      _ = ε := by field_simp
  linarith

/-- If at most `M ^ 4` coefficients are removed, `M` is positive, and the nonnegative threshold
is at most `ε / (M : ℝ) ^ 4`, the removed absolute mass is at most `ε`. -/
theorem removed_sum_le_epsilon_of_m4 (h : ι → ℝ) (Hrem : Finset ι) {δ ε : ℝ} {M : ℕ}
    (hsmall : ∀ i ∈ Hrem, |h i| < δ) (hcard : Hrem.card ≤ M ^ 4)
    (hδ0 : 0 ≤ δ) (hδM : δ ≤ ε / ((M : ℝ) ^ 4)) (hM : 0 < M) :
    ∑ i ∈ Hrem, |h i| ≤ ε := by
  have h2 := removed_sum_le_card_mul h Hrem hsmall
  have hcardR : (Hrem.card : ℝ) ≤ (M : ℝ) ^ 4 := by exact_mod_cast hcard
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) ^ 4 := by positivity
  have hstep1 : (Hrem.card : ℝ) * δ ≤ (M : ℝ) ^ 4 * δ :=
    mul_le_mul_of_nonneg_right hcardR hδ0
  have hstep2 : (M : ℝ) ^ 4 * δ ≤ (M : ℝ) ^ 4 * (ε / (M : ℝ) ^ 4) :=
    mul_le_mul_of_nonneg_left hδM (le_of_lt hMpos)
  have heq : (M : ℝ) ^ 4 * (ε / (M : ℝ) ^ 4) = ε := by field_simp
  linarith

end Qatlib.Papers.QChemistry14.ScalarModels.Truncation
