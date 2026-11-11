/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions

/-!
# Van Vleck bias and product overlap identities

The module proves algebraic bias formulas for a two-energy mixture and product identities for a
repeated overlap parameter. `vanVleck_bias_eq` isolates the energy gap, while
`qpe_ground_probability_abs` expresses the product of squared overlaps using the absolute
overlap. See [McCleanEtAl2014].

## Main statements

* `vanVleck_bias_eq`: factors the scalar energy bias.
* `qpe_ground_probability`: evaluates a constant product of squared overlaps.
* `qpe_ground_probability_lt_one`: gives a strict upper bound for a nontrivial overlap.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.VanVleck

open Finset

/-- The difference between the mixture energy and `N * Eg` factors as `N * (1 - Δ ^ 2) * (Ee -
Eg)`. -/
theorem vanVleck_bias_eq (N Δ Eg Ee : ℝ) :
    N * (Δ ^ 2 * Eg + (1 - Δ ^ 2) * Ee) - N * Eg
      = N * (1 - Δ ^ 2) * (Ee - Eg) := by
  ring

/-- When `ω = Ee - Eg`, the scalar mixture bias equals `N * (1 - Δ ^ 2) * ω`. -/
theorem vanVleck_bias_gap (N Δ Eg Ee ω : ℝ) (hω : ω = Ee - Eg) :
    N * (Δ ^ 2 * Eg + (1 - Δ ^ 2) * Ee) - N * Eg
      = N * (1 - Δ ^ 2) * ω := by
  rw [vanVleck_bias_eq, hω]

/-- The product of `N` copies of `Δ ^ 2` equals `Δ ^ (2 * N)`. This is the product-overlap
identity used in Eqs. (53)–(54) of [McCleanEtAl2014]. -/
theorem qpe_ground_probability (Δ : ℝ) (N : ℕ) :
    (∏ _i : Fin N, Δ ^ 2) = Δ ^ (2 * N) := by
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (pow_mul Δ 2 N).symm

/-- The absolute value of the product of `N` copies of `Δ` equals `|Δ| ^ N`. -/
theorem qpe_ground_amplitude (Δ : ℝ) (N : ℕ) :
    |∏ _i : Fin N, Δ| = |Δ| ^ N := by
  rw [Finset.abs_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The product of `N` copies of `Δ ^ 2` equals `|Δ| ^ (2 * N)`. -/
theorem qpe_ground_probability_abs (Δ : ℝ) (N : ℕ) :
    (∏ _i : Fin N, Δ ^ 2) = |Δ| ^ (2 * N) := by
  rw [qpe_ground_probability, ← abs_pow]
  exact (abs_of_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg Δ) N)).symm

/-- If `|Δ| < 1` and `N ≥ 1`, the product-overlap expression `|Δ| ^ (2 * N)` is strictly less
than one. -/
theorem qpe_ground_probability_lt_one (Δ : ℝ) (N : ℕ) (hΔ : |Δ| < 1)
    (hN : 1 ≤ N) :
    |Δ| ^ (2 * N) < 1 := by
  have h2N : 0 < 2 * N := by omega
  have h0 : 0 ≤ |Δ| := abs_nonneg Δ
  exact pow_lt_one₀ h0 hΔ (by omega)

end Qatlib.Papers.QChemistry14.ScalarModels.VanVleck
