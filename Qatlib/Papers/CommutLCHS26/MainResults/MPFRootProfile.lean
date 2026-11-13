/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.CommutatorProducts
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Root scales for commutator profile products

This module defines `rootCoefficient` from positive commutator-profile products and takes their
supremum over the order-dependent `rootSet` to obtain `mu`. The scale is nonnegative and bounded
by `boundingScale` for positive order, and it bounds every relevant raw product.

A radius satisfying rμ ≤ 1 then supplies the odd-coefficient control required by the
multi-product error expansions associated with [AftabAnTrivisa2026].

## Main statements

* `rootSet_bounded`: bounds the set defining the root scale.
* `rawProduct_le_mu`: controls profile products by powers of μ.
* `oddControl`: derives odd-coefficient control from a scaled-radius bound.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFRootProfile

open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal
open CommutatorGrowth CommutatorProducts BCHControlled
open Qatlib.Concepts.TrotterFormula.GeneralOrder

variable {I : Type} [Fintype I]

/-- The nonnegative real (j + l)-th root of the positive commutator-profile product, using the
reciprocal exponent. -/
def rootCoefficient (xs : List (Matrix I I ℂ)) (j l : ℕ) : ℝ :=
  (positiveProduct xs j l) ^ (((j + l : ℕ) : ℝ)⁻¹)

/-- The set of root coefficients for even j ≥ 2m and depths 1 ≤ l ≤ m. -/
def rootSet (xs : List (Matrix I I ℂ)) (m : ℕ) : Set ℝ :=
  {z | ∃ j l : ℕ, Even j ∧ 2 * m ≤ j ∧ 1 ≤ l ∧ l ≤ m ∧ z = rootCoefficient xs j l}

/-- The supremum of the order-dependent set of commutator root coefficients. -/
def mu (xs : List (Matrix I I ℂ)) (m : ℕ) : ℝ := sSup (rootSet xs m)

/-- Every commutator root coefficient is nonnegative. -/
theorem rootCoefficient_nonneg (xs : List (Matrix I I ℂ)) (j l : ℕ) :
    0 ≤ rootCoefficient xs j l := Real.rpow_nonneg (positiveProduct_nonneg xs j l) _

/-- For j + l > 0, raising the root coefficient to power j + l recovers the positive product. -/
theorem rootCoefficient_pow (xs : List (Matrix I I ℂ)) (j l : ℕ) (hd : 0 < j + l) :
    rootCoefficient xs j l ^ (j + l) = positiveProduct xs j l :=
  Real.rpow_inv_natCast_pow (positiveProduct_nonneg xs j l) (by omega)

/-- The set of root coefficients is nonempty for positive m. -/
theorem rootSet_nonempty (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m) :
    (rootSet xs m).Nonempty := by
  refine ⟨rootCoefficient xs (2 * m) m, 2 * m, m, even_two_mul m, le_refl _, ?_, le_refl _, rfl⟩
  omega

variable [DecidableEq I]

/-- Every member of the root set is at most the bounding scale. -/
theorem rootSet_le_scale (xs : List (Matrix I I ℂ)) (m : ℕ) :
    ∀ z ∈ rootSet xs m, z ≤ boundingScale xs := by
  rintro z ⟨j, l, heven, hj, hl, hlm, rfl⟩
  obtain ⟨a, ha⟩ := heven
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = 2 * (n + l) := ⟨a - l, by omega⟩
  unfold rootCoefficient
  rw [positiveProduct_eq_raw]
  apply (Real.rpow_inv_le_iff_of_pos (rawProduct_nonneg xs l n)
    (boundingScale_pos xs).le (show (0 : ℝ) < ((2 * (n + l) + l : ℕ) : ℝ) by positivity)).mpr
  rw [Real.rpow_natCast]
  have h := rawProduct_le_scale xs l n
  convert! h using 1
  congr 1
  omega

/-- The set of root coefficients is bounded above. -/
theorem rootSet_bounded (xs : List (Matrix I I ℂ)) (m : ℕ) : BddAbove (rootSet xs m) :=
  ⟨boundingScale xs, rootSet_le_scale xs m⟩

/-- The root scale μ is nonnegative for positive m. -/
theorem mu_nonneg (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m) : 0 ≤ mu xs m := by
  have hw : rootCoefficient xs (2 * m) m ∈ rootSet xs m := by
    exact ⟨2 * m, m, even_two_mul m, le_refl _, by omega, le_refl _, rfl⟩
  exact (rootCoefficient_nonneg xs (2 * m) m).trans (le_csSup (rootSet_bounded xs m) hw)

/-- For positive m, the root scale μ is at most the bounding scale. -/
theorem mu_le_scale (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m) :
    mu xs m ≤ boundingScale xs :=
  csSup_le (rootSet_nonempty xs m hm) (rootSet_le_scale xs m)

/-- For 1 ≤ l ≤ m and n + l ≥ m, the raw profile product is at most μ^(2n + 3l). -/
theorem rawProduct_le_mu (xs : List (Matrix I I ℂ)) (m l n : ℕ)
    (hl : 1 ≤ l) (hlm : l ≤ m) (hn : m ≤ n + l) :
    rawProduct xs l n ≤ mu xs m ^ (2 * n + 3 * l) := by
  have hw : rootCoefficient xs (2 * (n + l)) l ∈ rootSet xs m := by
    refine ⟨2 * (n + l), l, even_two_mul _, ?_, hl, hlm, rfl⟩
    omega
  have hroot := le_csSup (rootSet_bounded xs m) hw
  calc
    _ = positiveProduct xs (2 * (n + l)) l := (positiveProduct_eq_raw xs l n).symm
    _ = rootCoefficient xs (2 * (n + l)) l ^ (2 * (n + l) + l) :=
      (rootCoefficient_pow xs _ l (by omega)).symm
    _ ≤ mu xs m ^ (2 * (n + l) + l) :=
      pow_le_pow_left₀ (rootCoefficient_nonneg xs _ l) hroot _
    _ = _ := by congr 1; omega

omit [DecidableEq I] in

/-- At depth one, the raw product equals the commutator profile of order 2n + 3. -/
theorem rawProduct_one (xs : List (Matrix I I ℂ)) (n : ℕ) :
    rawProduct xs 1 n = pfCommAlphaSelf xs (2 * n + 3) := by
  have hf : Finset.finAntidiagonal 1 n = {(fun _ : Fin 1 => n)} := by
    ext v
    simp only [Finset.mem_finAntidiagonal, Fin.sum_univ_one, Finset.mem_singleton]
    constructor
    · intro hv
      funext i
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
      exact hv
    · intro hv
      rw [hv]
  rw [rawProduct, hf, Finset.sum_singleton, Fin.prod_univ_one]

/-- For positive m, a nonnegative radius satisfying rμ ≤ 1 gives odd-coefficient control with
cutoff 2m + 1. -/
theorem oddControl (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m)
    (r : ℝ≥0) (hr : (r : ℝ) * mu xs m ≤ 1) : OddControl xs r (2 * m + 1) := by
  intro k hk ho
  obtain ⟨a, ha⟩ := ho
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 2 * n + 3 := ⟨a - 1, by omega⟩
  have hα : pfCommAlphaSelf xs (2 * n + 3) ≤ mu xs m ^ (2 * n + 3) := by
    have h := rawProduct_le_mu xs m 1 n (by decide) (by omega) (by omega)
    rw [rawProduct_one] at h
    simpa only [mul_one] using! h
  calc
    _ ≤ (r : ℝ) ^ (2 * n + 3) * mu xs m ^ (2 * n + 3) :=
      mul_le_mul_of_nonneg_left hα (pow_nonneg r.2 _)
    _ = ((r : ℝ) * mu xs m) ^ (2 * n + 3) := (mul_pow _ _ _).symm
    _ ≤ 1 := pow_le_one₀ (mul_nonneg r.2 (mu_nonneg xs m hm)) hr

end Qatlib.Papers.CommutLCHS26.MainResults.MPFRootProfile
