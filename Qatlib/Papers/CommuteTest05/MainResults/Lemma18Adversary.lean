/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# A one-query adversary increment estimate

This module proves the finite-sum inequality controlling a one-query adversary increment in
Lemma 18 of [Itakura2005]. Bounds on the squared amplitudes over a finite relation imply a bound
on their paired products through the positive parameters `m` and `m'`.

## Main statements

* `lemma18_increment_bound`: Bounds the weighted relation sum by `2 * card R / sqrt(m * m')`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CommuteTest05.MainResults.Lemma18Adversary

/-- For a finite relation with nonnegative selected amplitudes and the stated squared-mass
bounds, `2 * ∑ p ∈ R, a p.1 (d p) * b p.2 (d p)` is at most `2 * R.card / sqrt(m * m')`.
This is the scalar increment estimate of [Itakura, Lemma 18][Itakura2005]. -/
theorem lemma18_increment_bound
    {ι X Y : Type*} (R : Finset (X × Y)) (d : X × Y → ι)
    (a : X → ι → ℝ) (b : Y → ι → ℝ) {m m' : ℝ}
    (hm : 0 < m) (hm' : 0 < m')
    (hnn : ∀ p ∈ R, 0 ≤ a p.1 (d p) ∧ 0 ≤ b p.2 (d p))
    (hmassX : ∑ p ∈ R, a p.1 (d p) ^ 2 ≤ (R.card : ℝ) / m)
    (hmassY : ∑ p ∈ R, b p.2 (d p) ^ 2 ≤ (R.card : ℝ) / m') :
    2 * (∑ p ∈ R, a p.1 (d p) * b p.2 (d p)) ≤
      2 / Real.sqrt (m * m') * (R.card : ℝ) := by
  set γ : ℝ := Real.sqrt (m / m') with hγdef
  have hmm'_pos : 0 < m / m' := div_pos hm hm'
  have hγpos : 0 < γ := Real.sqrt_pos.mpr hmm'_pos
  have hmmpos : 0 < m * m' := mul_pos hm hm'
  have hsqrtpos : 0 < Real.sqrt (m * m') := Real.sqrt_pos.mpr hmmpos

  have hstep : ∀ x y : ℝ, 2 * x * y ≤ γ * x ^ 2 + γ⁻¹ * y ^ 2 := by
    intro x y
    have h := two_mul_le_add_sq (Real.sqrt γ * x) (Real.sqrt γ⁻¹ * y)
    have h1 : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt (le_of_lt hγpos)
    have h2 : Real.sqrt γ⁻¹ ^ 2 = γ⁻¹ :=
      Real.sq_sqrt (le_of_lt (inv_pos.mpr hγpos))
    have h3 : Real.sqrt γ * Real.sqrt γ⁻¹ = 1 := by
      rw [← Real.sqrt_mul (le_of_lt hγpos) (γ⁻¹)]
      rw [mul_inv_cancel₀ (ne_of_gt hγpos), Real.sqrt_one]
    have hL : 2 * (Real.sqrt γ * x) * (Real.sqrt γ⁻¹ * y) = 2 * x * y := by
      calc 2 * (Real.sqrt γ * x) * (Real.sqrt γ⁻¹ * y)
          = 2 * x * y * (Real.sqrt γ * Real.sqrt γ⁻¹) := by ring
        _ = 2 * x * y := by rw [h3]; ring
    calc 2 * x * y = 2 * (Real.sqrt γ * x) * (Real.sqrt γ⁻¹ * y) := hL.symm
      _ ≤ (Real.sqrt γ * x) ^ 2 + (Real.sqrt γ⁻¹ * y) ^ 2 := h
      _ = γ * x ^ 2 + γ⁻¹ * y ^ 2 := by rw [mul_pow, mul_pow, h1, h2]
  have hsumle : 2 * (∑ p ∈ R, a p.1 (d p) * b p.2 (d p)) ≤
      ∑ p ∈ R, (γ * a p.1 (d p) ^ 2 + γ⁻¹ * b p.2 (d p) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have := hstep (a p.1 (d p)) (b p.2 (d p))
    simpa only [mul_assoc] using this
  have hsplit : ∑ p ∈ R, (γ * a p.1 (d p) ^ 2 + γ⁻¹ * b p.2 (d p) ^ 2)
      = γ * (∑ p ∈ R, a p.1 (d p) ^ 2) +
        γ⁻¹ * (∑ p ∈ R, b p.2 (d p) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hbounds : γ * (∑ p ∈ R, a p.1 (d p) ^ 2) +
        γ⁻¹ * (∑ p ∈ R, b p.2 (d p) ^ 2) ≤
      γ * ((R.card : ℝ) / m) + γ⁻¹ * ((R.card : ℝ) / m') := by
    refine add_le_add ?_ ?_
    · exact mul_le_mul_of_nonneg_left hmassX (le_of_lt hγpos)
    · exact mul_le_mul_of_nonneg_left hmassY (le_of_lt (inv_pos.mpr hγpos))
  have hkey : γ * Real.sqrt (m * m') = m := by
    have hsq : γ * Real.sqrt (m * m') = Real.sqrt ((m / m') * (m * m')) := by
      rw [← Real.sqrt_mul (le_of_lt hmm'_pos) (m * m')]
    rw [hsq]
    have hmul : (m / m') * (m * m') = m ^ 2 := by
      rw [div_mul_eq_mul_div]
      have hrw : m * (m * m') = m ^ 2 * m' := by ring
      rw [hrw, mul_div_cancel_right₀ _ (ne_of_gt hm')]
    rw [hmul, Real.sqrt_sq (le_of_lt hm)]
  have hkey2 : γ⁻¹ * Real.sqrt (m * m') = m' := by
    rw [hγdef, ← (Real.sqrt_inv (m / m'))]
    have hsq : Real.sqrt ((m / m')⁻¹) * Real.sqrt (m * m')
        = Real.sqrt ((m / m')⁻¹ * (m * m')) := by
      rw [← Real.sqrt_mul (le_of_lt (inv_pos.mpr hmm'_pos)) (m * m')]
    rw [hsq]
    have hmul : (m / m')⁻¹ * (m * m') = m' ^ 2 := by
      rw [inv_div, div_mul_eq_mul_div]
      have hrw : m' * (m * m') = m' ^ 2 * m := by ring
      rw [hrw, mul_div_cancel_right₀ _ (ne_of_gt hm)]
    rw [hmul, Real.sqrt_sq (le_of_lt hm')]
  have hγm : γ / m = 1 / Real.sqrt (m * m') := by
    rw [div_eq_div_iff (ne_of_gt hm) (ne_of_gt hsqrtpos)]
    simpa using hkey
  have hγm' : γ⁻¹ / m' = 1 / Real.sqrt (m * m') := by
    rw [div_eq_div_iff (ne_of_gt hm') (ne_of_gt hsqrtpos)]
    simpa using hkey2
  have hcombine : γ * ((R.card : ℝ) / m) + γ⁻¹ * ((R.card : ℝ) / m')
      = 2 / Real.sqrt (m * m') * (R.card : ℝ) := by
    have e1 : γ * ((R.card : ℝ) / m) = (γ / m) * (R.card : ℝ) := by ring
    have e2 : γ⁻¹ * ((R.card : ℝ) / m') = (γ⁻¹ / m') * (R.card : ℝ) := by ring
    rw [e1, e2, hγm, hγm']
    ring
  calc 2 * (∑ p ∈ R, a p.1 (d p) * b p.2 (d p))
      ≤ ∑ p ∈ R, (γ * a p.1 (d p) ^ 2 + γ⁻¹ * b p.2 (d p) ^ 2) := hsumle
    _ = γ * (∑ p ∈ R, a p.1 (d p) ^ 2) +
        γ⁻¹ * (∑ p ∈ R, b p.2 (d p) ^ 2) := hsplit
    _ ≤ γ * ((R.card : ℝ) / m) + γ⁻¹ * ((R.card : ℝ) / m') := hbounds
    _ = 2 / Real.sqrt (m * m') * (R.card : ℝ) := hcombine

end Qatlib.Papers.CommuteTest05.MainResults.Lemma18Adversary
