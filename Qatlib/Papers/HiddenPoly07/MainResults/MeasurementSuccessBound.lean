/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Measurement sums from good-set cardinalities

This module defines the minimum good output cardinality `WgoodMin` and the minimum squared
cardinality `WgoodSq`, assigning zero when the index set is empty. It proves lower bounds on
normalized sums of squared square-root multiplicities, including the cardinality estimate
`lemma31_success_lower_bound`.

The development follows [DeckerDraismaWocjan2009].

## Main statements

* `lemma31_success_lower_bound`: Bounds the normalized square-root sum below by d^(−3n) times
  the cardinality of `X` times `WgoodMin X W` squared, assuming every selected multiplicity is
  positive.
* `lemma31_min_square_bound`: Bounds the normalized square-root sum below by d^(−3n) times the
  cardinality of `X` times `WgoodSq X W`, assuming every selected multiplicity is positive.
* `success_probability_constant_of_good_counts`: If `X` and the minimum good output cardinality
  are each at least d^n/2^n and selected multiplicities are positive, the normalized square-root
  sum is at least 2^(−3n).

## References

* [Decker et al., 2009][DeckerDraismaWocjan2009]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HiddenPoly07.MainResults

open scoped BigOperators

/-- The minimum cardinality of `W x` over `x` in `X`, with value zero when `X` is empty. -/
def WgoodMin {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (X : Finset (Fin n → F))
    (W : (Fin n → F) → Finset (Fin n → F)) : ℕ :=
  if h : X.Nonempty then
    (X.image fun x => (W x).card).min' (h.image fun x => (W x).card)
  else 0

/-- The minimum of the squared cardinalities of `W x` over `x` in `X`, with value zero when `X`
is empty. -/
def WgoodSq {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (X : Finset (Fin n → F))
    (W : (Fin n → F) → Finset (Fin n → F)) : ℕ :=
  if h : X.Nonempty then
    (X.image fun x => (W x).card ^ 2).min' (h.image fun x => (W x).card ^ 2)
  else 0

/-- For an index `x` in `X`, the minimum good output cardinality is at most the cardinality of
`W x`. -/
theorem WgoodMin_le {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (X : Finset (Fin n → F)) (W : (Fin n → F) → Finset (Fin n → F)) {x : Fin n → F}
    (hx : x ∈ X) : WgoodMin X W ≤ (W x).card := by
  unfold WgoodMin
  rw [dif_pos ⟨x, hx⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)

/-- For an index `x` in `X`, the minimum squared good output cardinality is at most the squared
cardinality of `W x`. -/
theorem WgoodSq_le {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (X : Finset (Fin n → F)) (W : (Fin n → F) → Finset (Fin n → F)) {x : Fin n → F}
    (hx : x ∈ X) : WgoodSq X W ≤ (W x).card ^ 2 := by
  unfold WgoodSq
  rw [dif_pos ⟨x, hx⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)

/-- If every selected multiplicity is at least one, the square of the output-set cardinality is
at most the square of the sum of square roots of those multiplicities ([Lemma
3.1][DeckerDraismaWocjan2009]). -/
theorem goodBlock_success_le {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (Wx : Finset (Fin n → F)) (eta : (Fin n → F) → ℕ)
    (hη : ∀ w ∈ Wx, 1 ≤ eta w) :
    ((Wx.card : ℝ)) ^ 2 ≤ (∑ w ∈ Wx, Real.sqrt (eta w)) ^ 2 := by
  have hsum1 : ((Wx.card : ℝ)) ≤ ∑ w ∈ Wx, Real.sqrt (eta w) := by
    have hcard_eq : ((Wx.card : ℝ)) = ∑ _w ∈ Wx, (1 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard_eq]
    exact Finset.sum_le_sum fun w hw => Real.one_le_sqrt.mpr (by exact_mod_cast hη w hw)
  exact pow_le_pow_left₀ (by positivity) hsum1 2

/-- Bounds the normalized square-root sum below by d^(−3n) times the cardinality of `X` times
`WgoodMin X W` squared, assuming every selected multiplicity is positive ([Lemma
3.1][DeckerDraismaWocjan2009]). -/
theorem lemma31_success_lower_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (X : Finset (Fin n → F)) (W : (Fin n → F) → Finset (Fin n → F))
    (eta : (Fin n → F) → (Fin n → F) → ℕ)
    (hη : ∀ x ∈ X, ∀ w ∈ W x, 1 ≤ eta x w) :
    ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ * ((X.card : ℝ) * (WgoodMin X W : ℝ) ^ 2)
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ∑ x ∈ X, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
  classical
  have hper : ∀ x ∈ X, ((WgoodMin X W : ℝ)) ^ 2 ≤ (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
    intro x hx
    have hcard : (WgoodMin X W : ℝ) ≤ ((W x).card : ℝ) := by
      exact_mod_cast WgoodMin_le X W hx
    exact (pow_le_pow_left₀ (by positivity) hcard 2).trans
      (goodBlock_success_le (W x) (eta x) (hη x hx))
  have hsum : ((X.card : ℝ) * (WgoodMin X W : ℝ) ^ 2)
      ≤ ∑ x ∈ X, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
    have := Finset.sum_le_sum hper
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have hnonneg : (0 : ℝ) ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hsum hnonneg

/-- Bounds the normalized square-root sum below by d^(−3n) times the cardinality of `X` times
`WgoodSq X W`, assuming every selected multiplicity is positive ([Lemma
3.1][DeckerDraismaWocjan2009]). -/
theorem lemma31_min_square_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (X : Finset (Fin n → F)) (W : (Fin n → F) → Finset (Fin n → F))
    (eta : (Fin n → F) → (Fin n → F) → ℕ)
    (hη : ∀ x ∈ X, ∀ w ∈ W x, 1 ≤ eta x w) :
    ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ * ((X.card : ℝ) * (WgoodSq X W : ℝ))
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ∑ x ∈ X, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
  classical
  have hper : ∀ x ∈ X, ((WgoodSq X W : ℝ)) ≤ (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
    intro x hx
    have hcard : (WgoodSq X W : ℝ) ≤ (W x).card ^ 2 := by
      have := WgoodSq_le X W hx
      exact_mod_cast this
    exact hcard.trans (goodBlock_success_le (W x) (eta x) (hη x hx))
  have hsum : ((X.card : ℝ) * (WgoodSq X W : ℝ))
      ≤ ∑ x ∈ X, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
    have := Finset.sum_le_sum hper
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have hnonneg : (0 : ℝ) ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hsum hnonneg

/-- When `WgoodSq X W ≤ 1` and selected multiplicities are positive, bounds the normalized
square-root sum below using the square of `WgoodSq X W`. -/
theorem lemma31_printed_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (X : Finset (Fin n → F)) (W : (Fin n → F) → Finset (Fin n → F))
    (eta : (Fin n → F) → (Fin n → F) → ℕ)
    (hη : ∀ x ∈ X, ∀ w ∈ W x, 1 ≤ eta x w) (hsmall : WgoodSq X W ≤ 1) :
    ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ * ((X.card : ℝ) * (WgoodSq X W : ℝ) ^ 2)
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ∑ x ∈ X, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
  classical
  have hsq : ((WgoodSq X W : ℝ) ^ 2) ≤ (WgoodSq X W : ℝ) := by
    have h1 : (WgoodSq X W : ℝ) ≤ 1 := by exact_mod_cast hsmall
    have h0 : (0 : ℝ) ≤ (WgoodSq X W : ℝ) := by positivity
    nlinarith
  have hnonneg : (0 : ℝ) ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ := by positivity
  have hX : (0 : ℝ) ≤ (X.card : ℝ) := by positivity
  calc ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ * ((X.card : ℝ) * (WgoodSq X W : ℝ) ^ 2)
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ * ((X.card : ℝ) * (WgoodSq X W : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hnonneg
        exact mul_le_mul_of_nonneg_left hsq hX
    _ ≤ _ := lemma31_min_square_bound X W eta hη

/-- If `X` and the minimum good output cardinality are each at least d^n/2^n and selected
multiplicities are positive, the normalized square-root sum is at least 2^(−3n). -/
theorem success_probability_constant_of_good_counts {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {n : ℕ} (X : Finset (Fin n → F)) (W : (Fin n → F) → Finset (Fin n → F))
    (eta : (Fin n → F) → (Fin n → F) → ℕ)
    (hη : ∀ x ∈ X, ∀ w ∈ W x, 1 ≤ eta x w)
    (hd : 0 < Fintype.card F)
    (hX : (Fintype.card F : ℝ) ^ n / 2 ^ n ≤ (X.card : ℝ))
    (hW : (Fintype.card F : ℝ) ^ n / 2 ^ n ≤ (WgoodMin X W : ℝ)) :
    ((2 : ℝ) ^ (3 * n))⁻¹
      ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ∑ x ∈ X, (∑ w ∈ W x, Real.sqrt (eta x w)) ^ 2 := by
  classical
  have hd' : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hd
  have hX0 : (0 : ℝ) ≤ (X.card : ℝ) := by positivity
  have hW0 : (0 : ℝ) ≤ (WgoodMin X W : ℝ) := by positivity
  have hcube : ((Fintype.card F : ℝ) ^ n / 2 ^ n) ^ 3
      ≤ (X.card : ℝ) * ((WgoodMin X W : ℝ) ^ 2) := by
    have hpos : (0 : ℝ) ≤ (Fintype.card F : ℝ) ^ n / 2 ^ n := by positivity
    have hsq : ((Fintype.card F : ℝ) ^ n / 2 ^ n) ^ 2 ≤ ((WgoodMin X W : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hpos hW 2
    calc ((Fintype.card F : ℝ) ^ n / 2 ^ n) ^ 3
        = ((Fintype.card F : ℝ) ^ n / 2 ^ n) * ((Fintype.card F : ℝ) ^ n / 2 ^ n) ^ 2 := by
          ring
      _ ≤ (X.card : ℝ) * ((WgoodMin X W : ℝ)) ^ 2 :=
          mul_le_mul hX hsq (by positivity) hX0
  have hd3 : (((Fintype.card F : ℝ)) ^ n) ^ 3 = (Fintype.card F : ℝ) ^ (3 * n) := by
    rw [← pow_mul, mul_comm]
  have h23 : (((2 : ℝ)) ^ n) ^ 3 = (2 : ℝ) ^ (3 * n) := by
    rw [← pow_mul, mul_comm]
  have hkey : ((2 : ℝ) ^ (3 * n))⁻¹
      = ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ((Fintype.card F : ℝ) ^ n / 2 ^ n) ^ 3 := by
    rw [div_pow, hd3, h23]
    field_simp
  calc ((2 : ℝ) ^ (3 * n))⁻¹
      = ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ((Fintype.card F : ℝ) ^ n / 2 ^ n) ^ 3 := hkey
    _ ≤ ((Fintype.card F : ℝ) ^ (3 * n))⁻¹ *
          ((X.card : ℝ) * (WgoodMin X W : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left hcube (by positivity)
    _ ≤ _ := lemma31_success_lower_bound X W eta hη

end Qatlib.Papers.HiddenPoly07.MainResults
