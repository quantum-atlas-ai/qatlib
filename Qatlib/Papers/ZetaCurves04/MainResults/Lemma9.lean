/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurves04.MainResults.Model.CurveZetaDefs

/-!
# Uniformization and amplification of finite samplers

A bounded-ratio distribution has a positive lower bound on every point mass. Reweighting by the
minimum point mass yields equal accepted masses, and the record `amplifiedSampler` combines a
uniform output distribution with a repeated-success expression bounded below by three quarters.

This development forms part of the formalization of [Kedlaya2006].

## Main statements

* `conditional_uniform`: Reweighting nonzero point masses by their minimum and normalizing gives
  the constant mass `(card V)⁻¹`.
* `lemma9_amplification`: Every sampler on a nonempty finite type yields a one-uniform sampler
  with constant output masses and success value at least `3 / 4`.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurves04.MainResults.Lemma9

open Qatlib.Papers.ZetaCurves04.MainResults.Model

/-- A normalized distribution with point-mass ratio at most `b ≥ 1` has each point mass at least
`1 / (b * card V)`. -/
theorem min_prob_lower_bound {V : Type} [Fintype V] [Nonempty V]
    {p : V → ℝ} {b : ℝ} (hb : 1 ≤ b) (hsum : (∑ x : V, p x) = 1)
    (huni : ∀ x y, p x ≤ b * p y) :
    ∀ x : V, 1 / (b * (Fintype.card V : ℝ)) ≤ p x := by
  intro x
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hb
  have hle : (∑ y : V, p y) ≤ b * (Fintype.card V : ℝ) * p x := by
    have h1 : ∀ y : V, p y ≤ b * p x := fun y => huni y x
    calc (∑ y : V, p y) ≤ ∑ y : V, b * p x := Finset.sum_le_sum (fun y _ => h1 y)
      _ = (Fintype.card V : ℝ) * (b * p x) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = b * (Fintype.card V : ℝ) * p x := by ring
  have hone : (1 : ℝ) ≤ b * (Fintype.card V : ℝ) * p x := by
    rw [← hsum]; exact hle
  by_cases hx : p x ≤ 0
  · have hzero : b * (Fintype.card V : ℝ) * p x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (mul_pos hbpos hNpos)) hx
    linarith [hone, hzero]
  · have hbN : (0 : ℝ) < b * (Fintype.card V : ℝ) := mul_pos hbpos hNpos
    rw [div_le_iff₀ hbN]
    nlinarith [hone]

/-- Multiplying any point mass by the cardinality gives a value at least `1 / b` under the
normalization and bounded-ratio hypotheses. -/
theorem min_prob_times_card {V : Type} [Fintype V] [Nonempty V]
    {p : V → ℝ} {b : ℝ} (hb : 1 ≤ b) (hsum : (∑ x : V, p x) = 1)
    (huni : ∀ x y, p x ≤ b * p y) (x : V) :
    1 / b ≤ p x * (Fintype.card V : ℝ) := by
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hb
  have hx := min_prob_lower_bound hb hsum huni x
  rw [div_le_iff₀ (mul_pos hbpos hNpos)] at hx
  rw [div_le_iff₀ hbpos]
  nlinarith [hx]

/-- Reweighting a nonzero point mass `p x` by `p₀ / p x` gives the constant mass `p₀`. -/
theorem uniform_acceptance {V : Type} (p : V → ℝ) (p₀ : ℝ) {x : V}
    (hx : p x ≠ 0) : p x * (p₀ / p x) = p₀ := by
  field_simp

/-- Reweighting nonzero point masses by their minimum and normalizing gives the constant mass
`(card V)⁻¹`. See [Kedlaya2006]. -/
theorem conditional_uniform {V : Type} [Fintype V] [Nonempty V]
    (p : V → ℝ) (_hsum : (∑ x : V, p x) = 1) (hpos : ∀ x, p x ≠ 0) :
    ∀ x : V,
      (p x * (minProb p / p x)) /
        (∑ y : V, p y * (minProb p / p y)) =
      (Fintype.card V : ℝ)⁻¹ := by
  intro x
  have hnum : p x * (minProb p / p x) = minProb p :=
    uniform_acceptance p (minProb p) (hpos x)
  have hden : (∑ y : V, p y * (minProb p / p y)) = (Fintype.card V : ℝ) * minProb p := by
    rw [Finset.sum_congr rfl (fun y _ => uniform_acceptance p (minProb p) (hpos y))]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hnum, hden]
  have hp0 : minProb p ≠ 0 := by
    obtain ⟨x₀, hx₀⟩ := exists_minProb_eq p
    rw [hx₀]
    exact hpos x₀
  have hN : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Fintype.card_pos)
  field_simp

/-- The sampler record with uniform distribution, uniformity factor one, and success value one. -/
def oneUniformSampler (V : Type) [Fintype V] [Nonempty V] : UniformSampler V where
  b := 1
  hb := le_refl 1
  dist := fun _ => (Fintype.card V : ℝ)⁻¹
  dist_nonneg := fun _ => by positivity
  dist_sum := by
    have hN : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt Fintype.card_pos)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hN
  success := 1
  success_nonneg := zero_le_one
  success_le_one := le_refl 1
  uniform := fun _ _ => by rw [one_mul]

/-- The canonical uniform sampler has uniformity factor at most one. -/
theorem oneUniformSampler_isOneUniform (V : Type) [Fintype V] [Nonempty V] :
    IsOneUniform (oneUniformSampler V) := by
  unfold IsOneUniform oneUniformSampler
  norm_num

/-- The minimum point mass of a sampler is nonnegative. -/
theorem minProb_nonneg {V : Type} [Fintype V] [Nonempty V] (O : UniformSampler V) :
    0 ≤ minProb O.dist := by
  obtain ⟨x, hx⟩ := exists_minProb_eq O.dist
  rw [hx]
  exact O.dist_nonneg x

/-- The minimum point mass times the cardinality is at least the reciprocal of the uniformity
factor. -/
theorem p0_times_card_ge {V : Type} [Fintype V] [Nonempty V] (O : UniformSampler V) :
    1 / O.b ≤ minProb O.dist * (Fintype.card V : ℝ) := by
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hbpos : (0 : ℝ) < O.b := lt_of_lt_of_le zero_lt_one O.hb
  obtain ⟨x, hx⟩ := exists_minProb_eq O.dist
  have hx' : 1 / (O.b * (Fintype.card V : ℝ)) ≤ O.dist x :=
    min_prob_lower_bound O.hb O.dist_sum O.uniform x
  rw [div_le_iff₀ (mul_pos hbpos hNpos)] at hx'
  rw [hx, div_le_iff₀ hbpos]
  nlinarith [hx']

/-- The minimum point mass times the cardinality is at most one. -/
theorem p0_times_card_le_one {V : Type} [Fintype V] [Nonempty V] (O : UniformSampler V) :
    minProb O.dist * (Fintype.card V : ℝ) ≤ 1 := by
  have h1 : minProb O.dist * (Fintype.card V : ℝ) = ∑ _x : V, minProb O.dist := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [h1]
  calc (∑ _x : V, minProb O.dist) ≤ ∑ x : V, O.dist x :=
        Finset.sum_le_sum (fun x _ => minProb_le O.dist x)
    _ = 1 := O.dist_sum

/-- For `b ≥ 1` and `1 / b ≤ s ≤ 1`, the repeated-success expression after `ceil (16 * b ^ 2)`
trials is at least `3 / 4`. See [Kedlaya2006]. -/
theorem boost_general (b s : ℝ) (hb : 1 ≤ b) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hs : 1 / b ≤ s) :
    1 - (1 - s) ^ (Nat.ceil (16 * b ^ 2)) ≥ 3 / 4 := by
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hbne : b ≠ 0 := ne_of_gt hbpos
  set K : ℕ := Nat.ceil (16 * b ^ 2) with hK
  have hKge : 16 * b ^ 2 ≤ (K : ℝ) := by
    rw [hK]
    exact Nat.le_ceil _
  have hKpos : (0 : ℝ) < (K : ℝ) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 16 * b ^ 2) hKge
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos

  have hKs : 12 ≤ (K : ℝ) * s := by
    have h1 : 16 * b ^ 2 * s ≤ (K : ℝ) * s :=
      mul_le_mul_of_nonneg_right hKge hs0
    have h2 : 16 * b ≤ 16 * b ^ 2 * s := by
      have hm := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 16 * b ^ 2)
      have heq : 16 * b ^ 2 * (1 / b) = 16 * b := by
        field_simp
      linarith [hm, heq]
    nlinarith [h1, h2, hb]

  have htle : (K : ℝ) * s ≤ (K : ℝ) := by
    have hknn : (0 : ℝ) ≤ (K : ℝ) := le_of_lt hKpos
    have := mul_le_mul_of_nonneg_left hs1 hknn
    simpa using this
  have hexp1 : (1 - s) ^ K ≤ Real.exp (-((K : ℝ) * s)) := by
    have h := Real.one_sub_div_pow_le_exp_neg (n := K) (t := (K : ℝ) * s) htle
    have hdiv : ((K : ℝ) * s) / (K : ℝ) = s := by
      field_simp
    rwa [hdiv] at h
  have hexp2 : Real.exp (-((K : ℝ) * s)) ≤ Real.exp (-12) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hKs]
  have hexp3 : Real.exp (-12) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    have hexp12 : (4 : ℝ) ≤ Real.exp 12 := by
      have h := Real.add_one_le_exp 12
      linarith
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hexp12
  have hchain : (1 - s) ^ K ≤ 1 / 4 :=
    le_trans (le_trans hexp1 hexp2) hexp3
  linarith [hchain]

/-- The natural ceiling of `16 * O.b ^ 2`, cast to the reals, is at least `16 * O.b ^ 2`. See
[Kedlaya2006]. -/
theorem lemma9_invocation_bound {V : Type} [Fintype V] [Nonempty V] (O : UniformSampler V) :
    16 * O.b ^ 2 ≤ ((Nat.ceil (16 * O.b ^ 2) : ℕ) : ℝ) :=
  Nat.le_ceil _

/-- A uniform sampler record with success value `1 - (1 - minProb O.dist * card V) ^ ceil (16 *
O.b ^ 2)`. -/
def amplifiedSampler {V : Type} [Fintype V] [Nonempty V]
    (O : UniformSampler V) : UniformSampler V where
  b := 1
  hb := le_refl 1
  dist := fun _ => (Fintype.card V : ℝ)⁻¹
  dist_nonneg := fun _ => by positivity
  dist_sum := by
    have hN : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt Fintype.card_pos)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hN
  success := 1 - (1 - minProb O.dist * (Fintype.card V : ℝ)) ^ Nat.ceil (16 * O.b ^ 2)
  success_nonneg := by
    have hs0 : 0 ≤ minProb O.dist * (Fintype.card V : ℝ) :=
      mul_nonneg (minProb_nonneg O) (by positivity)
    have hs1 : minProb O.dist * (Fintype.card V : ℝ) ≤ 1 := p0_times_card_le_one O
    have hp : (1 - minProb O.dist * (Fintype.card V : ℝ)) ^ Nat.ceil (16 * O.b ^ 2) ≤ 1 :=
      pow_le_one₀ (by linarith) (by linarith)
    linarith
  success_le_one := by
    have hp : 0 ≤ (1 - minProb O.dist * (Fintype.card V : ℝ)) ^ Nat.ceil (16 * O.b ^ 2) := by
      apply pow_nonneg
      have hs1 : minProb O.dist * (Fintype.card V : ℝ) ≤ 1 := p0_times_card_le_one O
      linarith
    linarith
  uniform := fun _ _ => by rw [one_mul]

/-- Every sampler on a nonempty finite type yields a one-uniform sampler with constant output
masses and success value at least `3 / 4`. See [Kedlaya2006]. -/
theorem lemma9_amplification {V : Type} [Fintype V] [Nonempty V]
    (O : UniformSampler V) :
    ∃ O' : UniformSampler V,
      IsOneUniform O' ∧
      (∀ x : V, O'.dist x = (Fintype.card V : ℝ)⁻¹) ∧
      (3 / 4 : ℝ) ≤ O'.success := by
  refine ⟨amplifiedSampler O, ?_, ?_, ?_⟩
  · unfold IsOneUniform amplifiedSampler
    norm_num
  · intro x
    rfl
  · change (3 / 4 : ℝ) ≤
      1 - (1 - minProb O.dist * (Fintype.card V : ℝ)) ^ Nat.ceil (16 * O.b ^ 2)
    have hs0 : 0 ≤ minProb O.dist * (Fintype.card V : ℝ) :=
      mul_nonneg (minProb_nonneg O) (by positivity)
    have hs1 : minProb O.dist * (Fintype.card V : ℝ) ≤ 1 := p0_times_card_le_one O
    have hs : 1 / O.b ≤ minProb O.dist * (Fintype.card V : ℝ) := p0_times_card_ge O
    have h := boost_general O.b (minProb O.dist * (Fintype.card V : ℝ)) O.hb hs0 hs1 hs
    linarith [h]

end Qatlib.Papers.ZetaCurves04.MainResults.Lemma9
