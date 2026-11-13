/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-!
# Near-uniform samplers from finite families

Uniformly choosing a finite-family index and then an element of its nonempty member set gives a
normalized distribution. Equal incidence counts and bounded member sizes control its uniformity
factor; numerical success estimates and repetition bounds yield `lemma8_oracle_of_family`.

This development forms part of the formalization of [Kedlaya2006].

## Main statements

* `sampling_uniformity`: A family of nonempty sets of size at most `K`, with constant incidence
  count, defines a normalized two-stage sampling distribution whose point masses differ by at
  most a factor `K`.
* `lemma8_oracle_of_family`: Under the stated family and numerical hypotheses, there exists a
  sampler with uniformity factor at most `1 + (2 * g - 2 + d) / e` and success value at least `3
  / 4`.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Lemma8

open Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-- Dividing the stated positive-degree inequality by `e` gives the uniformity-factor bound `j *
d / e ≤ 1 + (2 * g - 2 + d) / e`. See [Kedlaya2006]. -/
theorem lemma8_ratio_bound {j d e g : ℕ} (he : 0 < e)
    (hx : (j : ℝ) * (d : ℝ) ≤ 2 * (g : ℝ) - 2 + (e : ℝ) + (d : ℝ)) :
    ((j : ℝ) * (d : ℝ)) / (e : ℝ) ≤ 1 + (2 * (g : ℝ) - 2 + (d : ℝ)) / (e : ℝ) := by
  have he_pos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have h1 : ((j : ℝ) * (d : ℝ)) / (e : ℝ)
      ≤ (2 * (g : ℝ) - 2 + (e : ℝ) + (d : ℝ)) / (e : ℝ) := by
    rw [div_le_iff₀ he_pos]
    have hmul : (2 * (g : ℝ) - 2 + (e : ℝ) + (d : ℝ)) / (e : ℝ) * (e : ℝ)
        = 2 * (g : ℝ) - 2 + (e : ℝ) + (d : ℝ) := by
      field_simp
    rw [hmul]
    exact hx
  have h2 : (2 * (g : ℝ) - 2 + (e : ℝ) + (d : ℝ)) / (e : ℝ)
      = 1 + (2 * (g : ℝ) - 2 + (d : ℝ)) / (e : ℝ) := by
    field_simp
    ring
  rw [h2] at h1
  exact h1

/-- For positive `d`, the stated natural quotient multiplied by `d` is bounded by `2 * g - 2 + e
+ d`. -/
theorem lemma8_ceiling_mul_le {g e d : ℕ} (hd : 0 < d) :
    ((2 * g - 1 + e + d - 1) / d) * d ≤ 2 * g - 2 + e + d := by
  have h := Nat.div_mul_le_self (2 * g - 1 + e + d - 1) d
  omega

/-- A family of nonempty sets of size at most `K`, with constant incidence count, defines a
normalized two-stage sampling distribution whose point masses differ by at most a factor
`K`. See [Kedlaya2006]. -/
theorem sampling_uniformity
    {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V]
    (S : F → Finset V) (K A : ℕ)
    (hF : 0 < Fintype.card F)
    (hne : ∀ f, (S f).Nonempty)
    (hK : ∀ f, (S f).card ≤ K)
    (hhit : ∀ x : V, (Finset.univ.filter (fun f => x ∈ S f)).card = A) :
    (∑ x : V,
        ((Fintype.card F : ℝ)⁻¹ *
          ∑ f : F, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0)) = 1) ∧
      (∀ x y : V,
        ((Fintype.card F : ℝ)⁻¹ *
            ∑ f : F, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0)) ≤
          (K : ℝ) *
            ((Fintype.card F : ℝ)⁻¹ *
              ∑ f : F, (if y ∈ S f then ((S f).card : ℝ)⁻¹ else 0))) := by
  classical
  haveI : Nonempty F := Fintype.card_pos_iff.mp hF
  set M : ℕ := Fintype.card F with hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hF
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hMinv : (0 : ℝ) ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)

  have hSpos : ∀ f : F, 0 < (S f).card := fun f => Finset.card_pos.mpr (hne f)
  have hSne : ∀ f : F, ((S f).card : ℝ) ≠ 0 := by
    intro f
    exact_mod_cast (ne_of_gt (hSpos f))

  have hcol : ∀ f : F,
      (∑ x : V, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0)) = 1 := by
    intro f
    rw [Finset.sum_ite_mem_eq]
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (hSne f)

  have hKpos : (0 : ℝ) < (K : ℝ) := by
    obtain ⟨f₀⟩ := ‹Nonempty F›
    have : 0 < K := lt_of_lt_of_le (hSpos f₀) (hK f₀)
    exact_mod_cast this
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  constructor
  · calc (∑ x : V,
          ((M : ℝ)⁻¹ * ∑ f : F, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0)))
        = (M : ℝ)⁻¹ *
            ∑ x : V, ∑ f : F, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0) := by
          rw [Finset.mul_sum]
      _ = (M : ℝ)⁻¹ *
            ∑ f : F, ∑ x : V, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0) := by
          rw [Finset.sum_comm]
      _ = (M : ℝ)⁻¹ * ∑ _f : F, (1 : ℝ) := by
          congr 1
          exact Finset.sum_congr rfl (fun f _ => hcol f)
      _ = (M : ℝ)⁻¹ * (M : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ = 1 := inv_mul_cancel₀ hMne
  · intro x y

    have hpx : ((M : ℝ)⁻¹ *
        ∑ f : F, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0)) ≤ (M : ℝ)⁻¹ * (A : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hMinv
      calc (∑ f : F, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0))
          ≤ ∑ f : F, (if x ∈ S f then (1 : ℝ) else 0) := by
            apply Finset.sum_le_sum
            intro f _
            split_ifs with h
            · exact inv_le_one_of_one_le₀ (by exact_mod_cast (hSpos f))
            · simp
        _ = (A : ℝ) := by
            rw [← Finset.sum_filter]
            simp [hhit x]

    have hpy : (M : ℝ)⁻¹ * (A : ℝ) * (K : ℝ)⁻¹ ≤
        ((M : ℝ)⁻¹ *
          ∑ f : F, (if y ∈ S f then ((S f).card : ℝ)⁻¹ else 0)) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hMinv
      have hAK : (A : ℝ) * (K : ℝ)⁻¹ =
          ∑ f : F, (if y ∈ S f then (K : ℝ)⁻¹ else 0) := by
        rw [← Finset.sum_filter]
        simp [hhit y]
      rw [hAK]
      apply Finset.sum_le_sum
      intro f _
      split_ifs with h
      · exact inv_anti₀ (by exact_mod_cast hSpos f) (by exact_mod_cast hK f)
      · simp
    calc ((M : ℝ)⁻¹ *
          ∑ f : F, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0))
        ≤ (M : ℝ)⁻¹ * (A : ℝ) := hpx
      _ = (K : ℝ) * ((M : ℝ)⁻¹ * (A : ℝ) * (K : ℝ)⁻¹) := by
          field_simp
      _ ≤ (K : ℝ) *
            ((M : ℝ)⁻¹ *
              ∑ f : F, (if y ∈ S f then ((S f).card : ℝ)⁻¹ else 0)) := by
          exact mul_le_mul_of_nonneg_left hpy (le_of_lt hKpos)

/-- If `16 * g < halfPower q e`, the normalized prime-divisor lower-bound expression is strictly
greater than `1 / (8 * e)`. See [Kedlaya2006]. -/
theorem lemma8_success_fraction (q e g : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e)
    (hbig : 16 * (g : ℝ) < halfPower q e) :
    (1 / (e : ℝ)) *
        (((q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e) /
          (q : ℝ) ^ e) > 1 / (8 * (e : ℝ)) := by
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hQ2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hQe : (0 : ℝ) < (q : ℝ) ^ e := by positivity
  have hH2 : halfPower q e ^ 2 = (q : ℝ) ^ e := halfPower_sq q e
  have hHpos : 0 < halfPower q e := by
    have : (0 : ℝ) ≤ 16 * (g : ℝ) := by positivity
    linarith

  have hinv : ((q : ℝ))⁻¹ ≤ 1 / 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hQ2
    simpa [one_div] using this

  have hA : (q : ℝ) ^ e / 2 ≤ (q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) := by
    have : (1 : ℝ) / 2 ≤ 1 - ((q : ℝ))⁻¹ := by linarith
    nlinarith [hQe, this]

  have hB : 4 * (g : ℝ) * halfPower q e < (q : ℝ) ^ e / 4 := by
    have hmul : 16 * (g : ℝ) * halfPower q e < halfPower q e * halfPower q e :=
      mul_lt_mul_of_pos_right hbig hHpos
    nlinarith [hmul, hH2]

  have hmain : (q : ℝ) ^ e / 8 <
      (q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e := by
    nlinarith [hA, hB, hQe]
  have hdiv : (1 : ℝ) / 8 <
      ((q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e) /
        (q : ℝ) ^ e := by
    rw [lt_div_iff₀ hQe]
    nlinarith [hmain]
  have hcpos : (0 : ℝ) < 1 / (e : ℝ) := one_div_pos.mpr hepos
  have hmul := mul_lt_mul_of_pos_left hdiv hcpos
  have heq : (1 : ℝ) / (e : ℝ) * (1 / 8) = 1 / (8 * (e : ℝ)) := by
    field_simp
  rw [heq] at hmul
  exact hmul

/-- A success value between `1 / (8 * e)` and one gives repeated-success expression at least `3
/ 4` after `1024 * e ^ 2` repetitions. See [Kedlaya2006]. -/
theorem lemma8_boost (e : ℕ) (he : 1 ≤ e) (s : ℝ)
    (_hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs : 1 / (8 * (e : ℝ)) ≤ s) :
    1 - (1 - s) ^ (1024 * e ^ 2) ≥ 3 / 4 := by
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hene : (e : ℝ) ≠ 0 := ne_of_gt hepos
  have hcast : ((1024 * e ^ 2 : ℕ) : ℝ) = 1024 * (e : ℝ) ^ 2 := by
    push_cast
    ring

  have htle : ((1024 * e ^ 2 : ℕ) : ℝ) * s ≤ ((1024 * e ^ 2 : ℕ) : ℝ) := by
    have hknn : (0 : ℝ) ≤ ((1024 * e ^ 2 : ℕ) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hs1 hknn
    simpa using this

  have hexp1 : (1 - s) ^ (1024 * e ^ 2) ≤ Real.exp (-(((1024 * e ^ 2 : ℕ) : ℝ) * s)) := by
    have h := Real.one_sub_div_pow_le_exp_neg (n := 1024 * e ^ 2)
      (t := ((1024 * e ^ 2 : ℕ) : ℝ) * s) htle
    have hdiv : (((1024 * e ^ 2 : ℕ) : ℝ) * s) / (((1024 * e ^ 2 : ℕ) : ℝ)) = s := by
      have hne : ((1024 * e ^ 2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rwa [hdiv] at h

  have hks : 12 ≤ ((1024 * e ^ 2 : ℕ) : ℝ) * s := by
    have he' : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have hknn : (0 : ℝ) ≤ ((1024 * e ^ 2 : ℕ) : ℝ) := by positivity
    have h1 : ((1024 * e ^ 2 : ℕ) : ℝ) * (1 / (8 * (e : ℝ))) ≤
        ((1024 * e ^ 2 : ℕ) : ℝ) * s :=
      mul_le_mul_of_nonneg_left hs hknn
    have heq : ((1024 * e ^ 2 : ℕ) : ℝ) * (1 / (8 * (e : ℝ))) = 128 * (e : ℝ) := by
      rw [hcast]
      field_simp
      ring
    rw [heq] at h1
    nlinarith [h1, he']
  have hexp2 : Real.exp (-(((1024 * e ^ 2 : ℕ) : ℝ) * s)) ≤ Real.exp (-12) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hks]
  have hexp3 : Real.exp (-12) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    have hexp12 : (4 : ℝ) ≤ Real.exp 12 := by
      have h := Real.add_one_le_exp 12
      linarith
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hexp12
  have hchain : (1 - s) ^ (1024 * e ^ 2) ≤ 1 / 4 :=
    le_trans (le_trans hexp1 hexp2) hexp3
  linarith [hchain]

/-- Under the field-size, positive-degree, and genus-size hypotheses, the normalized
prime-divisor lower-bound expression is nonnegative. -/
theorem lemma8_success_nonneg (q e g : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e)
    (hbig : 16 * (g : ℝ) < halfPower q e) :
    0 ≤ (1 / (e : ℝ)) *
        (((q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e) /
          (q : ℝ) ^ e) := by
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hQ2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hQe : (0 : ℝ) < (q : ℝ) ^ e := by positivity
  have hH2 : halfPower q e ^ 2 = (q : ℝ) ^ e := halfPower_sq q e
  have hHpos : 0 < halfPower q e := by
    have : (0 : ℝ) ≤ 16 * (g : ℝ) := by positivity
    linarith
  have hinv : ((q : ℝ))⁻¹ ≤ 1 / 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hQ2
    simpa [one_div] using this
  have hA : (q : ℝ) ^ e / 2 ≤ (q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) := by
    have : (1 : ℝ) / 2 ≤ 1 - ((q : ℝ))⁻¹ := by linarith
    nlinarith [hQe, this]
  have hB : 4 * (g : ℝ) * halfPower q e < (q : ℝ) ^ e / 4 := by
    have hmul : 16 * (g : ℝ) * halfPower q e < halfPower q e * halfPower q e :=
      mul_lt_mul_of_pos_right hbig hHpos
    nlinarith [hmul, hH2]
  have hmain : 0 <
      (q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e := by
    nlinarith [hA, hB, hQe]
  have hdiv : 0 <
      ((q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e) /
        (q : ℝ) ^ e :=
    div_pos hmain hQe
  exact mul_nonneg (le_of_lt (one_div_pos.mpr hepos)) (le_of_lt hdiv)

/-- For `q ≥ 2` and positive `e`, the normalized prime-divisor lower-bound expression is at most
one. -/
theorem lemma8_success_le_one (q e g : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e) :
    (1 / (e : ℝ)) *
        (((q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e) /
          (q : ℝ) ^ e) ≤ 1 := by
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hQ2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hQe : (0 : ℝ) < (q : ℝ) ^ e := by positivity
  have hterm : 0 ≤ 4 * (g : ℝ) * halfPower q e := by
    have := halfPower_nonneg q e
    positivity
  have hA : (q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) ≤ (q : ℝ) ^ e := by
    have h1 : (q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) =
        (q : ℝ) ^ e - (q : ℝ) ^ e * ((q : ℝ))⁻¹ := by ring
    rw [h1]
    have h2 : 0 ≤ (q : ℝ) ^ e * ((q : ℝ))⁻¹ :=
      mul_nonneg (le_of_lt hQe) (le_of_lt (inv_pos.mpr hQpos))
    linarith
  have hAle : (q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e
      ≤ (q : ℝ) ^ e := by linarith
  have hdivle :
      ((q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e) /
        (q : ℝ) ^ e ≤ 1 := by
    rw [div_le_iff₀ hQe]
    linarith
  have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hinvle : (1 : ℝ) / (e : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hepos]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hdivle
    (le_of_lt (one_div_pos.mpr hepos))
  have hone : (1 : ℝ) / (e : ℝ) * 1 = 1 / (e : ℝ) := mul_one _
  rw [hone] at hmul
  linarith

/-- Under the stated family and numerical hypotheses, there exists a sampler with uniformity
factor at most `1 + (2 * g - 2 + d) / e` and success value at least `3 / 4`. See
[Kedlaya2006]. -/
theorem lemma8_oracle_of_family
    {V F : Type} [Fintype V] [Fintype F] [DecidableEq V]
    (S : F → Finset V) (K A q e g d : ℕ)
    (hq : 2 ≤ q) (he : 1 ≤ e) (hbig : 16 * (g : ℝ) < halfPower q e)
    (hF : 0 < Fintype.card F) (hne : ∀ f, (S f).Nonempty)
    (hK : ∀ f, (S f).card ≤ K)
    (hhit : ∀ x : V, (Finset.univ.filter (fun f => x ∈ S f)).card = A)
    (hK1 : 1 ≤ K)
    (hKb : (K : ℝ) ≤ 1 + (2 * (g : ℝ) - 2 + (d : ℝ)) / (e : ℝ)) :
    ∃ O : UniformSampler V,
      O.b ≤ 1 + (2 * (g : ℝ) - 2 + (d : ℝ)) / (e : ℝ) ∧
      (∀ x y : V, O.dist x ≤ O.b * O.dist y) ∧
      (3 / 4 : ℝ) ≤ O.success := by
  classical
  obtain ⟨hsum, huni⟩ := sampling_uniformity S K A hF hne hK hhit
  set s : ℝ := (1 / (e : ℝ)) *
      (((q : ℝ) ^ e * (1 - ((q : ℝ))⁻¹) - 4 * (g : ℝ) * halfPower q e) /
        (q : ℝ) ^ e) with hs_def
  have hs0 : 0 ≤ s := lemma8_success_nonneg q e g hq he hbig
  have hs1 : s ≤ 1 := lemma8_success_le_one q e g hq he
  have hs : 1 / (8 * (e : ℝ)) ≤ s :=
    le_of_lt (lemma8_success_fraction q e g hq he hbig)
  have hboost : 1 - (1 - s) ^ (1024 * e ^ 2) ≥ 3 / 4 :=
    lemma8_boost e he s hs0 hs1 hs
  refine ⟨{
    b := (K : ℝ)
    hb := by exact_mod_cast hK1
    dist := fun x => (Fintype.card F : ℝ)⁻¹ *
      ∑ f : F, (if x ∈ S f then ((S f).card : ℝ)⁻¹ else 0)
    dist_nonneg := ?_
    dist_sum := hsum
    success := 1 - (1 - s) ^ (1024 * e ^ 2)
    success_nonneg := ?_
    success_le_one := ?_
    uniform := huni }, ?_, huni, hboost⟩
  · intro x
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro f _
    split_ifs
    · exact inv_nonneg.mpr (by positivity)
    · exact le_refl 0
  · have h1 : (0 : ℝ) ≤ 1 - s := by linarith
    have h2 : 1 - s ≤ 1 := by linarith
    have hp : (1 - s) ^ (1024 * e ^ 2) ≤ 1 := pow_le_one₀ h1 h2
    linarith
  · have h1 : (0 : ℝ) ≤ 1 - s := by linarith
    have hp : 0 ≤ (1 - s) ^ (1024 * e ^ 2) := pow_nonneg h1 _
    linarith
  · exact hKb

end Qatlib.Papers.ZetaCurve04.MainResults.Lemma8
