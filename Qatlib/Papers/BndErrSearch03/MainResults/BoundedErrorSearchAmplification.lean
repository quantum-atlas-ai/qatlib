/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Scalar amplification bounds for bounded-error search

This module develops analytic estimates for the bounded-error search argument of
[HoyerMoscaDeWolf2003]. `ampGain`, `errFactor`, and `roundGain` encode the trigonometric gain
and error factor, while `sum_theta_sq_le` and `prod_gainLower_ge` control accumulated angle and
product losses.

`amplitude_ge_constant` proves the threshold `α m ≥ 1/24` from explicit recurrence, angle,
initialization, and stopping-scale hypotheses. `src_amplitude_ge_constant` derives the required
angle-sum bound from the supplied amplitude estimates, and `success_probability_ge` converts the
amplitude threshold into `α m ^ 2 ≥ 1/576`.

## Main statements

* `amplitude_ge_constant`: the conditional scalar amplitude threshold `1/24`.
* `src_amplitude_ge_constant`: the threshold derived from the supplied amplitude recurrences.
* `success_probability_ge`: the resulting squared-amplitude threshold `1/576`.

## References

* [Høyer et al., 2003][HoyerMoscaDeWolf2003]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.BndErrSearch03.MainResults.BoundedErrorSearchAmplification

/-- The scalar trigonometric gain `Real.sin (3 * θ) / Real.sin θ`. -/
def ampGain (θ : ℝ) : ℝ := Real.sin (3 * θ) / Real.sin θ

/-- When `Real.sin θ` is nonzero, the amplification gain equals `3 - 4 * (Real.sin θ) ^ 2`. -/
theorem ampGain_eq (θ : ℝ) (h : Real.sin θ ≠ 0) :
    ampGain θ = 3 - 4 * (Real.sin θ) ^ 2 := by
  unfold ampGain
  rw [Real.sin_three_mul]
  field_simp

/-- For `0 < θ ≤ Real.pi / 2`, the amplification gain is at least `3 - (9 / 2) * θ ^ 2`. -/
theorem ampGain_ge (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 2) :
    3 - (9 / 2) * θ ^ 2 ≤ ampGain θ := by
  have hspos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [ampGain_eq θ hspos.ne']
  have habs : |Real.sin θ| ≤ |θ| := Real.abs_sin_le_abs
  rw [abs_of_nonneg hspos.le, abs_of_nonneg h0.le] at habs
  have hsq : (Real.sin θ) ^ 2 ≤ θ ^ 2 := by
    nlinarith [sq_nonneg (Real.sin θ), sq_nonneg θ]
  nlinarith [hsq]

/-- For `0 < θ ≤ Real.pi / 2`, the amplification gain is at most three. -/
theorem ampGain_le_three (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 2) :
    ampGain θ ≤ 3 := by
  have hspos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [ampGain_eq θ hspos.ne']
  have hsq : 0 ≤ (Real.sin θ) ^ 2 := sq_nonneg _
  nlinarith [hsq]

/-- The round-dependent error factor `Real.sqrt (1 - ((2 : ℝ) ^ (k + 5))⁻¹)`. -/
def errFactor (k : ℕ) : ℝ := Real.sqrt (1 - ((2 : ℝ) ^ (k + 5))⁻¹)

/-- For `0 ≤ e ≤ 1`, the square root of `1 - e` is at least `1 - e`. -/
theorem sqrt_one_sub_ge (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    1 - e ≤ Real.sqrt (1 - e) := by
  have h1me : 0 ≤ 1 - e := by linarith
  have hsq : (1 - e) ^ 2 ≤ 1 - e := by nlinarith
  calc (1 - e) = Real.sqrt ((1 - e) ^ 2) := (Real.sqrt_sq h1me).symm
    _ ≤ Real.sqrt (1 - e) := Real.sqrt_le_sqrt hsq

/-- The reciprocal of any natural power of two is at most one. -/
theorem inv_pow_two_le_one (j : ℕ) : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  exact inv_le_one_of_one_le₀ h1

/-- The reciprocal of any natural power of two is nonnegative. -/
theorem inv_pow_two_nonneg (j : ℕ) : (0 : ℝ) ≤ ((2 : ℝ) ^ j)⁻¹ := by
  positivity

/-- The product of the trigonometric amplification gain and the round-dependent error factor. -/
def roundGain (k : ℕ) (θ : ℝ) : ℝ := ampGain θ * errFactor k

/-- Under the stated positive-angle and small-angle hypotheses, `roundGain k θ` is at least `(3
- (9 / 2) * θ ^ 2) * (1 - ((2 : ℝ) ^ (k + 5))⁻¹)`. -/
theorem roundGain_ge (k : ℕ) (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 2)
    (hsmall : (3 / 2) * θ ^ 2 ≤ 1) :
    (3 - (9 / 2) * θ ^ 2) * (1 - ((2 : ℝ) ^ (k + 5))⁻¹) ≤ roundGain k θ := by
  have hgain : 3 - (9 / 2) * θ ^ 2 ≤ ampGain θ := ampGain_ge θ h0 h1
  have hgain_nn : 0 ≤ 3 - (9 / 2) * θ ^ 2 := by nlinarith
  have herr : 1 - ((2 : ℝ) ^ (k + 5))⁻¹ ≤ errFactor k :=
    sqrt_one_sub_ge _ (inv_pow_two_nonneg (k + 5)) (inv_pow_two_le_one (k + 5))
  have hamp_nn : 0 ≤ ampGain θ := le_trans hgain_nn hgain
  unfold roundGain
  calc (3 - (9 / 2) * θ ^ 2) * (1 - ((2 : ℝ) ^ (k + 5))⁻¹)
      ≤ (3 - (9 / 2) * θ ^ 2) * errFactor k :=
        mul_le_mul_of_nonneg_left herr hgain_nn
    _ ≤ ampGain θ * errFactor k :=
        mul_le_mul_of_nonneg_right hgain (by
          unfold errFactor
          exact Real.sqrt_nonneg _)

/-- Under the stated positive-angle and small-angle hypotheses, the round gain is nonnegative. -/
theorem roundGain_nonneg (k : ℕ) (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 2)
    (hsmall : (3 / 2) * θ ^ 2 ≤ 1) : 0 ≤ roundGain k θ := by
  unfold roundGain
  have hgain_nn : 0 ≤ ampGain θ :=
    le_trans (by nlinarith) (ampGain_ge θ h0 h1)
  have herr : 0 ≤ errFactor k := by
    unfold errFactor
    exact Real.sqrt_nonneg _
  exact mul_nonneg hgain_nn herr

/-- Iterates the assumed amplitude recurrence with nonnegative gains to bound `α m` below by `α
1` times the product of gains from rounds one through `m - 1`, for `m ≥ 1`. -/
theorem amplitude_iterate_ge (α : ℕ → ℝ) (θ : ℕ → ℝ)
    (_hα : 0 < α 1)
    (hrec : ∀ k, α (k + 2) ≥ α (k + 1) * roundGain (k + 1) (θ (k + 1)))
    (hgain : ∀ k, 0 ≤ roundGain (k + 1) (θ (k + 1))) :
    ∀ m, 1 ≤ m →
      α 1 * ∏ k ∈ Finset.range (m - 1), roundGain (k + 1) (θ (k + 1)) ≤ α m := by
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hstep : α (n + 1 + 1) ≥ α (n + 1) * roundGain (n + 1) (θ (n + 1)) := hrec n
    have hprev : α 1 * ∏ k ∈ Finset.range n, roundGain (k + 1) (θ (k + 1)) ≤ α (n + 1) :=
      ih (by omega)
    have hprod : ∏ k ∈ Finset.range (n + 1 + 1 - 1), roundGain (k + 1) (θ (k + 1))
        = (∏ k ∈ Finset.range n, roundGain (k + 1) (θ (k + 1)))
            * roundGain (n + 1) (θ (n + 1)) := by
      rw [show n + 1 + 1 - 1 = n + 1 by omega, Finset.prod_range_succ]
    rw [hprod]
    calc α 1 * ((∏ k ∈ Finset.range n, roundGain (k + 1) (θ (k + 1)))
            * roundGain (n + 1) (θ (n + 1)))
        = (α 1 * ∏ k ∈ Finset.range n, roundGain (k + 1) (θ (k + 1)))
            * roundGain (n + 1) (θ (n + 1)) := by ring
      _ ≤ α (n + 1) * roundGain (n + 1) (θ (n + 1)) :=
          mul_le_mul_of_nonneg_right hprev (hgain n)
      _ ≤ α (n + 1 + 1) := hstep

/-- A nonnegative sequence growing by at most a factor of three per step satisfies `α m ^ 2 ≤ 9
^ (m - 1) * α 1 ^ 2` for `m ≥ 1`. -/
theorem alpha_sq_le (α : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k)
    (hstep : ∀ k, α (k + 1) ≤ 3 * α k) (m : ℕ) (hm : 1 ≤ m) :
    α m ^ 2 ≤ 9 ^ (m - 1) * α 1 ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega]
  clear hm
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : α (n + 1 + 1) ^ 2 ≤ (3 * α (n + 1)) ^ 2 :=
      pow_le_pow_left₀ (hα0 (n + 1 + 1)) (hstep (n + 1)) 2
    have h2 : (3 * α (n + 1)) ^ 2 = 9 * α (n + 1) ^ 2 := by ring
    calc α (n + 1 + 1) ^ 2 ≤ 9 * α (n + 1) ^ 2 := by rw [← h2]; exact h1
      _ ≤ 9 * (9 ^ n * α 1 ^ 2) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = 9 ^ (n + 1) * α 1 ^ 2 := by rw [pow_succ]; ring

/-- The assumed squared-amplitude recurrence implies `β m ^ 2 ≤ β 1 ^ 2 * (9 / 64) ^ (m - 1)`
for `m ≥ 1`. -/
theorem beta_sq_le (β : ℕ → ℝ) (_hβ0 : ∀ k, 0 ≤ β k)
    (hstep : ∀ k, β (k + 1) ^ 2 ≤ (9 / (2 : ℝ) ^ (k + 5)) * β k ^ 2)
    (m : ℕ) (hm : 1 ≤ m) :
    β m ^ 2 ≤ β 1 ^ 2 * (9 / 64) ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega]
  clear hm
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hstep (n + 1)
    have hcoef : 9 / (2 : ℝ) ^ (n + 1 + 5) ≤ 9 / 64 := by
      have hpow : (64 : ℝ) ≤ 2 ^ (n + 1 + 5) := by
        rw [show (64 : ℝ) = 2 ^ 6 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow
    have hβnn : 0 ≤ β (n + 1) ^ 2 := sq_nonneg _
    calc β (n + 1 + 1) ^ 2 ≤ (9 / (2 : ℝ) ^ (n + 1 + 5)) * β (n + 1) ^ 2 := h
      _ ≤ (9 / 64) * β (n + 1) ^ 2 := mul_le_mul_of_nonneg_right hcoef hβnn
      _ ≤ (9 / 64) * (β 1 ^ 2 * (9 / 64) ^ n) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = β 1 ^ 2 * (9 / 64) ^ (n + 1) := by rw [pow_succ]; ring

/-- For `0 ≤ θ ≤ 1`, the squared angle is at most twice the squared sine. -/
theorem theta_sq_le_two_sin_sq (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ ^ 2 ≤ 2 * (Real.sin θ) ^ 2 := by
  rcases lt_or_eq_of_le h0 with hpos | rfl
  · have hgt : θ - θ ^ 3 / 4 < Real.sin θ := by
      linarith [Real.sin_gt_sub_cube hpos, pow_nonneg hpos.le 3]
    have hcube : θ ^ 3 / 4 ≤ θ / 4 := by
      have h3 : θ ^ 3 ≤ θ := by
        calc θ ^ 3 = θ * θ ^ 2 := by ring
          _ ≤ θ * 1 := mul_le_mul_of_nonneg_left (by nlinarith) h0
          _ = θ := by ring
      linarith
    have hlow : 3 * θ / 4 ≤ Real.sin θ := by linarith
    have hsq : (3 * θ / 4) ^ 2 ≤ (Real.sin θ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    nlinarith [hsq]
  · simp

/-- The sum of the first `n` powers of nine is at most `9 ^ n / 8`. -/
theorem geom_sum_nine_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (9 : ℝ) ^ k ≤ 9 ^ n / 8 := by
  rw [geom_sum_eq (by norm_num : (9 : ℝ) ≠ 1) n]
  have h : (0 : ℝ) < 9 ^ n := pow_pos (by norm_num) n
  rw [show (9 : ℝ) - 1 = 8 by norm_num]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
  nlinarith

/-- The sum of the first `n` powers of `9 / 64` is at most `64 / 55`. -/
theorem geom_sum_sixtyfour_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (9 / 64 : ℝ) ^ k ≤ 64 / 55 := by
  rw [geom_sum_eq (by norm_num : (9 / 64 : ℝ) ≠ 1) n]
  have hpos : (0 : ℝ) < (9 / 64 : ℝ) ^ n := pow_pos (by norm_num) n
  have hneg : (9 / 64 : ℝ) - 1 < 0 := by norm_num
  rw [div_le_iff_of_neg hneg]
  nlinarith

/-- The stated bounds on squared amplitudes, together with the sine decomposition and angles in
`[0, 1]`, bound the sum of squared angles through round `m - 1` by `2 * 9 ^ (m - 1) * α 1 ^
2 + 1/4`. -/
theorem sum_theta_sq_le (α β θ : ℕ → ℝ) (m : ℕ)
    (hα : ∀ k, 1 ≤ k → α k ^ 2 ≤ 9 ^ (k - 1) * α 1 ^ 2)
    (hβ : ∀ k, 1 ≤ k → β k ^ 2 ≤ (1 / 10) * (9 / 64) ^ (k - 1))
    (hsin : ∀ k, 1 ≤ k → Real.sin (θ k) ^ 2 = α k ^ 2 + β k ^ 2)
    (hθ0 : ∀ k, 1 ≤ k → 0 ≤ θ k) (hθ1 : ∀ k, 1 ≤ k → θ k ≤ 1) :
    ∑ k ∈ Finset.range (m - 1), θ (k + 1) ^ 2 ≤
      2 * 9 ^ (m - 1) * α 1 ^ 2 + 1 / 4 := by
  have hterm : ∀ k ∈ Finset.range (m - 1),
      θ (k + 1) ^ 2 ≤ 2 * (9 ^ k * α 1 ^ 2) + 2 * ((1 / 10) * (9 / 64) ^ k) := by
    intro k _
    have hk : 1 ≤ k + 1 := by omega
    have hθle : θ (k + 1) ^ 2 ≤ 2 * Real.sin (θ (k + 1)) ^ 2 :=
      theta_sq_le_two_sin_sq (θ (k + 1)) (hθ0 (k + 1) hk) (hθ1 (k + 1) hk)
    rw [hsin (k + 1) hk] at hθle
    have ha := hα (k + 1) hk
    have hb := hβ (k + 1) hk
    rw [show k + 1 - 1 = k by omega] at ha hb
    nlinarith [hθle, ha, hb]
  calc ∑ k ∈ Finset.range (m - 1), θ (k + 1) ^ 2
      ≤ ∑ k ∈ Finset.range (m - 1),
          (2 * (9 ^ k * α 1 ^ 2) + 2 * ((1 / 10) * (9 / 64) ^ k)) :=
        Finset.sum_le_sum hterm
    _ = 2 * α 1 ^ 2 * ∑ k ∈ Finset.range (m - 1), 9 ^ k
          + (1 / 5) * ∑ k ∈ Finset.range (m - 1), (9 / 64) ^ k := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
        · rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
    _ ≤ 2 * α 1 ^ 2 * (9 ^ (m - 1) / 8) + (1 / 5) * (64 / 55) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (geom_sum_nine_le (m - 1)) (by positivity)
        · exact mul_le_mul_of_nonneg_left (geom_sum_sixtyfour_le (m - 1))
            (by norm_num)
    _ ≤ 2 * 9 ^ (m - 1) * α 1 ^ 2 + 1 / 4 := by
        have h9 : (0 : ℝ) ≤ 9 ^ (m - 1) := pow_nonneg (by norm_num) _
        have ha : (0 : ℝ) ≤ α 1 ^ 2 := sq_nonneg _
        nlinarith

/-- For a finite family with each `a i` in `[0, 1]`, the product of `1 - a i` is at least one
minus the sum of the `a i`. -/
theorem prod_one_sub_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have ha0i : 0 ≤ a i := ha0 i (Finset.mem_insert_self i s)
    have ha1i : a i ≤ 1 := ha1 i (Finset.mem_insert_self i s)
    have hs0 : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha0 j (Finset.mem_insert_of_mem hj)
    have hs1 : ∀ j ∈ s, a j ≤ 1 := fun j hj => ha1 j (Finset.mem_insert_of_mem hj)
    have hprod := ih hs0 hs1
    have hsum_nonneg : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg hs0
    have hmul : (1 - a i) * (1 - ∑ j ∈ s, a j) ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
      mul_le_mul_of_nonneg_left hprod (sub_nonneg.2 ha1i)
    nlinarith [hmul, mul_nonneg ha0i hsum_nonneg]

/-- The sum of the first `n` powers of one half is at most two. -/
theorem sum_half_le_two (n : ℕ) :
    ∑ k ∈ Finset.range n, ((1 / 2 : ℝ) ^ k) ≤ 2 := by
  rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) n]
  rw [div_le_iff_of_neg (by norm_num : ((1 / 2 : ℝ) - 1) < 0)]
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  linarith

/-- The sum of the reciprocal powers `2 ^ (k + 6)` for `k < m - 1` is at most `1/32`. -/
theorem sum_inv_pow_two_le (m : ℕ) :
    ∑ k ∈ Finset.range (m - 1), ((2 : ℝ) ^ ((k + 1) + 5))⁻¹ ≤ 1 / 32 := by
  have hterm : ∀ k : ℕ, ((2 : ℝ) ^ ((k + 1) + 5))⁻¹ = (1 / 64) * ((1 / 2) ^ k) := by
    intro k
    rw [show ((k + 1) + 5) = k + 6 by ring, pow_add, mul_inv]
    rw [show ((2 : ℝ) ^ k)⁻¹ = (1 / 2) ^ k by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]]
    norm_num
    ring
  calc ∑ k ∈ Finset.range (m - 1), ((2 : ℝ) ^ ((k + 1) + 5))⁻¹
      = ∑ k ∈ Finset.range (m - 1), (1 / 64) * ((1 / 2) ^ k) :=
        Finset.sum_congr rfl (fun k _ => hterm k)
    _ = (1 / 64) * ∑ k ∈ Finset.range (m - 1), ((1 / 2 : ℝ) ^ k) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / 64) * 2 :=
        mul_le_mul_of_nonneg_left (sum_half_le_two _) (by norm_num)
    _ = 1 / 32 := by norm_num

/-- If the squared angles sum to at most a nonnegative `S` with `(3 / 2) * S ≤ 1`, and each
angle satisfies the stated smallness bound, the product of the explicit lower gain factors
is at least `3 ^ (m - 1) * (1 - (3 / 2) * S - 1/16)`. -/
theorem prod_gainLower_ge (θ : ℕ → ℝ) (m : ℕ) (_hm : 1 ≤ m) (S : ℝ)
    (hθsmall : ∀ k, (3 / 2) * θ (k + 1) ^ 2 ≤ 1)
    (hsum : ∑ k ∈ Finset.range (m - 1), θ (k + 1) ^ 2 ≤ S)
    (hS0 : 0 ≤ S) (hS1 : (3 / 2) * S ≤ 1) :
    3 ^ (m - 1) * (1 - (3 / 2) * S - 1 / 16) ≤
      ∏ k ∈ Finset.range (m - 1),
        ((3 - (9 / 2) * θ (k + 1) ^ 2) * (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹)) := by
  classical
  have hfactor : ∀ k : ℕ,
      (3 - (9 / 2) * θ (k + 1) ^ 2) * (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹)
        = 3 * ((1 - (3 / 2) * θ (k + 1) ^ 2)
            * (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹)) := by
    intro k; ring
  have hprod_split :
      ∏ k ∈ Finset.range (m - 1),
          ((3 - (9 / 2) * θ (k + 1) ^ 2) * (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹))
        = 3 ^ (m - 1)
            * (∏ k ∈ Finset.range (m - 1), (1 - (3 / 2) * θ (k + 1) ^ 2))
            * (∏ k ∈ Finset.range (m - 1), (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹)) := by
    simp only [hfactor]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    ring
  have hA : 1 - ∑ k ∈ Finset.range (m - 1), (3 / 2) * θ (k + 1) ^ 2
      ≤ ∏ k ∈ Finset.range (m - 1), (1 - (3 / 2) * θ (k + 1) ^ 2) := by
    apply prod_one_sub_ge
    · intro k _; exact mul_nonneg (by norm_num) (sq_nonneg _)
    · intro k _; exact hθsmall k
  have hB : 1 - ∑ k ∈ Finset.range (m - 1), ((2 : ℝ) ^ ((k + 1) + 5))⁻¹
      ≤ ∏ k ∈ Finset.range (m - 1), (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹) := by
    apply prod_one_sub_ge
    · intro k _; exact inv_pow_two_nonneg ((k + 1) + 5)
    · intro k _; exact inv_pow_two_le_one ((k + 1) + 5)
  have hA' : 1 - (3 / 2) * S ≤
      ∏ k ∈ Finset.range (m - 1), (1 - (3 / 2) * θ (k + 1) ^ 2) := by
    refine le_trans ?_ hA
    have hsum' : ∑ k ∈ Finset.range (m - 1), (3 / 2) * θ (k + 1) ^ 2
        = (3 / 2) * ∑ k ∈ Finset.range (m - 1), θ (k + 1) ^ 2 := by
      rw [Finset.mul_sum]
    rw [hsum']
    nlinarith [hsum]
  have hB' : 1 - 1 / 16 ≤
      ∏ k ∈ Finset.range (m - 1), (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹) := by
    refine le_trans ?_ hB
    have h := sum_inv_pow_two_le m
    linarith
  rw [hprod_split]
  have h3 : 0 ≤ (3 : ℝ) ^ (m - 1) := by positivity
  have hbase : 0 ≤ 1 - (3 / 2) * S := by linarith
  have hAn : 0 ≤ ∏ k ∈ Finset.range (m - 1), (1 - (3 / 2) * θ (k + 1) ^ 2) :=
    le_trans hbase hA'
  have h16 : (0 : ℝ) ≤ 1 - 1 / 16 := by norm_num
  have hAB : (1 - (3 / 2) * S) * (1 - 1 / 16) ≤
      (∏ k ∈ Finset.range (m - 1), (1 - (3 / 2) * θ (k + 1) ^ 2))
        * (∏ k ∈ Finset.range (m - 1), (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹)) :=
    mul_le_mul hA' hB' h16 hAn
  have hrewrite : 1 - (3 / 2) * S - 1 / 16 ≤ (1 - (3 / 2) * S) * (1 - 1 / 16) := by
    nlinarith [hS0]
  calc 3 ^ (m - 1) * (1 - (3 / 2) * S - 1 / 16)
      ≤ 3 ^ (m - 1) * ((1 - (3 / 2) * S) * (1 - 1 / 16)) :=
        mul_le_mul_of_nonneg_left hrewrite h3
    _ ≤ 3 ^ (m - 1) * ((∏ k ∈ Finset.range (m - 1), (1 - (3 / 2) * θ (k + 1) ^ 2))
          * (∏ k ∈ Finset.range (m - 1), (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹))) :=
        mul_le_mul_of_nonneg_left hAB h3
    _ = 3 ^ (m - 1) * (∏ k ∈ Finset.range (m - 1), (1 - (3 / 2) * θ (k + 1) ^ 2))
          * (∏ k ∈ Finset.range (m - 1), (1 - ((2 : ℝ) ^ ((k + 1) + 5))⁻¹)) := by ring

/-- For `1/90 ≤ s ≤ 1/10`, the expression `Real.sqrt s * (1/2 - 3 * s)` is at least `1/24`. -/
theorem sqrt_mul_factor_ge (s : ℝ) (hlo : 1 / 90 ≤ s) (hhi : s ≤ 1 / 10) :
    (1 / 24 : ℝ) ≤ Real.sqrt s * (1 / 2 - 3 * s) := by
  have hs0 : 0 ≤ s := by linarith
  set w := Real.sqrt s with hw
  have hw2 : w ^ 2 = s := by rw [hw]; exact Real.sq_sqrt hs0
  have h_100_90 : (1 / 100 : ℝ) ≤ s := by linarith
  have h_10_9 : s ≤ (1 / 3 : ℝ) ^ 2 := by linarith
  have hwlo : (1 / 10 : ℝ) ≤ w := by
    rw [hw]
    calc (1 / 10 : ℝ) = Real.sqrt (1 / 100) := by
          rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 10)]
      _ ≤ Real.sqrt s := Real.sqrt_le_sqrt h_100_90
  have hwhi : w ≤ 1 / 3 := by
    rw [hw]
    calc Real.sqrt s ≤ Real.sqrt ((1 / 3 : ℝ) ^ 2) := Real.sqrt_le_sqrt h_10_9
      _ = 1 / 3 := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hw2le : w ^ 2 ≤ w / 3 := by nlinarith [hwlo, hwhi]
  have hquad : 72 * w ^ 2 + (36 / 5) * w - 282 / 25 ≤ 0 := by
    nlinarith [hw2le, hwhi, hwlo]
  have hfac : 72 * w ^ 3 - 12 * w + 1
      = (w - 1 / 10) * (72 * w ^ 2 + (36 / 5) * w - 282 / 25) - 16 / 125 := by
    ring
  have hprod : (w - 1 / 10) * (72 * w ^ 2 + (36 / 5) * w - 282 / 25) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [hwlo]) hquad
  have hcubic : 72 * w ^ 3 - 12 * w + 1 ≤ 0 := by
    rw [hfac]; nlinarith [hprod]
  have htarget : (1 / 24 : ℝ) ≤ w * (1 / 2 - 3 * w ^ 2) := by
    nlinarith [hcubic]
  rw [show s = w ^ 2 from hw2.symm]
  exact htarget

/-- The initialization `α1 ^ 2 = 9 * t / (10 * n)` and scale bounds `9 ^ m * t ≤ n ≤ 9 ^ (m + 1)
* t` imply the stated amplified scalar expression is at least `1/24`, under the positivity
hypotheses. -/
theorem threshold_amplitude_ge (m : ℕ) (hm : 1 ≤ m) (α1 t n : ℝ)
    (hα1 : 0 < α1) (_ht : 0 < t) (hn : 0 < n)
    (hαsq : α1 ^ 2 = 9 * t / (10 * n))
    (hlo : n ≤ 9 ^ (m + 1) * t) (hhi : 9 ^ m * t ≤ n) :
    (1 / 24 : ℝ) ≤ α1 * 3 ^ (m - 1) * (1 / 2 - 3 * 9 ^ (m - 1) * α1 ^ 2) := by
  set s : ℝ := 9 ^ (m - 1) * α1 ^ 2 with hs
  have h9pos : (0 : ℝ) < 9 ^ (m - 1) := by positivity
  have h3pos : (0 : ℝ) < 3 ^ (m - 1) := by positivity
  have h9m : (9 : ℝ) ^ m = 9 ^ (m - 1) * 9 := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  have hsval : 9 ^ (m - 1) * α1 ^ 2 = 9 ^ m * t / (10 * n) := by
    rw [hαsq, h9m]
    ring
  have hden : (0 : ℝ) < 10 * n := by positivity
  have hslo : (1 : ℝ) / 90 ≤ s := by
    rw [hs, hsval, le_div_iff₀ hden]
    have hlo2 : n ≤ 9 ^ m * t * 9 := by
      calc n ≤ 9 ^ (m + 1) * t := hlo
        _ = 9 ^ m * t * 9 := by rw [pow_succ]; ring
    nlinarith [hlo2]
  have hshi : s ≤ 1 / 10 := by
    rw [hs, hsval, div_le_iff₀ hden]
    nlinarith [hhi]
  have h9sq : (9 : ℝ) ^ (m - 1) = (3 ^ (m - 1)) ^ 2 := by
    calc (9 : ℝ) ^ (m - 1) = (3 ^ 2) ^ (m - 1) := by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
      _ = 3 ^ (2 * (m - 1)) := (pow_mul (3 : ℝ) 2 (m - 1)).symm
      _ = 3 ^ ((m - 1) * 2) := by rw [Nat.mul_comm]
      _ = (3 ^ (m - 1)) ^ 2 := pow_mul (3 : ℝ) (m - 1) 2
  have hsqrt_eq : Real.sqrt s = α1 * 3 ^ (m - 1) := by
    rw [hs, Real.sqrt_mul (le_of_lt h9pos), h9sq,
      Real.sqrt_sq (le_of_lt h3pos), Real.sqrt_sq (le_of_lt hα1)]
    ring
  have hmain := sqrt_mul_factor_ge s hslo hshi
  rw [← hsqrt_eq]
  have h3s : 3 * 9 ^ (m - 1) * α1 ^ 2 = 3 * s := by rw [hs]; ring
  rw [h3s]
  exact hmain

/-- The explicit lower gain factor `(3 - (9 / 2) * θ ^ 2) * (1 - ((2 : ℝ) ^ (k + 5))⁻¹)`. -/
def gainLower (k : ℕ) (θ : ℝ) : ℝ := (3 - (9 / 2) * θ ^ 2) * (1 - ((2 : ℝ) ^ (k + 5))⁻¹)

/-- The explicit lower gain factor is nonnegative whenever `(3 / 2) * θ ^ 2 ≤ 1`. -/
theorem gainLower_nonneg (k : ℕ) (θ : ℝ) (hsmall : (3 / 2) * θ ^ 2 ≤ 1) :
    0 ≤ gainLower k θ := by
  unfold gainLower
  have h1 : 0 ≤ 3 - (9 / 2) * θ ^ 2 := by nlinarith
  have h2 : 0 ≤ 1 - ((2 : ℝ) ^ (k + 5))⁻¹ := by linarith [inv_pow_two_le_one (k + 5)]
  exact mul_nonneg h1 h2

/-- The stated initialization, gain recurrence, angle bounds, squared-angle sum bound, and
stopping-scale inequalities imply `α m ≥ 1/24`. -/
theorem amplitude_ge_constant (α : ℕ → ℝ) (θ : ℕ → ℝ) (m : ℕ) (t n : ℝ)
    (hm : 1 ≤ m) (hα1 : 0 < α 1)
    (ht : 0 < t) (hn : 0 < n)
    (hαsq : (α 1) ^ 2 = 9 * t / (10 * n))
    (hrec : ∀ k, α (k + 2) ≥ α (k + 1) * roundGain (k + 1) (θ (k + 1)))
    (hθpos : ∀ k, 0 < θ (k + 1)) (hθle : ∀ k, θ (k + 1) ≤ Real.pi / 2)
    (hθsmall : ∀ k, (3 / 2) * (θ (k + 1)) ^ 2 ≤ 1)
    (hsum : ∑ k ∈ Finset.range (m - 1), (θ (k + 1)) ^ 2
      ≤ 2 * 9 ^ (m - 1) * (α 1) ^ 2 + 1 / 4)
    (hlo : n ≤ 9 ^ (m + 1) * t) (hhi : 9 ^ m * t ≤ n) :
    (1 / 24 : ℝ) ≤ α m := by
  set S : ℝ := 2 * 9 ^ (m - 1) * (α 1) ^ 2 + 1 / 4 with hS
  have hreg : 9 ^ (m - 1) * (α 1) ^ 2 ≤ 1 / 10 := by
    have h9m : (9 : ℝ) ^ m = 9 ^ (m - 1) * 9 := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    have hsval : 9 ^ (m - 1) * (α 1) ^ 2 = 9 ^ m * t / (10 * n) := by
      rw [hαsq, h9m]; ring
    rw [hsval, div_le_iff₀ (by positivity : (0 : ℝ) < 10 * n)]
    nlinarith [hhi]
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hS1 : (3 / 2) * S ≤ 1 := by
    rw [hS]; nlinarith [hreg]
  have hprod := prod_gainLower_ge θ m hm S hθsmall hsum hS0 hS1
  have hgain_le : ∀ k ∈ Finset.range (m - 1),
      gainLower (k + 1) (θ (k + 1)) ≤ roundGain (k + 1) (θ (k + 1)) := by
    intro k _
    exact roundGain_ge (k + 1) (θ (k + 1)) (hθpos k) (hθle k) (hθsmall k)
  have hgain_nn : ∀ k ∈ Finset.range (m - 1),
      0 ≤ gainLower (k + 1) (θ (k + 1)) := by
    intro k _; exact gainLower_nonneg (k + 1) (θ (k + 1)) (hθsmall k)
  have hprod_le : ∏ k ∈ Finset.range (m - 1), gainLower (k + 1) (θ (k + 1))
      ≤ ∏ k ∈ Finset.range (m - 1), roundGain (k + 1) (θ (k + 1)) :=
    Finset.prod_le_prod₀ hgain_nn hgain_le
  have hiter := amplitude_iterate_ge α θ hα1 hrec
    (fun k => roundGain_nonneg (k + 1) (θ (k + 1)) (hθpos k) (hθle k) (hθsmall k))
    m hm
  have hthr := threshold_amplitude_ge m hm (α 1) t n hα1 ht hn hαsq hlo hhi
  have hSval : 1 - (3 / 2) * S - 1 / 16 = 9 / 16 - 3 * 9 ^ (m - 1) * (α 1) ^ 2 := by
    rw [hS]; ring
  have hfac_nn : 0 ≤ α 1 * 3 ^ (m - 1) :=
    mul_nonneg hα1.le (by positivity)
  have hstep1 : α 1 * 3 ^ (m - 1) * (1 / 2 - 3 * 9 ^ (m - 1) * (α 1) ^ 2)
      ≤ α 1 * 3 ^ (m - 1) * (9 / 16 - 3 * 9 ^ (m - 1) * (α 1) ^ 2) :=
    mul_le_mul_of_nonneg_left
      (by linarith : (1 / 2 : ℝ) - 3 * 9 ^ (m - 1) * (α 1) ^ 2
        ≤ 9 / 16 - 3 * 9 ^ (m - 1) * (α 1) ^ 2) hfac_nn
  have hfinal : (1 / 24 : ℝ) ≤ α m := by
    calc (1 / 24 : ℝ) ≤ α 1 * 3 ^ (m - 1) * (1 / 2 - 3 * 9 ^ (m - 1) * (α 1) ^ 2) :=
          hthr
      _ ≤ α 1 * 3 ^ (m - 1) * (9 / 16 - 3 * 9 ^ (m - 1) * (α 1) ^ 2) := hstep1
      _ = α 1 * (3 ^ (m - 1) * (9 / 16 - 3 * 9 ^ (m - 1) * (α 1) ^ 2)) := by ring
      _ = α 1 * (3 ^ (m - 1) * (1 - (3 / 2) * S - 1 / 16)) := by rw [hSval]
      _ ≤ α 1 * ∏ k ∈ Finset.range (m - 1), gainLower (k + 1) (θ (k + 1)) :=
          mul_le_mul_of_nonneg_left hprod hα1.le
      _ ≤ α 1 * ∏ k ∈ Finset.range (m - 1), roundGain (k + 1) (θ (k + 1)) :=
          mul_le_mul_of_nonneg_left hprod_le hα1.le
      _ ≤ α m := hiter
  exact hfinal

/-- The stated initial amplitudes, amplitude recurrences, sine decomposition, angle bounds, and
stopping-scale inequalities imply `α m ≥ 1/24`. This supplies the conditional scalar
amplitude threshold used in the bounded-error search analysis of [HoyerMoscaDeWolf2003]. -/
theorem src_amplitude_ge_constant (α β θ : ℕ → ℝ) (m : ℕ) (t n : ℝ)
    (hm : 1 ≤ m) (ht : 0 < t) (hn : 0 < n)
    (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hβ1sq : β 1 ^ 2 ≤ 1 / 10)
    (hα1sq : α 1 ^ 2 = 9 * t / (10 * n))
    (hαstep : ∀ k, α (k + 1) ≤ 3 * α k)
    (hβstep : ∀ k, β (k + 1) ^ 2 ≤ (9 / (2 : ℝ) ^ (k + 5)) * β k ^ 2)
    (hrec : ∀ k, α (k + 2) ≥ α (k + 1) * roundGain (k + 1) (θ (k + 1)))
    (hθpos : ∀ k, 0 < θ (k + 1)) (hθle : ∀ k, θ (k + 1) ≤ Real.pi / 2)
    (hθsmall : ∀ k, (3 / 2) * (θ (k + 1)) ^ 2 ≤ 1)
    (hsin : ∀ k, Real.sin (θ (k + 1)) ^ 2 = α (k + 1) ^ 2 + β (k + 1) ^ 2)
    (hlo : n ≤ 9 ^ (m + 1) * t) (hhi : 9 ^ m * t ≤ n) :
    (1 / 24 : ℝ) ≤ α m := by
  have hα1 : 0 < α 1 := by
    have hsqpos : 0 < α 1 ^ 2 := by rw [hα1sq]; positivity
    have hne : α 1 ≠ 0 := by
      intro hzero
      rw [hzero] at hsqpos
      simp at hsqpos
    exact lt_of_le_of_ne (hα0 1) (Ne.symm hne)
  have hθ1 : ∀ k, 1 ≤ k → θ k ≤ 1 := by
    intro k hk
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hpos : 0 < θ k := by simpa [hk'] using hθpos (k - 1)
    have hsmall : (3 / 2) * θ k ^ 2 ≤ 1 := by simpa [hk'] using hθsmall (k - 1)
    nlinarith [hpos, hsmall, sq_nonneg (θ k - 1), sq_nonneg (θ k)]
  have hαsum : ∀ k, 1 ≤ k → α k ^ 2 ≤ 9 ^ (k - 1) * α 1 ^ 2 :=
    alpha_sq_le α hα0 hαstep
  have hβsum : ∀ k, 1 ≤ k → β k ^ 2 ≤ (1 / 10) * (9 / 64) ^ (k - 1) := by
    intro k hk
    have h := beta_sq_le β hβ0 hβstep k hk
    have hpow : (0 : ℝ) ≤ (9 / 64) ^ (k - 1) := pow_nonneg (by norm_num) _
    nlinarith [h, hβ1sq, hpow]
  have hsum := sum_theta_sq_le α β θ m hαsum hβsum
    (fun k hk => by
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
      simpa [hk'] using hsin (k - 1))
    (fun k hk => by
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
      simpa [hk'] using le_of_lt (hθpos (k - 1)))
    hθ1
  exact amplitude_ge_constant α θ m t n hm hα1 ht hn hα1sq hrec hθpos hθle
    hθsmall hsum hlo hhi

/-- An amplitude at least `1/24` has square at least `1/576`. -/
theorem success_probability_ge (α : ℕ → ℝ) (m : ℕ) (h : (1 / 24 : ℝ) ≤ α m) :
    (1 / 576 : ℝ) ≤ α m ^ 2 := by
  have h0 : 0 ≤ α m := le_trans (by norm_num) h
  have hmul : (1 / 24 : ℝ) * (1 / 24) ≤ α m * α m :=
    mul_le_mul h h (by norm_num) h0
  nlinarith [hmul]

end Qatlib.Papers.BndErrSearch03.MainResults.BoundedErrorSearchAmplification
