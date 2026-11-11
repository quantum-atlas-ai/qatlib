/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KDistinctness11.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# KDistinctness11 — the exponent schedule of §5.3

Belovs–Lee, *Quantum Algorithm for k-distinctness with Prior Knowledge on the Input*,
arXiv:1108.3022v1, Section 5.3 ("Parameters", pp. 15–16).

The paper writes `ρ i = log_n r i`, derives
`ρ i - ρ (i+1) = (ρ (i-1) - ρ i) / 2` from the requirement that all addends of the
complexity estimate are equal, and with `ρ 0 = 1`, `ρ k = 1/2` obtains
`ρ 1 = 1 - 2^{k-2}/(2^k - 1)`.  We record that closed form and prove the two
asymptotic facts used in Proposition 18.

The closed form is stated with `2^k / 4` in place of `2^{k-2}` so that it is also
correct at `k = 1` (where natural-number subtraction would truncate).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KDistinctness11.MainResults

open Filter Asymptotics

open scoped BigOperators ENNReal Topology

/-- The optimal exponent schedule of §5.3:
`ρ i = 1 - (2^{k-2}/(2^k-1)) · (2 - 2^{1-i})`. -/
def rho (k i : ℕ) : ℝ :=
  1 - (((2 : ℝ) ^ k / 4) / ((2 : ℝ) ^ k - 1)) * (2 - (2 : ℝ) / (2 : ℝ) ^ i)

/-- The optimal exponent of Theorem 1: `ρ 1 = 1 - 2^{k-2}/(2^k - 1)`. -/
def mainExponent (k : ℕ) : ℝ :=
  1 - ((2 : ℝ) ^ k / 4) / ((2 : ℝ) ^ k - 1)

/-- The coefficient `2^{k-2}/(2^k-1)` of the schedule. -/
def rhoCoef (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k / 4) / ((2 : ℝ) ^ k - 1)

/-- The rho eq property in the paper model. -/
theorem rho_eq (k i : ℕ) : rho k i = 1 - rhoCoef k * (2 - 2 / (2 : ℝ) ^ i) := rfl

/-- The rho zero property in the paper model. -/
theorem rho_zero (k : ℕ) : rho k 0 = 1 := by
  simp [rho]

/-- The rho one property in the paper model. -/
theorem rho_one (k : ℕ) : rho k 1 = mainExponent k := by
  simp only [rho, mainExponent]
  norm_num

/-- `0 < 2^k - 1` for `k ≥ 1`. -/
theorem two_pow_sub_one_pos {k : ℕ} (hk : 1 ≤ k) : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by
  have h : (1 : ℝ) < (2 : ℝ) ^ k := one_lt_pow₀ (by norm_num) (by omega)
  linarith

/-- `ρ 1 < 1`. -/
theorem rho_one_lt_one {k : ℕ} (hk : 1 ≤ k) : mainExponent k < 1 := by
  have hpos : 0 < rhoCoef k := by
    unfold rhoCoef
    exact div_pos (by positivity) (two_pow_sub_one_pos hk)
  simp only [mainExponent, rhoCoef] at hpos ⊢
  linarith

/-- The coefficient exceeds `1/4` for `k ≥ 1`. -/
theorem rhoCoef_gt_quarter {k : ℕ} (hk : 1 ≤ k) : 1 / 4 < rhoCoef k := by
  have hx : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hx1 : (0 : ℝ) < (2 : ℝ) ^ k - 1 := two_pow_sub_one_pos hk
  unfold rhoCoef
  rw [div_lt_div_iff₀ (by norm_num) hx1]
  nlinarith

/-- `ρ 1 < 3/4` (§5.3, used in the proof of Proposition 18). -/
theorem rho_one_lt_three_quarters {k : ℕ} (hk : 1 ≤ k) : mainExponent k < 3 / 4 := by
  have hc := rhoCoef_gt_quarter hk
  simp only [mainExponent, rhoCoef] at hc ⊢
  linarith

/-- `ρ 2 < 5/8` (§5.3, used in the proof of Proposition 18). -/
theorem rho_two_lt_five_eighths {k : ℕ} (hk : 1 ≤ k) : rho k 2 < 5 / 8 := by
  have hc := rhoCoef_gt_quarter hk
  simp only [rhoCoef] at hc
  simp only [rho]
  norm_num
  linarith

/-- `ρ k = 1/2`, i.e. the right endpoint of the recurrence. -/
theorem rho_last (k : ℕ) (hk : 1 ≤ k) : rho k k = 1 / 2 := by
  have hx : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hx1 : (2 : ℝ) ^ k - 1 ≠ 0 := ne_of_gt (two_pow_sub_one_pos hk)
  simp only [rho]
  field_simp
  ring

/-- The exponent schedule is antitone in the stage index. -/
theorem rho_antitone (k : ℕ) : Antitone (rho k) := by
  intro a b hab
  simp only [rho]
  have hpow : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b := by
    gcongr <;> norm_num
  have hstep : 2 / (2 : ℝ) ^ b ≤ 2 / (2 : ℝ) ^ a := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact hpow
  have hcoef : 0 ≤ ((2 : ℝ) ^ k / 4) / ((2 : ℝ) ^ k - 1) := by
    apply div_nonneg (by positivity)
    have : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hA : 2 - 2 / (2 : ℝ) ^ a ≤ 2 - 2 / (2 : ℝ) ^ b := by linarith
  have hmul := mul_le_mul_of_nonneg_left hA hcoef
  linarith

/-- `ρ i ≥ 1/2` for every stage `i ≤ k` (§5.3). -/
theorem rho_ge_half {k i : ℕ} (hi : i ≤ k) : 1 / 2 ≤ rho k i := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : i = 0 := by omega
    subst this
    rw [rho_zero]
    norm_num
  · have hlast : rho k k = 1 / 2 := rho_last k hk
    calc 1 / 2 = rho k k := hlast.symm
      _ ≤ rho k i := rho_antitone k hi

/-! ## Asymptotics of real powers -/

/-- If `a < b` then `n^a = o(n^b)` along the naturals. -/
theorem isLittleO_natCast_rpow {a b : ℝ} (h : a < b) :
    (fun n : ℕ => (n : ℝ) ^ a) =o[atTop] (fun n : ℕ => (n : ℝ) ^ b) := by
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn hzero
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    exact absurd hzero (ne_of_gt (Real.rpow_pos_of_pos hn0 b))
  · have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop (𝓝 0) := by
      have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      convert (tendsto_rpow_neg_atTop (show 0 < b - a by linarith)).comp hcast using 1
      ext n
      simp only [Function.comp_apply, neg_sub]
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    rw [Real.rpow_sub hn0]

/-- `√(n^a · n^b) = n^{(a+b)/2}` eventually. -/
theorem eventually_sqrt_rpow_mul (a b : ℝ) :
    (fun n : ℕ => Real.sqrt ((n : ℝ) ^ a * (n : ℝ) ^ b)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((a + b) / 2)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  rw [← Real.rpow_add hn0 a b, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
  congr 1
  ring

/-- `√(n^a) = n^{a/2}` eventually. -/
theorem eventually_sqrt_rpow (a : ℝ) :
    (fun n : ℕ => Real.sqrt ((n : ℝ) ^ a)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a / 2)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
  congr 1
  ring

/-- Product of two powers: `n^a · n^b = n^{a+b}` eventually. -/
theorem eventually_rpow_mul (a b : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ b) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a + b)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  exact (Real.rpow_add hn0 a b).symm

/-- Proposition 18 (first asymptotic fact): `√r 1 · r 2 = o(n)`. -/
theorem prop18_sqrt_r1_mul_r2 {k : ℕ} (hk : 1 ≤ k) :
    (fun n : ℕ => Real.sqrt ((n : ℝ) ^ rho k 1) * (n : ℝ) ^ rho k 2) =o[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have h1' : rho k 1 < 3 / 4 := by
    rw [rho_one]
    exact rho_one_lt_three_quarters hk
  have hlt : rho k 1 / 2 + rho k 2 < 1 := by
    have h2 := rho_two_lt_five_eighths hk
    linarith
  have hceil : (fun n : ℕ => (n : ℝ) ^ (rho k 1 / 2 + rho k 2)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := isLittleO_natCast_rpow hlt
  have e1 := eventually_sqrt_rpow (rho k 1)
  have e2 := eventually_rpow_mul (rho k 1 / 2) (rho k 2)
  refine (hceil.congr' ?_ ?_)
  · filter_upwards [e1, e2] with n h1 h2
    rw [h1, h2]
  · filter_upwards with n
    rw [Real.rpow_one]

/-- Proposition 18 (second asymptotic fact): `√r 1 = o(r i)` for every `1 ≤ i ≤ k`. -/
theorem prop18_sqrt_r1_isLittleO {k i : ℕ} (hk : 1 ≤ k) (hi : 1 ≤ i) (_hik : i ≤ k) :
    (fun n : ℕ => Real.sqrt ((n : ℝ) ^ rho k 1)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ rho k i) := by
  have hlt : rho k 1 / 2 < rho k i := by
    have h1 : rho k 1 < 1 := by
      rw [rho_one]
      exact rho_one_lt_one hk
    rcases eq_or_lt_of_le hi with hi1 | hi2
    · subst hi1
      have hpos := rho_ge_half (k := k) (i := 1) (by omega)
      linarith
    · have := rho_ge_half (k := k) (i := i) (by omega)
      linarith
  have hceil : (fun n : ℕ => (n : ℝ) ^ (rho k 1 / 2)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ rho k i) := isLittleO_natCast_rpow hlt
  exact hceil.congr' (eventually_sqrt_rpow (rho k 1)).symm EventuallyEq.rfl

end Qatlib.Papers.KDistinctness11.MainResults
