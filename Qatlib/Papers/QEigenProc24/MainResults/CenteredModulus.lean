/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QEigenProc24.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# QEigenProc24 — centered modulus and trigonometric bounds

Fixed source: arXiv:2401.06240v3.

* Lemma 15 (Eqs. (164)–(168), p. 44): the five properties of
  `CMod_q(x) = x - q⌊(x + q/2)/q⌋` — periodicity, boundedness, negation, positive scaling and
  the triangle inequality.
* Lemma 16 (Eqs. (169)–(170), p. 45): `|sin x| ≥ (2/π)|CMod_π x|` and
  `|cos x - cos y| ≤ |CMod_{2π}(x - y)|`.

Reused FQNs: `Int.floor_le`, `Int.lt_floor_add_one`, `Int.floor_eq_iff`,
`Int.floor_add_intCast`, `Int.floor_intCast` (`Mathlib/Algebra/Order/Floor/Ring.lean`);
`le_div_iff₀`, `div_lt_iff₀` (`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean`);
`Real.abs_cos_sub_cos_le`, `Real.mul_abs_le_abs_sin`
(`Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`);
`Real.cos_add_int_mul_two_pi`, `Real.sin_add_int_mul_pi`
(`.../Trigonometric/Basic.lean`).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Real

namespace Qatlib.Papers.QEigenProc24.MainResults.CenteredModulus

open Qatlib.Papers.QEigenProc24.MainResults

/-! ## Elementary bounds on `cmod` -/

/-- `CMod_q x` lies in `[-q/2, q/2)` for `q > 0` (definition after Eq. (164), p. 44). -/
theorem abs_cmod_le_half (q x : ℝ) (hq : 0 < q) : |cmod q x| ≤ q / 2 := by
  unfold cmod
  set m : ℤ := ⌊(x + q / 2) / q⌋ with hm
  have hle : (m : ℝ) ≤ (x + q / 2) / q := by
    rw [hm]; exact Int.floor_le _
  have hlt : (x + q / 2) / q < (m : ℝ) + 1 := by
    rw [hm]; exact Int.lt_floor_add_one _
  have hm1 : (m : ℝ) * q ≤ x + q / 2 := (le_div_iff₀ hq).mp hle
  have hm2 : x + q / 2 < ((m : ℝ) + 1) * q := (div_lt_iff₀ hq).mp hlt
  rw [abs_le]
  constructor <;> linarith

/-- The floor shift identity behind periodicity: shifting `x` by `l q` shifts the floor by `l`. -/
theorem floor_shift (q x : ℝ) (hq : q ≠ 0) (l : ℤ) :
    ⌊(x + (l : ℝ) * q + q / 2) / q⌋ = ⌊(x + q / 2) / q⌋ + l := by
  have h : (x + (l : ℝ) * q + q / 2) / q = (x + q / 2) / q + (l : ℝ) := by
    rw [show x + (l : ℝ) * q + q / 2 = (x + q / 2) + (l : ℝ) * q by ring, add_div,
      mul_div_cancel_right₀ (l : ℝ) hq]
  rw [h, Int.floor_add_intCast]

/-! ## Lemma 15 — properties of the centered modulus (p. 44) -/

/-- **Lemma 15.1 (Periodicity, Eq. (165), p. 44).**  `CMod_q(x + l q) = CMod_q x` for `l ∈ ℤ`. -/
theorem cmod_add_int_mul (q x : ℝ) (hq : q ≠ 0) (l : ℤ) :
    cmod q (x + (l : ℝ) * q) = cmod q x := by
  unfold cmod
  rw [floor_shift q x hq l]
  push_cast
  ring

/-- **Lemma 15.2 (Boundedness, p. 44).**  `|CMod_q x| ≤ |x|` for `q > 0`. -/
theorem abs_cmod_le_abs (q x : ℝ) (hq : 0 < q) : |cmod q x| ≤ |x| := by
  unfold cmod
  set m : ℤ := ⌊(x + q / 2) / q⌋ with hm
  rcases le_or_gt (q / 2) |x| with h | h
  · exact (abs_cmod_le_half q x hq).trans h
  · have hx : -(q / 2) < x ∧ x < q / 2 := abs_lt.mp h
    have h0 : (0 : ℝ) ≤ (x + q / 2) / q :=
      div_nonneg (by linarith [hx.1]) (le_of_lt hq)
    have h1' : (x + q / 2) / q < 1 := by
      rw [div_lt_one hq]; linarith [hx.2]
    have hm0 : m = 0 := by
      rw [hm]
      exact Int.floor_eq_zero_iff.mpr ⟨h0, h1'⟩
    rw [hm0]
    push_cast
    rw [mul_zero, sub_zero]

/-- **Lemma 15.3 (Negation, Eq. (165), p. 44).**  `|CMod_q(-x)| = |CMod_q x|`.

The source splits on whether `(x + q/2)/q` is an integer; in the integer case both centered
moduli equal `-q/2`, otherwise `CMod_q(-x) = -CMod_q x`. -/
theorem abs_cmod_neg (q x : ℝ) (hq : 0 < q) : |cmod q (-x)| = |cmod q x| := by
  have hqne : q ≠ 0 := ne_of_gt hq
  set y : ℝ := (x + q / 2) / q with hy
  set m : ℤ := ⌊y⌋ with hm
  set y' : ℝ := (-x + q / 2) / q with hy'
  set m' : ℤ := ⌊y'⌋ with hm'
  have hyq : q * y = x + q / 2 := by
    rw [hy, mul_comm, div_mul_cancel₀ _ hqne]
  have hy'rel : y' = 1 - y := by
    rw [hy', hy, div_eq_iff hqne]
    nlinarith [hyq]
  have hcmx : cmod q x = x - q * (m : ℝ) := by
    unfold cmod
    rw [← hy, ← hm]
  have hcmnx : cmod q (-x) = -x - q * (m' : ℝ) := by
    unfold cmod
    rw [← hy', ← hm']
  by_cases hint : ∃ z : ℤ, y = (z : ℝ)
  · obtain ⟨z, hz⟩ := hint
    have hmz : m = z := by
      rw [hm, hz, Int.floor_intCast]
    have hm'z : m' = 1 - z := by
      rw [hm', hy'rel, hz]
      have hcast : (1 : ℝ) - (z : ℝ) = ((1 - z : ℤ) : ℝ) := by
        push_cast; ring
      rw [hcast, Int.floor_intCast]
    have hxq : x = q * (z : ℝ) - q / 2 := by
      rw [hz] at hyq
      linarith
    have hnxq : -x = q * (1 - (z : ℝ)) - q / 2 := by linarith
    rw [hcmx, hcmnx, hmz, hm'z, hnxq, hxq]
    push_cast
    congr 1
    ring
  · have hle : (m : ℝ) ≤ y := by
      rw [hm]; exact Int.floor_le y
    have hne : (m : ℝ) ≠ y := fun hh => hint ⟨m, hh.symm⟩
    have hmy : (m : ℝ) < y := lt_of_le_of_ne hle hne
    have hmy' : y < (m : ℝ) + 1 := by
      rw [hm]; exact Int.lt_floor_add_one y
    have hm'_val : m' = -m := by
      rw [hm']
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · rw [hy'rel]; push_cast; linarith
      · rw [hy'rel]; push_cast; linarith
    rw [hcmnx, hcmx, hm'_val]
    have hEq : -x - q * ((-m : ℤ) : ℝ) = -(x - q * (m : ℝ)) := by
      push_cast
      ring
    rw [hEq, abs_neg]

/-- **Lemma 15.4 (Positive scaling, Eq. (166), p. 44).**  `CMod_q(c x) = c CMod_{q/c}(x)` for
`c > 0`. -/
theorem cmod_scale (q x c : ℝ) (hc : 0 < c) (hq : 0 < q) :
    cmod q (c * x) = c * cmod (q / c) x := by
  unfold cmod
  have hqne : q ≠ 0 := ne_of_gt hq
  have hcne : c ≠ 0 := ne_of_gt hc
  have hqc : q / c ≠ 0 := ne_of_gt (div_pos hq hc)
  have harg : (c * x + q / 2) / q = (x + q / c / 2) / (q / c) := by
    rw [div_eq_div_iff hqne hqc]
    field_simp
  rw [harg, mul_sub, ← mul_assoc, mul_comm c (q / c), div_mul_cancel₀ q hcne]

/-- **Lemma 15.5 (Triangle inequality, Eq. (167)–(168), p. 44).**
`|CMod_q(x + y)| ≤ |CMod_q x| + |CMod_q y|` for `q > 0`. -/
theorem abs_cmod_add_le (q x y : ℝ) (hq : 0 < q) :
    |cmod q (x + y)| ≤ |cmod q x| + |cmod q y| := by
  set mx : ℤ := ⌊(x + q / 2) / q⌋ with hmx
  set my : ℤ := ⌊(y + q / 2) / q⌋ with hmy
  have hxrep : x = cmod q x + (mx : ℝ) * q := by
    unfold cmod; rw [← hmx]; ring
  have hyrep : y = cmod q y + (my : ℝ) * q := by
    unfold cmod; rw [← hmy]; ring
  have hxy : x + y = (cmod q x + cmod q y) + ((mx + my : ℤ) : ℝ) * q := by
    conv_lhs => rw [hxrep, hyrep]
    push_cast; ring
  have hval : cmod q (x + y) = cmod q (cmod q x + cmod q y) := by
    rw [hxy]
    exact cmod_add_int_mul q (cmod q x + cmod q y) (ne_of_gt hq) (mx + my)
  rw [hval]
  exact (abs_cmod_le_abs q _ hq).trans (abs_add_le _ _)

/-! ## Lemma 16 — trigonometric bounds (p. 45) -/

/-- **Lemma 16.1 (Eq. (169), p. 45).**  `|sin x| ≥ (2/π)|CMod_π x|`.

Source proof: write `x = kπ + r` with `|r| ≤ π/2`; then `sin x = ±sin r`, and Jordan's
inequality `sin r ≥ (2/π) r` on `[0, π/2]` gives the bound. -/
theorem sin_ge_two_div_pi_cmod (x : ℝ) :
    2 / π * |cmod π x| ≤ |Real.sin x| := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set m : ℤ := ⌊(x + π / 2) / π⌋ with hm
  have hr : |cmod π x| ≤ π / 2 := abs_cmod_le_half π x hpi
  have hx : x = cmod π x + (m : ℝ) * π := by
    unfold cmod; rw [← hm]; ring
  have hsin : Real.sin x = (-1 : ℝ) ^ m * Real.sin (cmod π x) := by
    nth_rewrite 1 [hx]
    simpa [add_comm, mul_comm] using Real.sin_add_int_mul_pi (cmod π x) m
  rw [hsin, abs_mul]
  have hsign : |(-1 : ℝ) ^ m| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  rw [hsign, one_mul]
  exact Real.mul_abs_le_abs_sin hr

/-- **Lemma 16.2 (Eq. (170), p. 45).**  `|cos x - cos y| ≤ |CMod_{2π}(x - y)|`.

Source proof: reduce `y` modulo `2π` (`cos` is `2π`-periodic), then use that `cos` is
1-Lipschitz. -/
theorem abs_cos_sub_cos_le_cmod (x y : ℝ) :
    |Real.cos x - Real.cos y| ≤ |cmod (2 * π) (x - y)| := by
  have hq : (0 : ℝ) < 2 * π := by positivity
  set d : ℝ := x - y with hd
  set k : ℤ := ⌊(d + 2 * π / 2) / (2 * π)⌋ with hk
  have hperp : Real.cos y = Real.cos (y + (k : ℝ) * (2 * π)) := by
    rw [Real.cos_add_int_mul_two_pi]
  have harg : y + (k : ℝ) * (2 * π) = x - cmod (2 * π) d := by
    unfold cmod
    rw [← hk]
    rw [hd]
    ring
  calc |Real.cos x - Real.cos y|
      = |Real.cos x - Real.cos (x - cmod (2 * π) d)| := by rw [hperp, harg]
    _ ≤ |x - (x - cmod (2 * π) d)| := Real.abs_cos_sub_cos_le _ _
    _ = |cmod (2 * π) d| := by
        rw [show x - (x - cmod (2 * π) d) = cmod (2 * π) d by ring]
    _ = |cmod (2 * π) (x - y)| := by rw [hd]

end Qatlib.Papers.QEigenProc24.MainResults.CenteredModulus
