/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Planar amplitude amplification

This module models amplitude amplification by two reflections on `AmplState` and derives the
exact iterates and success probability of `groverStep`. The rounded iteration count `amplIters`
gives the success and query bounds used for amplified impatient learning in [HunzikerEtAl2003].

## Main statements

* `groverStep_iterate`: Exact trigonometric formula for repeated amplification.
* `amplified_success_prob`: Success probability at least max(1 - s², s²).
* `amplified_query_bound`: An explicit query bound proportional to 1/s.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Real

/-- The real two-dimensional space of amplitudes used in the planar amplification model. -/
abbrev AmplState : Type := ℝ × ℝ

/-- The map x ↦ 2⟨v, x⟩v - x on the real plane, which is reflection in the line spanned by `v`
when `v` has unit length. -/
noncomputable def planeRefl (v : AmplState) (x : AmplState) : AmplState :=
  (2 * (v.1 * x.1 + v.2 * x.2) * v.1 - x.1,
   2 * (v.1 * x.1 + v.2 * x.2) * v.2 - x.2)

/-- One amplification step, obtained by reflecting in the first coordinate axis and then in the
line through (sin θ, cos θ). -/
noncomputable def groverStep (θ : ℝ) (x : AmplState) : AmplState :=
  planeRefl (Real.sin θ, Real.cos θ) (planeRefl (1, 0) x)

/-- Reflection in the first coordinate axis preserves the first coordinate and negates the
second. -/
lemma refl_target (x : AmplState) : planeRefl (1, 0) x = (x.1, -x.2) := by
  apply Prod.ext <;> simp [planeRefl] <;> ring

/-- The coordinate formula for `groverStep θ` in terms of cos(2θ) and sin(2θ). -/
lemma groverStep_apply (θ : ℝ) (x : AmplState) :
    groverStep θ x
      = (-(Real.cos (2 * θ) * x.1) - Real.sin (2 * θ) * x.2,
         Real.sin (2 * θ) * x.1 - Real.cos (2 * θ) * x.2) := by
  rw [groverStep, refl_target]
  apply Prod.ext
  · simp only [planeRefl, Real.sin_two_mul, Real.cos_two_mul]
    linear_combination (2 * x.1) * Real.sin_sq_add_cos_sq θ
  · simp only [planeRefl, Real.sin_two_mul, Real.cos_two_mul]
    ring

/-- One amplification step preserves the sum of the squared coordinates. -/
lemma groverStep_norm (θ : ℝ) (x : AmplState) :
    (groverStep θ x).1 ^ 2 + (groverStep θ x).2 ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  rw [groverStep_apply]
  nlinarith [Real.sin_sq_add_cos_sq (2 * θ)]

/-- After `m` amplification steps, the initial amplitudes are (-1)^m times (sin((2m + 1)θ),
cos((2m + 1)θ)). This gives the iteration formula used in [HunzikerEtAl2003]. -/
theorem groverStep_iterate (θ : ℝ) (m : ℕ) :
    (groverStep θ)^[m] (Real.sin θ, Real.cos θ)
      = ((-1 : ℝ) ^ m * Real.sin (((2 * m + 1 : ℕ) : ℝ) * θ),
         (-1 : ℝ) ^ m * Real.cos (((2 * m + 1 : ℕ) : ℝ) * θ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, groverStep_apply]
      have hcast : (((2 * (m + 1) + 1 : ℕ)) : ℝ) * θ
          = (((2 * m + 1 : ℕ)) : ℝ) * θ + 2 * θ := by
        push_cast
        ring
      rw [hcast, Real.sin_add, Real.cos_add, pow_succ]
      apply Prod.ext <;> ring

/-- The success probability sin²((2m + 1)θ) after `m` amplification steps. -/
noncomputable def successProb (θ : ℝ) (m : ℕ) : ℝ :=
  (Real.sin (((2 * m + 1 : ℕ) : ℝ) * θ)) ^ 2

/-- The squared first coordinate after `m` amplification steps equals `successProb θ m`, as used
in [HunzikerEtAl2003]. -/
theorem groverStep_prob (θ : ℝ) (m : ℕ) :
    ((groverStep θ)^[m] (Real.sin θ, Real.cos θ)).1 ^ 2 = successProb θ m := by
  rw [groverStep_iterate, successProb, mul_pow]
  have h : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, show m * 2 = 2 * m by ring, pow_mul]
    norm_num
  rw [h, one_mul]

/-- If 0 < θ ≤ π/2 and x is within θ of π/2, then sin² x is at least cos² θ. -/
theorem sin_sq_ge_cos_sq_of_close {θ x : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ π / 2)
    (hx : |x - π / 2| ≤ θ) : Real.cos θ ^ 2 ≤ Real.sin x ^ 2 := by
  have hx1 : π / 2 - θ ≤ x := by
    have := (abs_le.mp hx).1
    linarith
  have hx2 : x ≤ π / 2 + θ := by
    have := (abs_le.mp hx).2
    linarith
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hθ2
  have haux : Real.cos θ ≤ Real.sin x := by
    rcases le_or_gt x (π / 2) with hle | hlt
    · have h1 : Real.sin (π / 2 - θ) ≤ Real.sin x :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hle (by linarith)
      rwa [Real.sin_pi_div_two_sub] at h1
    · have h1 : Real.sin (π / 2 - θ) ≤ Real.sin (π - x) := by
        refine Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
      rwa [Real.sin_pi_div_two_sub, Real.sin_pi_sub] at h1
  exact pow_le_pow_left₀ hcos haux 2

/-- If the amplified angle is within θ of π/2, then the success probability is at least 1 - sin²
θ. -/
theorem successProb_ge_one_sub_sq {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ π / 2) {m : ℕ}
    (hm : |(((2 * m + 1 : ℕ) : ℝ) * θ - π / 2)| ≤ θ) :
    1 - Real.sin θ ^ 2 ≤ successProb θ m := by
  unfold successProb
  have h : Real.cos θ ^ 2 ≤ Real.sin ((((2 * m + 1 : ℕ) : ℝ) * θ)) ^ 2 :=
    sin_sq_ge_cos_sq_of_close hθ0 hθ2 hm
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The natural-number iteration count obtained by rounding π/(4θ) - 1/2 and converting the
result with `Int.toNat`. -/
noncomputable def amplIters (θ : ℝ) : ℕ :=
  (round (π / (4 * θ) - 1 / 2)).toNat

/-- For 0 < θ ≤ π/2, the angle selected by `amplIters θ` is within θ of π/2, as required for
amplification in [HunzikerEtAl2003]. -/
lemma amplIters_close {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ π / 2) :
    |(((2 * amplIters θ + 1 : ℕ) : ℝ) * θ - π / 2)| ≤ θ := by
  have h4θ : (0 : ℝ) < 4 * θ := by linarith
  have hc0 : 0 ≤ π / (4 * θ) - 1 / 2 := by
    rw [sub_nonneg, le_div_iff₀ h4θ]
    linarith
  have hround : |π / (4 * θ) - 1 / 2 - (round (π / (4 * θ) - 1 / 2) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  have hr0 : (0 : ℤ) ≤ round (π / (4 * θ) - 1 / 2) := by
    have h := (abs_le.mp hround).2
    have : (-1 : ℝ) < (round (π / (4 * θ) - 1 / 2) : ℝ) := by linarith
    have h2 : (-1 : ℤ) < round (π / (4 * θ) - 1 / 2) := by exact_mod_cast this
    omega
  have hcast : ((amplIters θ : ℕ) : ℤ) = round (π / (4 * θ) - 1 / 2) := by
    rw [amplIters, Int.toNat_of_nonneg hr0]
  have hcastR : ((amplIters θ : ℕ) : ℝ) = (round (π / (4 * θ) - 1 / 2) : ℝ) := by
    rw [← hcast]
    push_cast
    rfl
  have hcast2 : (((2 * amplIters θ + 1 : ℕ)) : ℝ) = 2 * (round (π / (4 * θ) - 1 / 2) : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hcastR]
  rw [hcast2]
  have hmul : (2 * (round (π / (4 * θ) - 1 / 2) : ℝ) + 1) * θ - π / 2
      = -(2 * θ * (π / (4 * θ) - 1 / 2 - (round (π / (4 * θ) - 1 / 2) : ℝ))) := by
    field_simp
    ring
  rw [hmul, abs_neg, abs_mul]
  have h2θ : |2 * θ| = 2 * θ := abs_of_pos (by linarith)
  rw [h2θ]
  nlinarith

/-- For s = sin θ with 0 < θ ≤ π/2 and 0 < s ≤ 1, the chosen amplification count achieves
success probability at least max(1 - s², s²). This is the probability bound of [Hunziker et
al., Theorem 4.1][HunzikerEtAl2003]. -/
theorem amplified_success_prob {s θ : ℝ} (hs : 0 < s) (_hs1 : s ≤ 1) (hθ : Real.sin θ = s)
    (hθ0 : 0 < θ) (hθ2 : θ ≤ π / 2) :
    max (1 - s ^ 2) (s ^ 2) ≤ successProb θ (amplIters θ) := by
  have hclose := amplIters_close hθ0 hθ2
  have hsnonneg : 0 ≤ Real.sin θ := hθ ▸ hs.le
  rcases le_or_gt θ (π / 4) with hle | hlt
  · have hs2 : s ^ 2 ≤ 1 - s ^ 2 := by
      have hsin : Real.sin θ ≤ Real.sin (π / 4) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hle
      have hsqrt : Real.sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      rw [hsqrt] at hsin
      have : s ≤ Real.sqrt 2 / 2 := hθ ▸ hsin
      have h1 : s ^ 2 ≤ (Real.sqrt 2 / 2) ^ 2 := pow_le_pow_left₀ hs.le this 2
      have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      linarith
    have hmain : 1 - s ^ 2 ≤ successProb θ (amplIters θ) := by
      have := successProb_ge_one_sub_sq hθ0 hθ2 hclose
      rwa [hθ] at this
    rw [max_eq_left hs2]
    exact hmain
  · have hc0 : 0 ≤ π / (4 * θ) - 1 / 2 := by
      rw [sub_nonneg, le_div_iff₀ (by linarith : (0:ℝ) < 4 * θ)]
      linarith
    have hc1 : π / (4 * θ) - 1 / 2 < 1 / 2 := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ (by linarith : (0:ℝ) < 4 * θ)]
      linarith
    have hzero : round (π / (4 * θ) - 1 / 2) = 0 := by
      rw [round_eq_zero_iff]
      exact ⟨by linarith, hc1⟩
    have hm0 : amplIters θ = 0 := by
      rw [amplIters, hzero]
      rfl
    have hs2 : 1 - s ^ 2 ≤ s ^ 2 := by
      have hs : Real.sqrt 2 / 2 < s := by
        have hsin : Real.sin (π / 4) < Real.sin θ :=
          Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hlt
        rwa [Real.sin_pi_div_four, hθ] at hsin
      have h1 : (Real.sqrt 2 / 2) ^ 2 < s ^ 2 := by
        exact pow_lt_pow_left₀ hs (by positivity) two_ne_zero
      have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      linarith
    have hval : successProb θ (amplIters θ) = s ^ 2 := by
      rw [hm0, successProb]
      have hcast1 : (((2 * 0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
      rw [hcast1, one_mul, hθ]
    rw [hval, max_eq_right hs2]

/-- For s = sin θ with 0 < θ ≤ π/2 and 0 < s ≤ 1, the query count 2 `amplIters θ` + 1 is at most
(π/2 + 1)/s. This supplies the amplification cost bound in [HunzikerEtAl2003]. -/
theorem amplified_query_bound {s θ : ℝ} (hs : 0 < s) (_hs1 : s ≤ 1) (hθ : Real.sin θ = s)
    (hθ0 : 0 < θ) (hθ2 : θ ≤ π / 2) :
    2 * amplIters θ + 1 ≤ (π / 2 + 1) / s := by
  have h4θ : (0 : ℝ) < 4 * θ := by linarith
  have hbase0 : 0 ≤ π / (4 * θ) - 1 / 2 := by
    rw [sub_nonneg, le_div_iff₀ h4θ]
    linarith
  have hround : |π / (4 * θ) - 1 / 2 - (round (π / (4 * θ) - 1 / 2) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  have hr0 : (0 : ℤ) ≤ round (π / (4 * θ) - 1 / 2) := by
    have h := (abs_le.mp hround).2
    have : (-1 : ℝ) < (round (π / (4 * θ) - 1 / 2) : ℝ) := by linarith
    have h2 : (-1 : ℤ) < round (π / (4 * θ) - 1 / 2) := by exact_mod_cast this
    omega
  have hcast : ((amplIters θ : ℕ) : ℤ) = round (π / (4 * θ) - 1 / 2) := by
    rw [amplIters, Int.toNat_of_nonneg hr0]
  have hcastR : ((amplIters θ : ℕ) : ℝ) = (round (π / (4 * θ) - 1 / 2) : ℝ) := by
    rw [← hcast]
    push_cast
    rfl
  have hrle : (round (π / (4 * θ) - 1 / 2) : ℝ) ≤ π / (4 * θ) := by
    have := (abs_le.mp hround).1
    linarith
  have hse : s ≤ θ := by
    rw [← hθ]
    exact Real.sin_le hθ0.le
  have hθpos : 0 < θ := hθ0
  have h1 : 2 * (amplIters θ : ℝ) + 1 ≤ π / (2 * θ) + 1 := by
    have : (amplIters θ : ℝ) ≤ π / (4 * θ) := by rw [hcastR]; exact hrle
    have : 2 * (amplIters θ : ℝ) ≤ 2 * (π / (4 * θ)) := by linarith
    calc 2 * (amplIters θ : ℝ) + 1 ≤ 2 * (π / (4 * θ)) + 1 := by linarith
      _ = π / (2 * θ) + 1 := by field_simp; ring
  have h2 : π / (2 * θ) + 1 ≤ π / (2 * s) + 1 := by
    have hdiv : π / (2 * θ) ≤ π / (2 * s) := by
      apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    linarith
  have h3 : π / (2 * s) + 1 ≤ (π / 2 + 1) / s := by
    have h1s : (1 : ℝ) ≤ 1 / s := by
      rw [le_div_iff₀ hs]
      linarith
    have heq : (π / 2 + 1) / s = π / (2 * s) + 1 / s := by
      field_simp
    rw [heq]
    linarith
  calc (2 * amplIters θ + 1 : ℝ) = 2 * (amplIters θ : ℝ) + 1 := by ring
    _ ≤ (π / 2 + 1) / s := by linarith

end Qatlib.Papers.QLearningGeom03.MainResults
