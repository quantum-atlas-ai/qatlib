/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommuteTest05.MainResults.Corollary14

@[expose] public section

/-!
# The averaged cosine estimate of Claim 13

In the proof of [Itakura2005], Claim 13 the deviation of the walk state is controlled through the
average `(1 / (T + 1)) * ∑ t, cos (2 * θ * t)` of the cosine of the accumulated phase. The source
uses `cos α ≤ 1 - α ^ 2 / 8` and the Lipschitz bound for `cos`; the resulting estimate is quoted
with a generous constant.

This module proves the averaged estimate directly. Pairing each term against `2 * sin θ` turns
the sum into the telescoping family `sin ((2 * t + 1) * θ) - sin ((2 * t - 1) * θ)`, whose total
is `sin ((2 * T + 1) * θ) + sin θ`. Bounding the sine by `1` gives the average bound `1 / sin θ`,
and `sin θ ≥ θ / 2` on `(0, π / 2]` upgrades the constant to the paper's `4 / θ`.

## Main statements

* `cosine_average_bound`: for `0 < θ ≤ π / 2`, the average of `cos (2 * θ * t)` over
  `t < T + 1` is at most `4 / ((T + 1) * θ)`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CommuteTest05.WalkDetect

/-- The elementary identity `2 * sin θ * cos (2 * θ * t) = sin ((2t + 1)θ) - sin ((2t - 1)θ)`,
which turns the cosine sum of [Itakura2005], Claim 13 into a telescoping sum. -/
theorem two_sin_mul_cos (θ : ℝ) (t : ℕ) :
    2 * Real.sin θ * Real.cos (2 * θ * (t : ℝ)) =
      Real.sin ((2 * (t : ℝ) + 1) * θ) - Real.sin ((2 * (t : ℝ) - 1) * θ) := by
  have hA : 2 * (t : ℝ) * θ + θ = (2 * (t : ℝ) + 1) * θ := by ring
  have hB : 2 * (t : ℝ) * θ - θ = (2 * (t : ℝ) - 1) * θ := by ring
  have hC : 2 * θ * (t : ℝ) = 2 * (t : ℝ) * θ := by ring
  rw [← hA, ← hB, Real.sin_add, Real.sin_sub, hC]
  ring

/-- For `0 < θ ≤ π / 2`, the average of `cos (2 * θ * t)` over `t < T + 1` is at most
`4 / ((T + 1) * θ)`. This is the averaged deviation estimate used in the proof of
[Itakura2005], Claim 13. -/
theorem cosine_average_bound (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2) (T : ℕ) :
    1 / ((T + 1 : ℕ) : ℝ) *
        (∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ * (t : ℝ)))
      ≤ 4 / (((T + 1 : ℕ) : ℝ) * θ) := by
  have hN : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) := by positivity
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos, hθπ])
  have hterm : ∀ t : ℕ, 2 * Real.sin θ * Real.cos (2 * θ * (t : ℝ)) =
      Real.sin ((2 * (t : ℝ) + 1) * θ) - Real.sin ((2 * (t : ℝ) - 1) * θ) :=
    two_sin_mul_cos θ
  have htel : (∑ t ∈ Finset.range (T + 1),
        (Real.sin ((2 * (t : ℝ) + 1) * θ) - Real.sin ((2 * (t : ℝ) - 1) * θ))) =
      Real.sin ((2 * (T : ℝ) + 1) * θ) + Real.sin θ := by
    have h2 := Finset.sum_range_sub
      (fun t : ℕ => Real.sin ((2 * (t : ℝ) - 1) * θ)) (T + 1)
    calc (∑ t ∈ Finset.range (T + 1),
          (Real.sin ((2 * (t : ℝ) + 1) * θ) - Real.sin ((2 * (t : ℝ) - 1) * θ)))
        = ∑ t ∈ Finset.range (T + 1),
            (Real.sin ((2 * ((t + 1 : ℕ) : ℝ) - 1) * θ) -
              Real.sin ((2 * (t : ℝ) - 1) * θ)) := by
          apply Finset.sum_congr rfl
          intro t _
          have e : 2 * ((t + 1 : ℕ) : ℝ) - 1 = 2 * (t : ℝ) + 1 := by
            push_cast
            ring
          rw [e]
      _ = Real.sin ((2 * ((T + 1 : ℕ) : ℝ) - 1) * θ) -
            Real.sin ((2 * ((0 : ℕ) : ℝ) - 1) * θ) := h2
      _ = Real.sin ((2 * (T : ℝ) + 1) * θ) + Real.sin θ := by
          have eT : 2 * ((T + 1 : ℕ) : ℝ) - 1 = 2 * (T : ℝ) + 1 := by
            push_cast
            ring
          have e0 : (2 * ((0 : ℕ) : ℝ) - 1) * θ = -θ := by norm_num
          rw [eT, e0, Real.sin_neg]
          ring
  have hsum : 2 * Real.sin θ *
      (∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ * (t : ℝ))) =
      Real.sin ((2 * (T : ℝ) + 1) * θ) + Real.sin θ := by
    have h1 : (∑ t ∈ Finset.range (T + 1),
          2 * Real.sin θ * Real.cos (2 * θ * (t : ℝ))) =
        ∑ t ∈ Finset.range (T + 1),
          (Real.sin ((2 * (t : ℝ) + 1) * θ) - Real.sin ((2 * (t : ℝ) - 1) * θ)) :=
      Finset.sum_congr rfl (fun t _ => hterm t)
    rw [← Finset.mul_sum] at h1
    rw [h1, htel]
  have hB : |∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ * (t : ℝ))| ≤ 1 / Real.sin θ := by
    have h2 : 2 * Real.sin θ *
        |∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ * (t : ℝ))| ≤ 2 := by
      have e : 2 * Real.sin θ *
            |∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ * (t : ℝ))| =
          |Real.sin ((2 * (T : ℝ) + 1) * θ) + Real.sin θ| := by
        rw [← hsum, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sin θ)]
      rw [e]
      calc |Real.sin ((2 * (T : ℝ) + 1) * θ) + Real.sin θ|
          ≤ |Real.sin ((2 * (T : ℝ) + 1) * θ)| + |Real.sin θ| := abs_add_le _ _
        _ ≤ 2 := by
            have h1 := Real.abs_sin_le_one ((2 * (T : ℝ) + 1) * θ)
            have h3 := Real.abs_sin_le_one θ
            linarith
    rw [le_div_iff₀ hsin]
    nlinarith
  have h1sin : 1 / Real.sin θ ≤ 4 / θ := by
    have hst : θ / 2 ≤ Real.sin θ := by
      have hpi2 : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
        rw [le_div_iff₀ Real.pi_pos]
        linarith [Real.pi_le_four]
      have h4 := mul_le_mul_of_nonneg_right hpi2 hθ0.le
      linarith [Real.mul_le_sin hθ0.le hθπ]
    rw [div_le_div_iff₀ hsin hθ0]
    nlinarith
  have hSle : (∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ * (t : ℝ))) ≤ 4 / θ :=
    (le_abs_self _).trans (hB.trans h1sin)
  calc 1 / ((T + 1 : ℕ) : ℝ) *
        (∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ * (t : ℝ)))
      ≤ 1 / ((T + 1 : ℕ) : ℝ) * (4 / θ) :=
        mul_le_mul_of_nonneg_left hSle (by positivity)
    _ = 4 / (((T + 1 : ℕ) : ℝ) * θ) := by
        field_simp

end Qatlib.Papers.CommuteTest05.WalkDetect
