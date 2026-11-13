/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.DenseZeroModeBoundaryStat

/-!
# Half-density restriction for the zero-frequency bound

`denseZeroModeBoundary_answer` proves the zero-frequency trigonometric bound for positive marked
density at most one half. It also exhibits density 3/4 as a counterexample to extending that
bound without the density restriction in the setting of [Cornwell2014].

## Main statements

* `denseZeroModeBoundary_answer`: Proves the zero-mode bound under half-density and the explicit
  N=4, T=3 counterexample with zero-mode value one and proposed upper bound 3/4; see
  [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope

/-- Proves the zero-mode bound under half-density and the explicit N=4, T=3 counterexample with
zero-mode value one and proposed upper bound 3/4; see [Cornwell2014]. -/
theorem denseZeroModeBoundary_answer : DenseZeroModeBoundary := by
  constructor
  · intro N hN T hhalf hT
    (try dsimp only)
    have hθ := aq_angle_properties N T hN hT hhalf
    have hg := aq_floor_gain (aqAngle N T) hθ.1 hθ.2.1
    have h1 := Real.sin_sq_add_cos_sq (2 * (aqRounds N T : ℝ) * aqAngle N T)
    have h2 := Real.sin_sq_add_cos_sq (2 * aqAngle N T)
    have hlow : (Real.cos (2 * aqAngle N T))^2 ≤
        (Real.sin (2 * (aqRounds N T : ℝ) * aqAngle N T))^2 := hg.2.1
    refine ⟨sq_nonneg _, ?_⟩
    change (Real.cos (2 * (aqRounds N T : ℝ) * aqAngle N T))^2 ≤ _
    nlinarith
  · have hθ : aqAngle 4 3 = Real.pi / 3 := by
      unfold aqAngle
      have hs : Real.sqrt ((3 : ℝ)/4) = Real.sin (Real.pi/3) := by
        rw [Real.sin_pi_div_three, Real.sqrt_div (by norm_num)]
        rw [show Real.sqrt 4 = (2 : ℝ) by norm_num [Real.sqrt_eq_iff_eq_sq]]
      norm_num only [Nat.cast_ofNat]
      rw [hs, Real.arcsin_sin]
      all_goals linarith [Real.pi_pos]
    have hk : aqRounds 4 3 = 0 := by
      unfold aqRounds
      rw [hθ]
      have hv : Real.pi / (4 * (Real.pi / 3)) = (3/4 : ℝ) := by
        field_simp
      rw [hv]
      norm_num
    (try dsimp only)
    rw [hθ, hk]
    norm_num only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, one_pow]
    simp only [true_and]
    refine ⟨Real.sq_sin_pi_div_three, ?_⟩
    rw [Real.sin_two_mul, Real.cos_pi_div_three]
    convert Real.sq_sin_pi_div_three using 1
    ring

end Qatlib.Concepts.AmpTransform.NoiseEnvelope
