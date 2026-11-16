/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier.SourceInfluenceFourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section


/-! # Preserved complete legacy mathematical components

These definitions and conditional estimates retain their complete original
mathematics. Free success/query fields are not an oracle algorithm; scalar
amplification estimates are not a repetition or termination proof.
-/
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier
open scoped BigOperators ENNReal
namespace Qatlib.Papers.BoolHidShift11.RankGrowth.AmpBounds

/-- On the positive first quadrant, the square root of the squared sine is bounded by the angle. -/
theorem sqrtAngle {a θ : ℝ} (hθ : 0 < θ) (hπ : θ ≤ Real.pi / 2)
    (hsin : Real.sin θ ^ 2 = a) : Real.sqrt a ≤ θ := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.le (by linarith [hπ, Real.pi_pos])
  have hsq : Real.sqrt a = Real.sin θ := by
    rw [← hsin]
    exact Real.sqrt_sq hs0
  rw [hsq]
  exact le_of_lt (Real.sin_lt hθ)

/-- **Amplification iteration bound**: the BHMT iteration count
`m = ⌊π/(4θ)⌋` is at most `π/(4√a)` when `sin²θ = a`, which is the
`O(1/√δ)` factor of Corollary 1. -/
theorem iterBound {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ)
    (hπ : θ ≤ Real.pi / 2) (hsin : Real.sin θ ^ 2 = a) :
    (Nat.floor (Real.pi / (4 * θ)) : ℝ) ≤ Real.pi / (4 * Real.sqrt a) := by
  have hsqrt_le : Real.sqrt a ≤ θ := sqrtAngle hθ hπ hsin
  have hfloor : (Nat.floor (Real.pi / (4 * θ)) : ℝ) ≤ Real.pi / (4 * θ) :=
    Nat.floor_le (by positivity)
  have hden : 4 * Real.sqrt a ≤ 4 * θ := by linarith
  have hpos : 0 < 4 * Real.sqrt a := by positivity
  calc
    (Nat.floor (Real.pi / (4 * θ)) : ℝ) ≤ Real.pi / (4 * θ) := hfloor
    _ ≤ Real.pi / (4 * Real.sqrt a) :=
      div_le_div_of_nonneg_left Real.pi_pos.le hpos hden

/-- The BHMT guarantee `max (1-a) a ≤ success` implies success probability at
least `1/2`, for any real `a`. -/
theorem maxHalf {a : ℝ} :
    (1 / 2 : ℝ) ≤ max (1 - a) a := by
  rcases le_or_gt a (1 / 2) with h | h
  · rw [max_eq_left (by linarith : a ≤ 1 - a)]
    linarith
  · rw [max_eq_right (by linarith : 1 - a ≤ a)]
    linarith

/-- Success probability above `max (1-a) a` (as delivered by the BHMT theorem)
is at least `1/2`. -/
theorem successHalf {a success : ℝ}
    (h : max (1 - a) a ≤ success) : (1 / 2 : ℝ) ≤ success :=
  le_trans maxHalf h

/-- `⌈log_{4/3}(1/ε)⌉` repetitions reduce the failure probability `(3/4)^k`
below `ε`; existence form used by the repetition step of Corollary 1. -/
theorem geoReps {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, (3 / 4 : ℝ) ^ k < ε :=
  exists_pow_lt_of_lt_one hε (by norm_num)

/-! ### Corollary 1 -/


end Qatlib.Papers.BoolHidShift11.RankGrowth.AmpBounds
