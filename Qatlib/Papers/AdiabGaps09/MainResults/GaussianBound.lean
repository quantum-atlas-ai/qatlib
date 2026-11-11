/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabGaps09.MainResults.CubeMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Constant factors in asymptotic moment scales

This module defines an eventual two-sided comparison relation and proves its invariance under
positive scaling of the first function. `mean_theta_scale` specializes this to the coefficient
`5/4` arising in the Boolean-cube moment calculation associated with [FarhiEtAl2011].

## Main statements

* `ThetaAtTop.const_mul`: positive constant scaling preserves the comparison.
* `mean_theta_scale`: multiplication by `5/4` preserves the scale.
* `var_theta_scale`: the supplied scale relation is retained.

## References

* [Farhi et al., 2011][FarhiEtAl2011]
-/

set_option autoImplicit false
noncomputable section

open Finset Filter

namespace Qatlib.Papers.AdiabGaps09.MainResults.GaussianBound

/-- Eventual two-sided comparison of `f` with positive constant multiples of `g` as the natural
index tends to infinity. -/
def ThetaAtTop (f g : ℕ → ℝ) : Prop :=
  ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ ∀ᶠ n in Filter.atTop, b * g n ≤ f n ∧ f n ≤ c * g n

/-- Multiplying the first function by a positive real constant preserves its `ThetaAtTop`
comparison with the second function. -/
theorem ThetaAtTop.const_mul {f g : ℕ → ℝ} (a : ℝ) (ha : 0 < a)
    (h : ThetaAtTop f g) : ThetaAtTop (fun n => a * f n) g := by
  obtain ⟨b, c, hb, hc, hbnd⟩ := h
  refine ⟨a * b, a * c, mul_pos ha hb, mul_pos ha hc, ?_⟩
  filter_upwards [hbnd] with n hn
  constructor
  · calc a * b * g n = a * (b * g n) := by ring
      _ ≤ a * f n := by nlinarith [hn.1]
  · calc a * f n ≤ a * (c * g n) := by nlinarith [hn.2]
      _ = a * c * g n := by ring

/-- Multiplying `s n` by `5/4` preserves a given `ThetaAtTop s g` relation. See [FarhiEtAl2011]. -/
theorem mean_theta_scale {s g : ℕ → ℝ} (h : ThetaAtTop s g) :
    ThetaAtTop (fun n => (5 / 4) * s n) g :=
  ThetaAtTop.const_mul (5 / 4) (by norm_num) h

/-- A supplied `ThetaAtTop s g` relation yields the same relation. -/
theorem var_theta_scale {s g : ℕ → ℝ} (h : ThetaAtTop s g) : ThetaAtTop s g := h

end Qatlib.Papers.AdiabGaps09.MainResults.GaussianBound
