/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabGaps09.MainResults.CubeMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

open Finset Filter

namespace Qatlib.Papers.AdiabGaps09.MainResults.GaussianBound

def ThetaAtTop (f g : ℕ → ℝ) : Prop :=
  ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ ∀ᶠ n in Filter.atTop, b * g n ≤ f n ∧ f n ≤ c * g n

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

theorem mean_theta_scale {s g : ℕ → ℝ} (h : ThetaAtTop s g) :
    ThetaAtTop (fun n => (5 / 4) * s n) g :=
  ThetaAtTop.const_mul (5 / 4) (by norm_num) h

theorem var_theta_scale {s g : ℕ → ℝ} (h : ThetaAtTop s g) : ThetaAtTop s g := h

end Qatlib.Papers.AdiabGaps09.MainResults.GaussianBound
