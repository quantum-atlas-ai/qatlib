/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SpinCoefficient

/-! # Finite dyadic square roots for the initial seed -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of seed Sqrt Floor in the Rational Flow construction. -/
def seedSqrtFloor (a : ℚ) (b : ℕ) : ℚ :=
  (Nat.sqrt (Nat.floor (a*(2^b : ℚ)^2)) : ℚ)/(2^b : ℚ)

/-- Original `seedSqrtFloor_nonneg` guarantee for the `SeedSqrt` construction; the complete source hypotheses are retained. -/
theorem seedSqrtFloor_nonneg (a : ℚ) (b : ℕ) : 0 ≤ seedSqrtFloor a b := by
  unfold seedSqrtFloor
  positivity

noncomputable section

/-- The executable integer square root is a lower enclosure of the real root,
with one dyadic unit of error. No real comparison occurs in its computation. -/
theorem seedSqrtFloor_bounds (a : ℚ) (ha : 0 ≤ a) (b : ℕ) :
    (seedSqrtFloor a b : ℝ) ≤ Real.sqrt (a : ℝ) ∧
      Real.sqrt (a : ℝ)-(seedSqrtFloor a b : ℝ) ≤ (2^b : ℝ)⁻¹ := by
  let n := Nat.floor (a*(2^b : ℚ)^2)
  let r := Nat.sqrt n
  have hp : (0 : ℚ)<2^b := by positivity
  have hlo : (r : ℚ)^2 ≤ a*(2^b : ℚ)^2 := by
    have h : r^2 ≤ n := Nat.sqrt_le' n
    have hR : (r : ℚ)^2 ≤ (n : ℚ) := by exact_mod_cast h
    exact hR.trans (Nat.floor_le (by positivity))
  have hhi : a*(2^b : ℚ)^2 < ((r : ℚ)+1)^2 := by
    have h : n+1 ≤ (r+1)^2 := Nat.succ_le_succ_sqrt' n
    have hh : (n : ℚ)+1 ≤ ((r : ℚ)+1)^2 := by exact_mod_cast h
    exact (Nat.lt_floor_add_one _).trans_le hh
  have hslo : (seedSqrtFloor a b)^2 ≤ a := by
    change ((r : ℚ)/(2^b : ℚ))^2 ≤ a
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hp)).mpr hlo
  have hshi : a ≤ (seedSqrtFloor a b+(2^b : ℚ)⁻¹)^2 := by
    have he : seedSqrtFloor a b+(2^b : ℚ)⁻¹=((r : ℚ)+1)/(2^b : ℚ) := by
      dsimp [seedSqrtFloor,r,n]
      field_simp
    rw [he,div_pow]
    exact (le_div_iff₀ (sq_pos_of_pos hp)).mpr hhi.le
  have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hsnon : (0 : ℝ) ≤ seedSqrtFloor a b := by exact_mod_cast seedSqrtFloor_nonneg a b
  have hsloR : (seedSqrtFloor a b : ℝ)^2 ≤ (a : ℝ) := by exact_mod_cast hslo
  have hshiR : (a : ℝ) ≤ ((seedSqrtFloor a b : ℝ)+(2^b : ℝ)⁻¹)^2 := by
    have h : (a : ℝ) ≤ (((seedSqrtFloor a b+(2^b : ℚ)⁻¹)^2 : ℚ) : ℝ) := Rat.cast_le.mpr hshi
    push_cast at h
    exact h
  constructor
  · apply (sq_le_sq₀ hsnon (Real.sqrt_nonneg _)).mp
    simpa only [Real.sq_sqrt har] using hsloR
  · have h : Real.sqrt (a : ℝ) ≤ (seedSqrtFloor a b : ℝ)+(2^b : ℝ)⁻¹ := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      simpa only [Real.sq_sqrt har] using hshiR
    linarith

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
