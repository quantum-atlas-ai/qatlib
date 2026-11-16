/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section


/-! # Endpoint diagnostics for the legacy multinomial contract -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SwitchAdiab12.MainResults.ConvProbe
open Finset

/-- The exact scalar constant in the legacy Lemma V.4 interface. -/
def kappa (α : ℝ) : ℝ := (4 : ℝ) ^ (-(α - 3 / 2)) / (1 - (4 : ℝ) ^ (-(α - 1)))

/-- Its value at exponent two is too small for the included endpoint terms. -/
theorem kappaTwo : kappa 2 = 2 / 3 := by
  have hh : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
    have hs : Real.sqrt (4 : ℝ) = 2 := by
      convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1; norm_num
    rw [hs]
    norm_num
  have he : -(2 - 3 / 2 : ℝ) = -(1 / 2 : ℝ) := by norm_num
  have he₂ : -(2 - 1 : ℝ) = -1 := by norm_num
  rw [kappa, he, he₂, hh, Real.rpow_neg_one]
  norm_num

/-- The three-index legacy target fails for α=2, k=1 and n=0. -/
theorem refuteTriple : ¬ (
    (∑ k₁ ∈ Finset.range (1 + 1), ∑ k₂ ∈ Finset.range (1 - k₁ + 1),
        ((Nat.factorial 1 : ℝ) /
            ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ) *
              (Nat.factorial (1 - k₁ - k₂) : ℝ))) *
          ((k₁ + 0 : ℕ) : ℝ) ^ ((2 : ℝ) * ((k₁ + 0 : ℕ) : ℝ)) *
          ((k₂ : ℕ) : ℝ) ^ ((2 : ℝ) * ((k₂ : ℕ) : ℝ)) *
          (((1 - k₁ - k₂ : ℕ) : ℝ)) ^ ((2 : ℝ) * ((1 - k₁ - k₂ : ℕ) : ℝ)))
    ≤ (kappa 2) ^ 2 * (((1 + 0 : ℕ) : ℝ) ^ ((2 : ℝ) * ((1 + 0 : ℕ) : ℝ)))) := by
  norm_num [Finset.sum_range_succ, kappaTwo, Real.rpow_two]

/-- The four-index legacy target also fails at the same admissible parameters. -/
theorem refuteQuad : ¬ (
    (∑ k₁ ∈ Finset.range (1 + 1), ∑ k₂ ∈ Finset.range (1 - k₁ + 1),
        ∑ k₃ ∈ Finset.range (1 - k₁ - k₂ + 1),
        ((Nat.factorial 1 : ℝ) /
            ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ) *
              (Nat.factorial k₃ : ℝ) * (Nat.factorial (1 - k₁ - k₂ - k₃) : ℝ))) *
          ((k₁ + 0 : ℕ) : ℝ) ^ ((2 : ℝ) * ((k₁ + 0 : ℕ) : ℝ)) *
          ((k₂ : ℕ) : ℝ) ^ ((2 : ℝ) * ((k₂ : ℕ) : ℝ)) *
          ((k₃ : ℕ) : ℝ) ^ ((2 : ℝ) * ((k₃ : ℕ) : ℝ)) *
          (((1 - k₁ - k₂ - k₃ : ℕ) : ℝ)) ^
            ((2 : ℝ) * ((1 - k₁ - k₂ - k₃ : ℕ) : ℝ)))
    ≤ (kappa 2) ^ 3 * (((1 + 0 : ℕ) : ℝ) ^ ((2 : ℝ) * ((1 + 0 : ℕ) : ℝ)))) := by
  norm_num [Finset.sum_range_succ, kappaTwo, Real.rpow_two]
end Qatlib.Papers.SwitchAdiab12.MainResults.ConvProbe
