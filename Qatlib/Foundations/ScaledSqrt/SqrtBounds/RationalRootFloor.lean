/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! # The actual integer-quotient/isqrt operation of the rational compiler

Only the positive square root is floored. Signs are applied afterwards.
The integer quotient is exactly the one used by Python's `isqrt` call.
-/
namespace Qatlib.Foundations.ScaledSqrt.SqrtBounds
set_option autoImplicit false
set_option maxHeartbeats 2000000

def rootCount (half : ℕ) (p : ℚ) : ℕ :=
  Nat.sqrt (half ^ 2 * p.num.toNat / p.den)

/-- The actual quotient/isqrt is within one below the exact positive root. -/
theorem rootCount_bounds (half : ℕ) (p : ℚ) (hp : 0 ≤ p) :
    (rootCount half p : ℝ) ≤ (half : ℝ) * Real.sqrt (p : ℝ) ∧
      (half : ℝ) * Real.sqrt (p : ℝ) < (rootCount half p : ℝ) + 1 := by
  let a := half ^ 2 * p.num.toNat
  let d := p.den
  let r := rootCount half p
  have hd : 0 < d := p.den_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (p.num.toNat : ℝ) = (p.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hp)
  have hc : (p : ℝ) = (p.num.toNat : ℝ) / d := by rw [Rat.cast_def, hn]
  have hlo : r ^ 2 * d ≤ a :=
    (Nat.le_div_iff_mul_le hd).mp (Nat.sqrt_le' (a / d))
  have hhi : a < (r + 1) ^ 2 * d :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_sqrt' (a / d))
  have hlR : (r : ℝ) ^ 2 ≤ (half : ℝ) ^ 2 * (p : ℝ) := by
    rw [hc, ← mul_div_assoc]
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast hlo
  have hhR : (half : ℝ) ^ 2 * (p : ℝ) < ((r : ℝ) + 1) ^ 2 := by
    rw [hc, ← mul_div_assoc]
    apply (div_lt_iff₀ hdR).mpr
    exact_mod_cast hhi
  have hpR : (0 : ℝ) ≤ p := by exact_mod_cast hp
  have hs := Real.sq_sqrt hpR
  have hr : (0 : ℝ) ≤ r := by positivity
  have hv : 0 ≤ (half : ℝ) * Real.sqrt (p : ℝ) := by positivity
  have hv2 : ((half : ℝ) * Real.sqrt (p : ℝ)) ^ 2 = (half : ℝ) ^ 2 * (p : ℝ) := by
    rw [mul_pow, hs]
  change (r : ℝ) ≤ _ ∧ _ < (r : ℝ) + 1
  constructor <;> nlinarith

/-- A probability bounded by one cannot exceed the supplied scale after flooring. -/
theorem rootCount_le_half (half : ℕ) (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    rootCount half p ≤ half := by
  have hs : Real.sqrt (p : ℝ) ≤ 1 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by exact_mod_cast hp1⟩
  have hb := (rootCount_bounds half p hp).1
  have hh : (0 : ℝ) ≤ half := by positivity
  have h : (rootCount half p : ℝ) ≤ half := by nlinarith [mul_le_mul_of_nonneg_left hs hh]
  exact_mod_cast h

def signedCount (negative : Bool) (n : ℕ) : ℤ := if negative then -(n : ℤ) else n

noncomputable def signedRoot (negative : Bool) (p : ℚ) : ℝ :=
  if negative then -Real.sqrt (p : ℝ) else Real.sqrt (p : ℝ)

/-- Adding the selected sign preserves the magnitude of an integer count. -/
theorem signedCount_natAbs (negative : Bool) (n : ℕ) :
    (signedCount negative n).natAbs = n := by cases negative <;> simp [signedCount]

/-- Either selected sign preserves the strict unit rounding-error bound. -/
theorem signedCount_error (half : ℕ) (p : ℚ) (hp : 0 ≤ p) (negative : Bool) :
    |(signedCount negative (rootCount half p) : ℝ) - (half : ℝ) * signedRoot negative p| < 1 := by
  have h := rootCount_bounds half p hp
  cases negative <;> simp only [signedCount, signedRoot, Bool.false_eq_true, ↓reduceIte,
    Int.cast_natCast, Int.cast_neg, mul_neg, sub_neg_eq_add]
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- Either selected sign squares back to the nonnegative rational input. -/
theorem signedRoot_sq (negative : Bool) (p : ℚ) (hp : 0 ≤ p) :
    signedRoot negative p ^ 2 = (p : ℝ) := by
  have h : (0 : ℝ) ≤ p := by exact_mod_cast hp
  cases negative <;> simp [signedRoot, Real.sq_sqrt h]

end Qatlib.Foundations.ScaledSqrt.SqrtBounds
