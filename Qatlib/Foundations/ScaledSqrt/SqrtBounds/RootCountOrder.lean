/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ScaledSqrt.SqrtBounds.RationalRootFloor

@[expose] public section

set_option doc.verso true

/-! # Order preservation for rational root counts

The integer approximation {name}`Qatlib.Foundations.ScaledSqrt.SqrtBounds.rootCount`
preserves the order of nonnegative rational inputs at a fixed natural scale.
The strict unit interval in
{name}`Qatlib.Foundations.ScaledSqrt.SqrtBounds.rootCount_bounds`
turns the real square-root comparison into a comparison of natural counts.
Zero scale and zero inputs are included; no running-time claim is made.
Signs are added separately, so the order statement concerns the unsigned count.
-/

namespace Qatlib.Foundations.ScaledSqrt.SqrtBounds

set_option autoImplicit false

/-- Integer root counts preserve the order of nonnegative rational inputs at a fixed scale.
The count is defined by {name}`Qatlib.Foundations.ScaledSqrt.SqrtBounds.rootCount`. -/
theorem rootCount_mono (half : ℕ) {p q : ℚ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    rootCount half p ≤ rootCount half q := by
  have hq : 0 ≤ q := le_trans hp hpq
  have hs : Real.sqrt (p : ℝ) ≤ Real.sqrt (q : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hpq)
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg half : (0 : ℝ) ≤ half)
  have h : (rootCount half p : ℝ) < (rootCount half q : ℝ) + 1 :=
    lt_of_le_of_lt (le_trans (rootCount_bounds half p hp).1 hm)
      (rootCount_bounds half q hq).2
  have hn : rootCount half p < rootCount half q + 1 := by exact_mod_cast h
  exact Nat.lt_succ_iff.mp hn

end Qatlib.Foundations.ScaledSqrt.SqrtBounds
