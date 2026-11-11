/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Qatlib.Papers.QLearningGeom03.MainResults.Battleship

/-!
# Sine formulas for cyclic ship windows

This module converts the finite geometric series for a symmetric cyclic ship window into a sine
quotient. It relates the cyclic character `chiN` to complex exponentials and proves
`bs_window_sine`, giving sin((2r + 1)θ)/sin θ for a nonzero frequency with nonvanishing
denominator.

These identities support the battleship spectral analysis in [HunzikerEtAl2003].

## Main statements

* `exp_window_sine`: The complex sine quotient for a symmetric exponential sum.
* `bs_window_sine`: The corresponding cyclic character sum.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {N : ℕ} [NeZero N]

/-- For complex z, exp(iz) - exp(-iz) equals 2i sin z. -/
lemma exp_mul_I_sub_exp_neg (z : ℂ) :
    Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I))
      = 2 * Complex.sin z * Complex.I := by
  have h := Complex.two_sin z
  have hneg : Complex.exp (-z * Complex.I) = Complex.exp (-(z * Complex.I)) := by
    rw [neg_mul]
  rw [hneg] at h
  have h' : Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)
      = 2 * Complex.sin z / Complex.I := by
    rw [eq_div_iff Complex.I_ne_zero]
    exact h.symm
  calc Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I))
      = -(Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)) := by ring
    _ = -(2 * Complex.sin z / Complex.I) := by rw [h']
    _ = 2 * Complex.sin z * Complex.I := by
        rw [div_eq_mul_inv, Complex.inv_I]
        ring

/-- For complex z, exp(2iz) - 1 factors as exp(iz) times 2i sin z. -/
lemma exp_two_mul_I_sub_one (z : ℂ) :
    Complex.exp (2 * z * Complex.I) - 1
      = Complex.exp (z * Complex.I) * (2 * Complex.sin z * Complex.I) := by
  have hsplit : Complex.exp (2 * z * Complex.I)
      = Complex.exp (z * Complex.I) * Complex.exp (z * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hone : Complex.exp (z * Complex.I) * Complex.exp (-(z * Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [hsplit, ← hone, ← mul_sub, exp_mul_I_sub_exp_neg]

/-- If sin z is nonzero, then exp(2iz) is different from 1. -/
lemma exp_two_mul_I_ne_one {z : ℂ} (hz : Complex.sin z ≠ 0) :
    Complex.exp (2 * z * Complex.I) ≠ 1 := by
  intro h
  have h1 := exp_two_mul_I_sub_one z
  rw [h, sub_self] at h1
  have h2 : Complex.exp (z * Complex.I) * (2 * Complex.sin z * Complex.I) = 0 := h1.symm
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Complex.exp_ne_zero _ h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · norm_num at h5
      · exact hz h5
    · exact Complex.I_ne_zero h4

/-- When sin z is nonzero, the phase-adjusted geometric quotient of length 2r + 1 equals sin((2r
+ 1)z)/sin z. -/
lemma exp_window_sine {z : ℂ} (hz : Complex.sin z ≠ 0) (r : ℕ) :
    (Complex.exp (2 * z * Complex.I) ^ r)⁻¹
        * ((Complex.exp (2 * z * Complex.I) ^ (2 * r + 1) - 1)
            / (Complex.exp (2 * z * Complex.I) - 1))
      = Complex.sin (((2 * r + 1 : ℕ) : ℂ) * z) / Complex.sin z := by
  have hden0 := exp_two_mul_I_ne_one hz
  have hsinz : Complex.sin z ≠ 0 := hz
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hden : Complex.exp (z * Complex.I) * (2 * Complex.sin z * Complex.I) ≠ 0 := by
    refine mul_ne_zero (Complex.exp_ne_zero _) ?_
    exact mul_ne_zero (mul_ne_zero (by norm_num) hsinz) hI
  have hpow : Complex.exp (2 * z * Complex.I) ^ (2 * r + 1)
      = Complex.exp (2 * (((2 * r + 1 : ℕ) : ℂ) * z) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpowr : Complex.exp (2 * z * Complex.I) ^ r
      = Complex.exp (2 * ((r : ℂ) * z) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hinv : (Complex.exp (2 * z * Complex.I) ^ r)⁻¹
      = Complex.exp (-(2 * ((r : ℂ) * z) * Complex.I)) := by
    rw [hpowr, ← Complex.exp_neg]
  rw [hinv, hpow, exp_two_mul_I_sub_one z,
    exp_two_mul_I_sub_one (((2 * r + 1 : ℕ) : ℂ) * z)]
  have hphase : Complex.exp (-(2 * ((r : ℂ) * z) * Complex.I))
        * Complex.exp ((((2 * r + 1 : ℕ) : ℂ) * z) * Complex.I)
      = Complex.exp (z * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hnum : Complex.exp (-(2 * ((r : ℂ) * z) * Complex.I))
        * (Complex.exp ((((2 * r + 1 : ℕ) : ℂ) * z) * Complex.I)
            * (2 * Complex.sin ((((2 * r + 1 : ℕ) : ℂ) * z)) * Complex.I))
      = Complex.exp (z * Complex.I)
          * (2 * Complex.sin ((((2 * r + 1 : ℕ) : ℂ) * z)) * Complex.I) := by
    rw [← mul_assoc, hphase]
  rw [← mul_div_assoc, hnum]
  rw [div_eq_div_iff hden hsinz]
  ring

/-- For real θ with nonzero sine, the phase-adjusted complex geometric quotient equals the
complex embedding of sin((2r + 1)θ)/sin θ. -/
lemma exp_window_sine_real {θ : ℝ} (hθ : Real.sin θ ≠ 0) (r : ℕ) :
    (Complex.exp (2 * (θ : ℂ) * Complex.I) ^ r)⁻¹
        * ((Complex.exp (2 * (θ : ℂ) * Complex.I) ^ (2 * r + 1) - 1)
            / (Complex.exp (2 * (θ : ℂ) * Complex.I) - 1))
      = ((Real.sin (((2 * r + 1 : ℕ) : ℝ) * θ) / Real.sin θ : ℝ) : ℂ) := by
  have hsin : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr hθ
  have h := exp_window_sine hsin r
  rw [h]
  have hmulcast : (((2 * r + 1 : ℕ) : ℂ)) = ((((2 * r + 1 : ℕ) : ℝ)) : ℂ) :=
    (Complex.ofReal_natCast (2 * r + 1)).symm
  rw [show Complex.sin (((2 * r + 1 : ℕ) : ℂ) * (θ : ℂ))
        = ((Real.sin (((2 * r + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ) from by
    rw [hmulcast, ← Complex.ofReal_mul, ← Complex.ofReal_sin]]
  rw [show Complex.sin (θ : ℂ) = ((Real.sin θ : ℝ) : ℂ) from (Complex.ofReal_sin θ).symm]
  rw [← Complex.ofReal_div]

/-- The cyclic character at 1 is exp(2iθ) for θ = π j.val/N. -/
lemma chiN_one_eq_exp (j : ZMod N) :
    chiN (N := N) j 1
      = Complex.exp (2 * ((Real.pi * (j.val : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I) := by
  unfold chiN
  rw [mul_one, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  ring

/-- The cyclic character at -r is the inverse of the r-th power of its value at 1. -/
lemma chiN_neg_natCast (j : ZMod N) (r : ℕ) :
    chiN (N := N) j (-((r : ℕ) : ZMod N)) = ((chiN (N := N) j 1) ^ r)⁻¹ := by
  have hmul : chiN (N := N) j (-((r : ℕ) : ZMod N)) * (chiN (N := N) j 1) ^ r = 1 := by
    rw [chiN_pow_natCast j r, ← chiN_add_right, neg_add_cancel, chiN_zero_right]
  exact eq_inv_of_mul_eq_one_left hmul

/-- For 2r + 1 ≤ N and a nonzero frequency with nonvanishing sine, the character sum over the
ship window is sin((2r + 1)θ)/sin θ with θ = π j.val/N. This is the sine formula used in
[Hunziker et al., Theorem 6.1][HunzikerEtAl2003]. -/
theorem bs_window_sine {r : ℕ} (h : 2 * r + 1 ≤ N) {j : ZMod N} (hj : j ≠ 0)
    (hsin : Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)) ≠ 0) :
    (∑ k ∈ shipWindow (N := N) r, chiN j k)
      = ((Real.sin (((2 * r + 1 : ℕ) : ℝ) * (Real.pi * (j.val : ℝ) / (N : ℝ)))
          / Real.sin (Real.pi * (j.val : ℝ) / (N : ℝ)) : ℝ) : ℂ) := by
  rw [bs_window_geom_closed h hj, chiN_neg_natCast, chiN_one_eq_exp]
  exact exp_window_sine_real hsin r

end Qatlib.Papers.QLearningGeom03.MainResults
