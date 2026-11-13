/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.Gadgets.GateWidgets

/-!
# The basis-change scattering block

This module packages the basis-widget transmission coefficients into `basisBlock` and identifies
its value at momentum `-π / 4` with `Ubasis`. It verifies both unitary identities for this
block, as required by the gate construction in [Childs2009].

## Main statements

* `basisBlock_at_working_momentum`: The working-momentum block equals `Ubasis`.
* `basisBlock_unitary`: The working-momentum block is unitary.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.Gates

open Matrix

set_option autoImplicit false

/-- The symmetric two-channel transmission matrix with diagonal coefficient `basisT00 k` and
off-diagonal coefficient `basisT01 k`. -/
noncomputable def basisBlock (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![basisT00 k, basisT01 k; basisT01 k, basisT00 k]

/-- The product of complex `√2` and `invSqrt2` is one. -/
theorem sqrt_two_mul_invSqrt2 : (Real.sqrt 2 : ℂ) * invSqrt2 = 1 := by
  unfold invSqrt2
  rw [← Complex.ofReal_mul]
  have h : (Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    field_simp
  rw [h]
  norm_num

/-- At momentum `-π / 4`, the diagonal basis-widget transmission coefficient is `-invSqrt2 * i`
[Childs2009]. -/
theorem basisT00_at_working_momentum :
    basisT00 (-(Real.pi / 4)) = -invSqrt2 * Complex.I := by
  unfold basisT00
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs : ((Real.sqrt 2 / 2 : ℝ) : ℂ) = (Real.sqrt 2 : ℂ) / 2 := by
    push_cast
    ring
  have hr2 : ((Real.sqrt 2 : ℂ) / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, hs2]
    norm_num
  have hnum : Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) *
      ((Real.cos (-(Real.pi / 4)) : ℂ) +
        Complex.I * (Real.sin (3 * (-(Real.pi / 4))) : ℂ)) = -Complex.I := by
    rw [exp_neg_pi_div_four, cos_neg_pi_div_four, sin_three_neg_pi_div_four, hs]
    push_cast
    have h1I : ((1 : ℂ) - Complex.I) ^ 2 = -(2 * Complex.I) := by
      rw [sub_sq, Complex.I_sq]
      ring
    have hfac : (Real.sqrt 2 : ℂ) / 2 + Complex.I * (-((Real.sqrt 2 : ℂ) / 2)) =
        (Real.sqrt 2 : ℂ) / 2 * (1 - Complex.I) := by ring
    rw [hfac]
    have hsq : ((Real.sqrt 2 : ℂ) / 2 * (1 - Complex.I)) *
        ((Real.sqrt 2 : ℂ) / 2 * (1 - Complex.I)) =
          ((Real.sqrt 2 : ℂ) / 2) ^ 2 * ((1 - Complex.I) ^ 2) := by ring
    rw [hsq, hr2, h1I]
    ring
  rw [hnum, basisDenom_at_working_momentum]
  unfold invSqrt2
  push_cast
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  field_simp

/-- At momentum `-π / 4`, the basis-widget transmission block equals `Ubasis` [Childs2009]. -/
theorem basisBlock_at_working_momentum :
    basisBlock (-(Real.pi / 4)) = Ubasis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisBlock, Ubasis, basisT00_at_working_momentum,
      basisT01_at_working_momentum]

/-- The basis-widget block at momentum `-π / 4` satisfies both matrix unitary identities
[Childs2009]. -/
theorem basisBlock_unitary :
    basisBlock (-(Real.pi / 4)) * (basisBlock (-(Real.pi / 4)))ᴴ = 1 ∧
      (basisBlock (-(Real.pi / 4)))ᴴ * basisBlock (-(Real.pi / 4)) = 1 := by
  rw [basisBlock_at_working_momentum]
  exact Ubasis_unitary

end Qatlib.Papers.UniversalWalk08.MainResults.Gates
