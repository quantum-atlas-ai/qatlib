/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CurveGroups.AffineAdd.ReversibleWord

/-!
# Encoded addition agrees with curve addition

This module proves that `sourcePermutation` computes the native curve group sum on encoded
affine inputs satisfying the two inversion domain conditions, with clean auxiliary registers. It
connects the reversible word to the elliptic curve arithmetic setting of [RoettelerEtAl2017].

## Main statements

* `sourcePermutation_native`: encoded affine addition computes the group sum.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

open WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K] {w : ℕ}

/-- For nonsingular affine inputs with distinct X coordinates and the negative double exclusion,
`sourcePermutation` produces an encoded affine representative of their sum with zero
auxiliary registers. -/
theorem sourcePermutation_native (E : FieldEncoding K w) {a b x1 y1 x2 y2 : K}
    (h1 : (shortCurve a b).Nonsingular x1 y1)
    (h2 : (shortCurve a b).Nonsingular x2 y2) (hx : x1 ≠ x2)
    (hminus2 : Point.some x1 y1 h1 ≠ -(Point.some x2 y2 h2 + Point.some x2 y2 h2)) :
    ∃ x3 y3, ∃ h3 : (shortCurve a b).Nonsingular x3 y3,
      Point.some x1 y1 h1 + Point.some x2 y2 h2 = Point.some x3 y3 h3 ∧
      sourcePermutation E x2 y2 ⟨E.encode x1,E.encode y1,0,0⟩ =
        ⟨E.encode x3,E.encode y3,0,0⟩ := by
  obtain ⟨h3, he⟩ := native_secant h1 h2 hx
  refine ⟨_, _, h3, he, ?_⟩
  have hsecond := second_inverse_nonzero h1 h2 hx hminus2
  have hX : (x1-x2)-((y1-y2)*(x1-x2)⁻¹)^2+3*x2 ≠ 0 := by
    intro hz
    apply hsecond
    unfold addX slope
    rw [div_eq_mul_inv]
    linear_combination hz
  rw [sourcePermutation_clean_apply, xorPointRun_clean E x1 y1 x2 y2 hx hX]
  have hs : (y1-y2)*(x1-x2)⁻¹ = slope x1 y1 x2 y2 := (div_eq_mul_inv ..).symm
  have hxx : -((x1-x2)-((y1-y2)*(x1-x2)⁻¹)^2+3*x2)+x2 =
      addX x1 x2 (slope x1 y1 x2 y2) := by rw [hs]; unfold addX; ring
  have hyy : ((y1-y2)*(x1-x2)⁻¹)*((x1-x2)-((y1-y2)*(x1-x2)⁻¹)^2+3*x2)-y2 =
      addY x1 y1 (addX x1 x2 (slope x1 y1 x2 y2)) (slope x1 y1 x2 y2) := by
    have hd : x1-x2 ≠ 0 := sub_ne_zero.mpr hx
    unfold addY addX slope
    field_simp
    ring
  simp only [hxx, hyy, E.encode_zero]

end Qatlib.Concepts.CurveGroups.AffineAdd
