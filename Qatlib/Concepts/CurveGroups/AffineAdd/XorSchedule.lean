/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CurveGroups.AffineAdd.EncodedOracle

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

variable {K : Type*} [Field K] {w : ℕ}

theorem xorPointRun_clean (E : FieldEncoding K w) (x1 y1 x2 y2 : K)
    (hD : x1 ≠ x2)
    (hX : (x1 - x2) - (((y1 - y2) * (x1 - x2)⁻¹)^2) + 3*x2 ≠ 0) :
    let S := (y1 - y2) * (x1 - x2)⁻¹
    let X := (x1 - x2) - S^2 + 3*x2
    xorPointRun E x2 y2 (E.encode x1) (E.encode y1) =
      ⟨E.encode (-X + x2), E.encode (S*X - y2), E.encode 0, E.encode 0⟩ := by
  have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hD
  have hs : ((y1-y2)*(x1-x2)⁻¹)*(x1-x2) = y1-y2 := by
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  have hi : ((x1-x2)-((y1-y2)*(x1-x2)⁻¹)^2+3*x2)⁻¹ *
      (((y1-y2)*(x1-x2)⁻¹)*((x1-x2)-((y1-y2)*(x1-x2)⁻¹)^2+3*x2)) =
      (y1-y2)*(x1-x2)⁻¹ := by
    rw [mul_left_comm, inv_mul_cancel₀ hX, mul_one]
  dsimp only
  simp only [xorPointRun, shiftBits_apply, E.decode_encode, xorBits_zero,
    sub_eq_add_neg] at *
  simp only [hs, xorBits_uncompute, E.decode_encode, E.encode_zero,
    xorBits_zero, hi, negateBits_apply, shiftBits_apply]

theorem xorPointRun_zero_second (E : FieldEncoding K w) (x1 y1 x2 y2 : K)
    (hD : x1 ≠ x2)
    (hX : (x1-x2)-((y1-y2)*(x1-x2)⁻¹)^2+3*x2 = 0) :
    xorPointRun E x2 y2 (E.encode x1) (E.encode y1) =
      ⟨E.encode x2, E.encode (-y2), E.encode ((y1-y2)*(x1-x2)⁻¹), E.encode 0⟩ := by
  have hd : x1-x2 ≠ 0 := sub_ne_zero.mpr hD
  have hs : ((y1-y2)*(x1-x2)⁻¹)*(x1-x2) = y1-y2 := by
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  simp only [xorPointRun, shiftBits_apply, E.decode_encode, xorBits_zero,
    sub_eq_add_neg] at *
  have hz : ∀ r, xorBits E 0 r = r := by
    intro r
    simp [xorBits, E.encode_zero]
  have hd0 : E.decode 0 = 0 := by rw [← E.encode_zero, E.decode_encode]
  have hn0 : negateBits E 0 = 0 := by
    simpa only [E.encode_zero, neg_zero] using negateBits_apply E 0
  have hs0 : ∀ c, shiftBits E c 0 = E.encode c := by
    intro c
    simpa only [E.encode_zero, zero_add] using shiftBits_apply E c 0
  simp only [hs, xorBits_uncompute, E.decode_encode, E.encode_zero,
    xorBits_zero, hX, inv_zero, mul_zero, hd0, hz, hn0, hs0]

end Qatlib.Concepts.CurveGroups.AffineAdd
