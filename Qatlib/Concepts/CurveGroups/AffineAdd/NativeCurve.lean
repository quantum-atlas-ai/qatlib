/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Qatlib.Concepts.CurveGroups.AffineAdd.PointAddition

/-!
# Affine addition in the native curve group

This module connects the secant coordinate formulas and the arithmetic register schedule to
Mathlib curve point addition. It verifies the second inversion condition and auxiliary register
cleanup on the stated domain, and defines point translation permutations. The reversible
addition setting is that of [RoettelerEtAl2017].

## Main statements

* `native_secant`: the secant formula for distinct X coordinates.
* `corrected_schedule`: point addition with cleared auxiliary registers.
* `controlledTranslation`: controlled addition as a permutation.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

open WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K]

/-- The short Weierstrass curve with coefficients `a` and `b` and all other Weierstrass
coefficients zero. -/
def shortCurve (a b : K) : WeierstrassCurve.Affine K :=
  ⟨0, 0, 0, a, b⟩

/-- For nonsingular affine points with distinct X coordinates, the secant coordinates are
nonsingular and represent their group sum. -/
theorem native_secant {a b x1 y1 x2 y2 : K}
    (h1 : (shortCurve a b).Nonsingular x1 y1)
    (h2 : (shortCurve a b).Nonsingular x2 y2) (hx : x1 ≠ x2) :
    ∃ h3 : (shortCurve a b).Nonsingular
        (addX x1 x2 (slope x1 y1 x2 y2))
        (addY x1 y1 (addX x1 x2 (slope x1 y1 x2 y2)) (slope x1 y1 x2 y2)),
      Point.some x1 y1 h1 + Point.some x2 y2 h2 = Point.some _ _ h3 := by
  have hn := nonsingular_add h1 h2 (fun h => hx h.1)
  have hs : (shortCurve a b).slope x1 x2 y1 y2 = slope x1 y1 x2 y2 :=
    slope_of_X_ne hx
  have heX : (shortCurve a b).addX x1 x2 (slope x1 y1 x2 y2) =
      addX x1 x2 (slope x1 y1 x2 y2) := by simp [shortCurve, addX]
  have heY : (shortCurve a b).addY x1 x2 y1 (slope x1 y1 x2 y2) =
      addY x1 y1 (addX x1 x2 (slope x1 y1 x2 y2)) (slope x1 y1 x2 y2) := by
    simp [WeierstrassCurve.Affine.addY, negY, negAddY, shortCurve, addX, addY]
    ring
  rw [hs, heX, heY] at hn
  refine ⟨hn, ?_⟩
  have hadd := Point.add_of_X_ne (h₁ := h1) (h₂ := h2) hx
  simpa only [hs, heX, heY] using hadd

/-- If the first point is not the negative double of the second and their X coordinates differ,
the sum X coordinate differs from `x2`. -/
theorem second_inverse_nonzero {a b x1 y1 x2 y2 : K}
    (h1 : (shortCurve a b).Nonsingular x1 y1)
    (h2 : (shortCurve a b).Nonsingular x2 y2) (hx : x1 ≠ x2)
    (hminus2 : Point.some x1 y1 h1 ≠ -(Point.some x2 y2 h2 + Point.some x2 y2 h2)) :
    x2 ≠ addX x1 x2 (slope x1 y1 x2 y2) := by
  obtain ⟨h3, he⟩ := native_secant h1 h2 hx
  intro hxx
  rcases Point.X_eq_iff.mp hxx.symm with hp | hp
  · rw [← he] at hp
    have hz : Point.some x1 y1 h1 = 0 := by
      exact add_right_cancel (hp.trans (zero_add _).symm)
    exact Point.some_ne_zero h1 hz
  · rw [← he] at hp
    apply hminus2
    have hz : Point.some x1 y1 h1 + (Point.some x2 y2 h2 + Point.some x2 y2 h2) = 0 := by
      rw [← add_assoc, hp, neg_add_cancel]
    exact eq_neg_iff_add_eq_zero.mpr hz

/-- Under the distinct coordinate and negative double exclusions, the enabled arithmetic
schedule represents the curve group sum and clears both auxiliary registers. -/
theorem corrected_schedule {a b x1 y1 x2 y2 : K}
    (h1 : (shortCurve a b).Nonsingular x1 y1)
    (h2 : (shortCurve a b).Nonsingular x2 y2) (hx : x1 ≠ x2)
    (hminus2 : Point.some x1 y1 h1 ≠ -(Point.some x2 y2 h2 + Point.some x2 y2 h2)) :
    (∃ h3 : (shortCurve a b).Nonsingular
        (run true x2 y2 x1 y1).x1 (run true x2 y2 x1 y1).y1,
      Point.some x1 y1 h1 + Point.some x2 y2 h2 = Point.some _ _ h3) ∧
    (run true x2 y2 x1 y1).lam = 0 ∧ (run true x2 y2 x1 y1).t0 = 0 := by
  obtain ⟨h3, he⟩ := native_secant h1 h2 hx
  obtain ⟨hxout, hyout⟩ := alg1_ctrl_true hx
  constructor
  · rw [hxout, hyout]
    exact ⟨h3, he⟩
  · exact alg1_ancillas_cleared hx (second_inverse_nonzero h1 h2 hx hminus2)

/-- Translation by a fixed curve point as a permutation of the curve point group. -/
def pointTranslation (a b : K) (P : (shortCurve a b).Point) :
    Equiv.Perm (shortCurve a b).Point where
  toFun Q := Q + P
  invFun Q := Q - P
  left_inv Q := add_sub_cancel_right Q P
  right_inv Q := sub_add_cancel Q P

/-- The permutation that adds `P` to the point component exactly when the Boolean control is
true. -/
def controlledTranslation (a b : K) (P : (shortCurve a b).Point) :
    Equiv.Perm (Bool × (shortCurve a b).Point) where
  toFun q := (q.1, if q.1 then pointTranslation a b P q.2 else q.2)
  invFun q := (q.1, if q.1 then (pointTranslation a b P).symm q.2 else q.2)
  left_inv := by rintro ⟨c, q⟩; cases c <;> simp
  right_inv := by rintro ⟨c, q⟩; cases c <;> simp

/-- Controlled translation adds `P` for a true control and fixes the point for a false control. -/
theorem controlled_translation_apply (a b : K) (P Q : (shortCurve a b).Point) :
    controlledTranslation a b P (true, Q) = (true, Q + P) ∧
    controlledTranslation a b P (false, Q) = (false, Q) := by
  constructor <;> rfl

end Qatlib.Concepts.CurveGroups.AffineAdd
