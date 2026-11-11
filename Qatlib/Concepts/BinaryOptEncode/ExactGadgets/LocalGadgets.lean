/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Exact local optimization gadgets

This module gives local algebraic encodings for integer sign selection, Boolean conjunction, and
common piecewise-linear functions. The Rosenberg polynomial `rosenberg` enforces a Boolean
product, while signed selectors represent absolute value, ReLU, parametric ReLU, and hinge loss.
These identities provide components for optimization encodings of neural networks as in
[SongEtAl2023].

## Main statements

* `sign_constraints_iff`: nonnegative integer slack variables characterize `signPlus`.
* `rosenberg_exact`: the Boolean product penalty is nonnegative, vanishes exactly on correct
  products, and has gap at least one otherwise.
* `rosenberg_substitution`: a sufficiently large penalty makes Boolean product substitution
  exact.
* `selector_relu`, `selector_prelu`, `selector_hinge`: signed-selector formulas for the
  corresponding piecewise-linear functions.

## References

* [Song et al., 2023][SongEtAl2023]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.BinaryOptEncode.ExactGadgets

/-- The integer sign function that returns 1 for nonnegative inputs and −1 for negative inputs. -/
def signPlus (s : ℤ) : ℤ := if 0 ≤ s then 1 else -1

/-- For an integer selector a in {−1, 1}, nonnegative integer slack variables r and t satisfying
a·s = r and a + 2r = 1 + t exist exactly when a equals `signPlus` s. -/
theorem sign_constraints_iff (s a : ℤ) (ha : a = 1 ∨ a = -1) :
    (∃ r t : ℤ, 0 ≤ r ∧ 0 ≤ t ∧ a * s = r ∧ a + 2 * r = 1 + t) ↔
      a = signPlus s := by
  constructor
  · rintro ⟨r, t, hr, ht, hprod, hsum⟩
    rcases ha with h | h <;> subst a
    · have hs : 0 ≤ s := by nlinarith
      simp [signPlus, hs]
    · have hs : ¬0 ≤ s := by intro hs; nlinarith
      simp [signPlus, hs]
  · intro hsign
    by_cases hs : 0 ≤ s
    · have h : a = 1 := by simpa [signPlus, hs] using hsign
      rw [h]
      exact ⟨s, 2 * s, hs, by omega, by ring, by ring⟩
    · have h : a = -1 := by simpa [signPlus, hs] using hsign
      rw [h]
      exact ⟨-s, -2 * s - 2, by omega, by omega, by ring, by ring⟩

/-- The real-valued Boolean encoding sending false to zero and true to one. -/
def bitValue (b : Bool) : ℝ := if b then 1 else 0

/-- The Rosenberg penalty polynomial for enforcing that the Boolean variable v equals the
conjunction of u and w. -/
def rosenberg (u w v : Bool) : ℝ :=
  3 * bitValue v + bitValue u * bitValue w -
    2 * bitValue u * bitValue v - 2 * bitValue w * bitValue v

/-- The Rosenberg penalty is nonnegative and vanishes exactly when v is the conjunction of u and
w; otherwise it is at least one. -/
theorem rosenberg_exact (u w v : Bool) :
    0 ≤ rosenberg u w v ∧
      (rosenberg u w v = 0 ↔ v = (u && w)) ∧
      (v ≠ (u && w) → 1 ≤ rosenberg u w v) := by
  cases u <;> cases w <;> cases v <;> norm_num [rosenberg, bitValue]

/-- When the penalty coefficient exceeds |p|, replacing the Boolean product term by an auxiliary
Boolean v and adding its Rosenberg penalty never decreases the objective. Equality holds
exactly when v equals the conjunction of the two factors. -/
theorem rosenberg_substitution (u w v : Bool) (q p penalty : ℝ)
    (hpenalty : |p| < penalty) :
    q + p * (bitValue u * bitValue w) ≤ q + p * bitValue v + penalty * rosenberg u w v ∧
      (q + p * (bitValue u * bitValue w) = q + p * bitValue v + penalty * rosenberg u w v ↔
        v = (u && w)) := by
  cases u <;> cases w <;> cases v <;> norm_num [rosenberg, bitValue]
  all_goals constructor <;> nlinarith [le_abs_self p, neg_le_abs p]

/-- A selector t in {−1, 1} with t·s nonnegative satisfies t·s = |s|. -/
theorem selector_abs (s t : ℝ) (ht : t = 1 ∨ t = -1) (h : 0 ≤ t * s) :
    t * s = |s| := by
  rcases ht with rfl | rfl
  · simp only [one_mul] at h ⊢
    exact (abs_of_nonneg h).symm
  · have hs : s ≤ 0 := by linarith
    simpa using (abs_of_nonpos hs).symm

/-- A selector t in {−1, 1} with t·s nonnegative represents ReLU by (t·s + s)/2 = max(0, s). -/
theorem selector_relu (s t : ℝ) (ht : t = 1 ∨ t = -1) (h : 0 ≤ t * s) :
    (t * s + s) / 2 = max 0 s := by
  rw [selector_abs s t ht h]
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs, max_eq_right hs]
    ring
  · rw [abs_of_neg (lt_of_not_ge hs), max_eq_left (le_of_not_ge hs)]
    ring

/-- A selector t in {−1, 1} with t·s nonnegative represents parametric ReLU by ((1 − alpha)t +
(1 + alpha))s/2, equal to s for nonnegative s and alpha·s otherwise. -/
theorem selector_prelu (s t alpha : ℝ) (ht : t = 1 ∨ t = -1) (h : 0 ≤ t * s) :
    ((1 - alpha) * t + (1 + alpha)) * s / 2 =
      if 0 ≤ s then s else alpha * s := by
  have ha := selector_abs s t ht h
  calc
    ((1 - alpha) * t + (1 + alpha)) * s / 2 =
        ((1 - alpha) * (t * s) + (1 + alpha) * s) / 2 := by ring
    _ = ((1 - alpha) * |s| + (1 + alpha) * s) / 2 := by rw [ha]
    _ = if 0 ≤ s then s else alpha * s := by
      split_ifs with hs
      · rw [abs_of_nonneg hs]
        ring
      · rw [abs_of_neg (lt_of_not_ge hs)]
        ring

/-- A sign selector for the margin residual 1 − y·output represents hinge loss as (t(1 −
y·output) + 1 − y·output)/2 = max(0, 1 − y·output). -/
theorem selector_hinge (y output t : ℝ) (ht : t = 1 ∨ t = -1)
    (h : 0 ≤ t * (1 - y * output)) :
    (t * (1 - y * output) + 1 - y * output) / 2 = max 0 (1 - y * output) := by
  convert selector_relu (1 - y * output) t ht h using 1
  ring

end Qatlib.Concepts.BinaryOptEncode.ExactGadgets
