/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HidShiftQuad09.MainResults.Defs
import Qatlib.Papers.HidShiftQuad09.MainResults.FindCloseQuadratic
import Qatlib.Papers.HidShiftQuad09.MainResults.ShiftedLargeU3

/-!
# Bent hidden-shift recovery and coefficient counts

This module proves the Fourier recovery identity for a bent Boolean function and its hidden
translate in the setting of [Roetteler2009]. Their coefficient ratio is the binary character of
the hidden shift, so character orthogonality gives a peak supported exactly at that shift.

It also defines `classicalBasisQueryCount`, proves a quadratic lower bound for that expression,
and counts the binary quadratic-pair and linear coefficient arrays. The theorem
`source_mainResult_linearQueries` collects these algebraic and counting identities.

## Main statements

* `hiddenShift_fourier_ratio`: expresses Fourier coefficient ratios as shift characters.
* `hiddenShift_recovery_peak`: identifies the unique peak of the character sum.
* `quadraticFormCount`: evaluates the coefficient-array count.

## References

* [Roetteler, 2009][Roetteler2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HidShiftQuad09.MainResults.LinearQueryIdentification

open scoped BigOperators RealInnerProductSpace
open Qatlib.Papers.HidShiftQuad09.MainResults.Defs
open Qatlib.Papers.HidShiftQuad09.MainResults.ShiftedLargeU3

/-- The real-valued count `1 + n + n * (n - 1) / 2` associated with constant, linear, and
quadratic basis queries. -/
def classicalBasisQueryCount (n : ℕ) : ℝ :=
  1 + (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) / 2

/-- For positive `n`, the defined basis-query count is at least `n ^ 2 / 4`. [Roetteler2009]. -/
theorem classicalBasisQueryCount_ge (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ 2 / 4 ≤ classicalBasisQueryCount n := by
  unfold classicalBasisQueryCount
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- The product of the counts of binary quadratic-pair and linear coefficient arrays equals `2 ^
(n * (n + 1) / 2)`. [Roetteler2009]. -/
theorem quadraticFormCount (n : ℕ) :
    Fintype.card (Fin (n * (n - 1) / 2) → ZMod 2) *
      Fintype.card (Fin n → ZMod 2) = 2 ^ (n * (n + 1) / 2) := by
  have hexp : n * (n - 1) / 2 + n = n * (n + 1) / 2 := by

    calc n * (n - 1) / 2 + n
        = n.choose 2 + n.choose 1 := by
          rw [Nat.choose_two_right, Nat.choose_one_right]
      _ = (n + 1).choose 2 := by
          have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := by
            simpa using (Nat.choose_succ_succ n 1)
          omega
      _ = n * (n + 1) / 2 := by
          rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (n + 1) n]
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin,
    Fintype.card_fin, ← pow_add, hexp]

/-- For a bent function and its hidden translate by `s`, the ratio of their Fourier coefficients
at `w` equals `chi w s`. [Roetteler2009]. -/
theorem hiddenShift_fourier_ratio {n : ℕ} (f g : Cube n → ZMod 2) (s : Cube n)
    (hb : bent f) (hshift : HiddenShift f g s) (w : Cube n) :
    fourierCoeff g w / fourierCoeff f w = chi w s := by
  have hg : g = fun x => f (x + s) := funext hshift
  rw [hg, fourierCoeff_shift]
  have hne : fourierCoeff f w ≠ 0 := bent_fourierCoeff_ne_zero f hb w
  field_simp [hne]

/-- For a bent function and its hidden translate, the Fourier-character sum of coefficient
ratios is supported at the shift `s`, where it equals `2 ^ n`. [Roetteler2009]. -/
theorem hiddenShift_recovery_peak {n : ℕ} (f g : Cube n → ZMod 2) (s : Cube n)
    (hb : bent f) (hshift : HiddenShift f g s) (x : Cube n) :
    (∑ w : Cube n, (fourierCoeff g w / fourierCoeff f w) * chi w x)
      = if x = s then (2 : ℝ) ^ n else 0 := by
  have hr : ∀ w : Cube n, fourierCoeff g w / fourierCoeff f w = chi w s :=
    fun w => hiddenShift_fourier_ratio f g s hb hshift w
  simp only [hr]
  have hmul : ∀ w : Cube n, chi w s * chi w x = chi w (s + x) := by
    intro w; rw [chi_add]
  simp only [hmul]
  exact chi_sum_eq_delta n s x

/-- For positive `n`, the hidden-shift recovery peak identity holds for every bent function and
its translate. The defined classical basis-query count is at least `n ^ 2 / 4`, and the
stated binary coefficient-array count is `2 ^ (n * (n + 1) / 2)`. [Roetteler2009]. -/
theorem source_mainResult_linearQueries (n : ℕ) (hn : 0 < n) :
    (∀ (f g : Cube n → ZMod 2) (s : Cube n), bent f → HiddenShift f g s →
        ∀ x : Cube n,
          (∑ w : Cube n, (fourierCoeff g w / fourierCoeff f w) * chi w x)
            = if x = s then (2 : ℝ) ^ n else 0) ∧
    ((n : ℝ) ^ 2 / 4 ≤ classicalBasisQueryCount n) ∧
    (Fintype.card (Fin (n * (n - 1) / 2) → ZMod 2) *
      Fintype.card (Fin n → ZMod 2) = 2 ^ (n * (n + 1) / 2)) := by
  refine ⟨?_, classicalBasisQueryCount_ge n hn, quadraticFormCount n⟩
  intro f g s hb hshift x
  exact hiddenShift_recovery_peak f g s hb hshift x

end Qatlib.Papers.HidShiftQuad09.MainResults.LinearQueryIdentification
