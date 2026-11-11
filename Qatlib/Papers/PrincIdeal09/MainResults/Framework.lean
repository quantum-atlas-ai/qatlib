/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic

/-!
# Abstract models for regulator and principal-ideal periods

The records `RegPeriodModel` and `PIPPeriodModel` specify successor and predecessor forms,
approximate real distances, a positive regulator, and interval descriptions of integer-indexed
output functions. The principal-ideal model includes a shifted base function, while the
elementary lemmas extract window membership and predecessor spacing from the recorded hypotheses
[Schmidt2009].

## Main statements

* `RegPeriodModel`: Specifies the one-variable regulator window model.
* `PIPPeriodModel`: Specifies a two-variable window model with a base-shift relation.
* `inWindow_iff`: The output function equals a form exactly on its recorded windows.

## References

* [Schmidt, 2009][Schmidt2009]
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.PrincIdeal09.MainResults

/-- The condition that a natural number is positive, is not a square, and is congruent to zero
or one modulo four. -/
structure IsRealQuadraticDiscriminant (Δ : ℕ) : Prop where

  pos : 0 < Δ

  not_square : ∀ m : ℕ, Δ ≠ m ^ 2

  mod_four : Δ % 4 = 0 ∨ Δ % 4 = 1

/-- An abstract regulator-period model with inverse successor and predecessor maps, approximate
distances, positive regulator, spacing, and a window specification for `reg`. -/
structure RegPeriodModel where

  Form : Type

  instDecEq : DecidableEq Form

  succ : Form → Form

  pred : Form → Form
  succ_pred : ∀ g, succ (pred g) = g
  pred_succ : ∀ g, pred (succ g) = g

  d : Form → ℝ

  delta : Form → ℝ

  R : ℝ
  R_pos : 0 < R

  approx : ∀ g, |d g - delta g| < 1 / 8

  succ_gap : ∀ g, 1 / 4 < d (succ g) - d g

  reg : ℤ → Form

  reg_spec : ∀ (x : ℤ) (g : Form),
    reg x = g ↔
      ∃ k : ℤ, d g + (k : ℝ) * R ≤ (x : ℝ) / 4 ∧ (x : ℝ) / 4 < d (succ g) + (k : ℝ) * R

namespace RegPeriodModel

variable (M : RegPeriodModel)

/-- The condition that `x / 4` lies between a form's distance and its successor's distance after
an integer regulator shift. -/
def InWindow (x : ℤ) (g : M.Form) : Prop :=
  ∃ k : ℤ, M.d g + (k : ℝ) * M.R ≤ (x : ℝ) / 4 ∧
    (x : ℝ) / 4 < M.d (M.succ g) + (k : ℝ) * M.R

/-- The regulator output is `g` if and only if the input lies in a window for `g`. -/
theorem inWindow_iff (x : ℤ) (g : M.Form) : M.reg x = g ↔ M.InWindow x g :=
  M.reg_spec x g

/-- Two forms equal to the regulator output at the same input are equal. -/
theorem reg_unique {x : ℤ} {g h : M.Form} (hg : M.reg x = g) (hh : M.reg x = h) : g = h := by
  rw [← hg, hh]

/-- Applying the predecessor map after the successor map returns the original form. -/
theorem pred_succ_apply (g : M.Form) : M.pred (M.succ g) = g := M.pred_succ g

/-- The distance from a form's predecessor to that form is greater than one quarter in a
regulator-period model. -/
theorem pred_gap (g : M.Form) : 1 / 4 < M.d g - M.d (M.pred g) := by
  have h := M.succ_gap (M.pred g)
  rwa [M.succ_pred] at h

end RegPeriodModel

/-- An abstract two-variable principal-ideal period model with form distances, a positive
regulator and integer shift, a base-shift relation, and a window specification for `pip`. -/
structure PIPPeriodModel where

  Form : Type
  instDecEq : DecidableEq Form

  succ : Form → Form

  pred : Form → Form
  succ_pred : ∀ g, succ (pred g) = g
  pred_succ : ∀ g, pred (succ g) = g

  d : Form → ℝ

  delta : Form → ℝ

  R : ℝ
  R_pos : 0 < R

  n : ℤ
  n_pos : 0 < n

  S : ℝ

  approx : ∀ g, |d g - delta g| < 1 / 8

  succ_gap : ∀ g, 1 / 4 < d (succ g) - d g

  base : ℤ → ℝ

  base_period : ∀ x : ℤ, base (x + n) = base x - S / 4

  pip : ℤ → ℤ → Form

  pip_spec : ∀ (x₁ x₂ : ℤ) (g : Form),
    pip x₁ x₂ = g ↔
      ∃ k : ℤ, d g + (k : ℝ) * R + base x₁ ≤ (x₂ : ℝ) / 4 ∧
        (x₂ : ℝ) / 4 < d (succ g) + (k : ℝ) * R + base x₁

namespace PIPPeriodModel

variable (M : PIPPeriodModel)

/-- The distance from a form's predecessor to that form is greater than one quarter in a
principal-ideal period model. -/
theorem pred_gap (g : M.Form) : 1 / 4 < M.d g - M.d (M.pred g) := by
  have h := M.succ_gap (M.pred g)
  rwa [M.succ_pred] at h

end PIPPeriodModel

end Qatlib.Papers.PrincIdeal09.MainResults
