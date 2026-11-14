/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Stability of Boolean postselection

This module defines pointwise relative error by `MultiplicativeClose` and normalizes a Boolean
slice using `postSelect`. A relative error of 1/10 gives conditional multiplicative bounds 9/11
and 11/9, with explicit acceptance thresholds; conditional probabilities and postselected
measurement outcomes are standard in quantum information [NielsenChuang2010].

## Main statements

* `postSelect_ratio`: Postselection preserves the stated multiplicative comparison.
* `postSelect_thresholds`: Conditional probabilities at least 2/3 or at most 1/3 yield bounds
  0.54 and 0.41.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Foundations.ProbabilityCore.Conditioning

open scoped BigOperators

variable {ι : Type*}
variable {θ : Type*}

/-- Pointwise relative closeness of real-valued functions: `|p z - q z| ≤ ε * q z` for every
`z`. -/
def MultiplicativeClose (p q : θ → ℝ) (ε : ℝ) : Prop :=
  ∀ z, |p z - q z| ≤ ε * q z

/-- Relative error at most 1/10 bounds `p z` between 9/10 and 11/10 times `q z`. -/
theorem multiplicative_bounds {p q : θ → ℝ}
    (h : MultiplicativeClose p q (1/10)) (z : θ) :
    (9 / 10 : ℝ) * q z ≤ p z ∧ p z ≤ (11 / 10 : ℝ) * q z := by
  have hz := h z
  have h1 := (abs_le.mp hz).1
  have h2 := (abs_le.mp hz).2
  constructor <;> linarith

/-- The normalized Boolean weight at `b` in the slice indexed by `r`, dividing `p (b, r)` by the
sum of the two slice weights. -/
noncomputable def postSelect (p : Bool × ι → ℝ) (r : ι) (b : Bool) : ℝ :=
  p (b, r) / (p (false, r) + p (true, r))

/-- For nonnegative reference slice weights of positive total mass, relative error 1/10 bounds
each postselected weight between 9/11 and 11/9 times its reference value. -/
theorem postSelect_ratio_one {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r)) (b : Bool) :
    (9 / 11 : ℝ) * postSelect q r b ≤ postSelect p r b ∧
      postSelect p r b ≤ (11 / 9 : ℝ) * postSelect q r b := by
  obtain ⟨hp0l, hp0u⟩ := multiplicative_bounds h (false, r)
  obtain ⟨hp1l, hp1u⟩ := multiplicative_bounds h (true, r)
  have hSl : (9 / 10 : ℝ) * (q (false, r) + q (true, r))
      ≤ p (false, r) + p (true, r) := by linarith
  have hSu : p (false, r) + p (true, r)
      ≤ (11 / 10 : ℝ) * (q (false, r) + q (true, r)) := by linarith
  have hTpos : 0 < p (false, r) + p (true, r) := lt_of_lt_of_le (by linarith) hSl
  have hqSpos : 0 < (9 / 10 : ℝ) * (q (false, r) + q (true, r)) := by linarith
  have hb0 : b = false ∨ b = true := by cases b <;> simp
  rcases hb0 with rfl | rfl
  · have hqb : 0 ≤ q (false, r) := hq0
    have hpbl : (9 / 10 : ℝ) * q (false, r) ≤ p (false, r) := hp0l
    have hpbu : p (false, r) ≤ (11 / 10 : ℝ) * q (false, r) := hp0u
    have hqden : (0 : ℝ) < q (false, r) + q (true, r) := hqS
    constructor
    · have h1 : (9 / 11 : ℝ) * (q (false, r) / (q (false, r) + q (true, r)))
          = ((9 / 10 : ℝ) * q (false, r))
              / ((11 / 10 : ℝ) * (q (false, r) + q (true, r))) := by
        field_simp [ne_of_gt hqS]
      rw [postSelect, postSelect, h1]
      calc ((9 / 10 : ℝ) * q (false, r))
            / ((11 / 10 : ℝ) * (q (false, r) + q (true, r)))
          ≤ ((9 / 10 : ℝ) * q (false, r)) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hq0) hTpos hSu
        _ ≤ p (false, r) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_right hpbl hTpos.le
    · have h2 : ((11 / 10 : ℝ) * q (false, r))
            / ((9 / 10 : ℝ) * (q (false, r) + q (true, r)))
          = (11 / 9 : ℝ) * (q (false, r) / (q (false, r) + q (true, r))) := by
        field_simp [ne_of_gt hqS, ne_of_gt hqSpos]
      rw [postSelect, postSelect, ← h2]
      calc p (false, r) / (p (false, r) + p (true, r))
          ≤ ((11 / 10 : ℝ) * q (false, r)) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_right hpbu hTpos.le
        _ ≤ ((11 / 10 : ℝ) * q (false, r))
              / ((9 / 10 : ℝ) * (q (false, r) + q (true, r))) :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hq0) hqSpos hSl
  · have hqb : 0 ≤ q (true, r) := hq1
    have hpbl : (9 / 10 : ℝ) * q (true, r) ≤ p (true, r) := hp1l
    have hpbu : p (true, r) ≤ (11 / 10 : ℝ) * q (true, r) := hp1u
    constructor
    · have h1 : (9 / 11 : ℝ) * (q (true, r) / (q (false, r) + q (true, r)))
          = ((9 / 10 : ℝ) * q (true, r))
              / ((11 / 10 : ℝ) * (q (false, r) + q (true, r))) := by
        field_simp [ne_of_gt hqS]
      rw [postSelect, postSelect, h1]
      calc ((9 / 10 : ℝ) * q (true, r))
            / ((11 / 10 : ℝ) * (q (false, r) + q (true, r)))
          ≤ ((9 / 10 : ℝ) * q (true, r)) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hq1) hTpos hSu
        _ ≤ p (true, r) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_right hpbl hTpos.le
    · have h2 : ((11 / 10 : ℝ) * q (true, r))
            / ((9 / 10 : ℝ) * (q (false, r) + q (true, r)))
          = (11 / 9 : ℝ) * (q (true, r) / (q (false, r) + q (true, r))) := by
        field_simp [ne_of_gt hqS, ne_of_gt hqSpos]
      rw [postSelect, postSelect, ← h2]
      calc p (true, r) / (p (false, r) + p (true, r))
          ≤ ((11 / 10 : ℝ) * q (true, r)) / (p (false, r) + p (true, r)) :=
            div_le_div_of_nonneg_right hpbu hTpos.le
        _ ≤ ((11 / 10 : ℝ) * q (true, r))
              / ((9 / 10 : ℝ) * (q (false, r) + q (true, r))) :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hq1) hqSpos hSl

/-- Under relative error 1/10 and nonnegative reference slice weights of positive total mass,
postselection preserves multiplicative bounds 9/11 and 11/9. -/
theorem postSelect_ratio {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r)) (b : Bool) :
    (9 / 11 : ℝ) * postSelect q r b ≤ postSelect p r b ∧
      postSelect p r b ≤ (11 / 9 : ℝ) * postSelect q r b :=
  postSelect_ratio_one h hq0 hq1 hqS b

/-- The postselected true weight of `p` is nonnegative under the stated relative-error and
reference-mass assumptions. -/
theorem postSelect_nonneg {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (_hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r)) :
    0 ≤ postSelect p r true := by
  obtain ⟨hp0l, _⟩ := multiplicative_bounds h (false, r)
  obtain ⟨hp1l, _⟩ := multiplicative_bounds h (true, r)
  have hSl : (9 / 10 : ℝ) * (q (false, r) + q (true, r))
      ≤ p (false, r) + p (true, r) := by linarith
  have hTpos : 0 < p (false, r) + p (true, r) := lt_of_lt_of_le (by linarith) hSl
  have hp1nn : 0 ≤ p (true, r) := le_trans (mul_nonneg (by norm_num) hq1) hp1l
  exact div_nonneg hp1nn hTpos.le

/-- Under relative error 1/10 and a nonnegative reference slice of positive mass, a reference
true probability at least 2/3 yields a probability at least 0.54, while one at most 1/3
yields a probability at most 0.41. -/
theorem postSelect_thresholds {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r)) :
    (2 / 3 ≤ postSelect q r true → (0.54 : ℝ) ≤ postSelect p r true) ∧
      (postSelect q r true ≤ 1 / 3 → postSelect p r true ≤ (0.41 : ℝ)) := by
  obtain ⟨hlow, hup⟩ := postSelect_ratio h hq0 hq1 hqS true
  constructor
  · intro hyes
    nlinarith [hlow, hyes]
  · intro hno
    nlinarith [hup, hno]

/-- If the reference postselected true probability is at least 2/3, relative error 1/10 gives a
postselected true probability at least 0.54 under the stated slice-mass assumptions. -/
theorem postSelect_yes_lower {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r))
    (hyes : 2 / 3 ≤ postSelect q r true) :
    (0.54 : ℝ) ≤ postSelect p r true := by
  obtain ⟨hlow, _⟩ := postSelect_ratio h hq0 hq1 hqS true
  nlinarith [hlow, hyes]

/-- If the reference postselected true probability is at most 1/3, relative error 1/10 gives a
postselected true probability at most 0.41 under the stated slice-mass assumptions. -/
theorem postSelect_no_upper {p q : Bool × ι → ℝ} {r : ι}
    (h : MultiplicativeClose p q (1/10))
    (hq0 : 0 ≤ q (false, r)) (hq1 : 0 ≤ q (true, r))
    (hqS : 0 < q (false, r) + q (true, r))
    (hno : postSelect q r true ≤ 1 / 3) :
    postSelect p r true ≤ (0.41 : ℝ) := by
  obtain ⟨_, hup⟩ := postSelect_ratio h hq0 hq1 hqS true
  nlinarith [hup, hno]

end Qatlib.Foundations.ProbabilityCore.Conditioning
