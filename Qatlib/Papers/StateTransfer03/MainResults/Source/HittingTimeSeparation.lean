/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Growth of the stated hitting-time scales

`classicalHittingTimeOnelink` and `classicalHittingTimeTwolink` encode the exponential scales `2
^ d` and `3 ^ d`, while the quantum quantities are fixed constants. The file proves
monotonicity, unboundedness, and domination of any fixed multiple of the quantum scales. See
[ChristandlEtAl2004].

## Main statements

* `exponential_separation_onelink`: the scale `2 ^ d` exceeds any real bound.
* `exponential_separation_twolink`: the scale `3 ^ d` exceeds any real bound.
* `hitting_time_ratio_unbounded_onelink`: the one-link classical scale exceeds every fixed
  multiple of its quantum scale.

## References

* [Christandl et al., 2004][ChristandlEtAl2004]
-/

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

set_option autoImplicit false

noncomputable section

/-- The stated one-link classical hitting-time scale, defined as `2 ^ d`. -/
def classicalHittingTimeOnelink (d : ℕ) : ℕ := 2 ^ d

/-- The stated two-link classical hitting-time scale, defined as `3 ^ d`. -/
def classicalHittingTimeTwolink (d : ℕ) : ℕ := 3 ^ d

/-- The one-link quantum hitting-time constant `π / 2`. -/
def quantumHittingTimeOnelink : ℝ := Real.pi / 2

/-- The two-link quantum hitting-time constant `π / sqrt 2`. -/
def quantumHittingTimeTwolink : ℝ := Real.pi / Real.sqrt 2

/-- For every dimension parameter, the one-link quantum hitting-time constant equals `π / 2`. -/
theorem quantum_hitting_time_onelink_constant (_d : ℕ) :
    quantumHittingTimeOnelink = Real.pi / 2 :=
  rfl

/-- For every dimension parameter, the two-link quantum hitting-time constant equals `π / sqrt
2`. -/
theorem quantum_hitting_time_twolink_constant (_d : ℕ) :
    quantumHittingTimeTwolink = Real.pi / Real.sqrt 2 :=
  rfl

/-- The one-link classical hitting-time scale is strictly increasing in the dimension. -/
theorem classical_hitting_time_onelink_strictMono :
    StrictMono classicalHittingTimeOnelink := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by norm_num) hab

/-- The two-link classical hitting-time scale is strictly increasing in the dimension. -/
theorem classical_hitting_time_twolink_strictMono :
    StrictMono classicalHittingTimeTwolink := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by norm_num) hab

/-- The one-link classical hitting-time scale exceeds every prescribed real bound in some
dimension. See [ChristandlEtAl2004]. -/
theorem exponential_separation_onelink :
    ∀ C : ℝ, ∃ d : ℕ, C < (classicalHittingTimeOnelink d : ℝ) := by
  intro C
  obtain ⟨d, hd⟩ := exists_nat_gt C
  refine ⟨d + 1, ?_⟩
  have hstep : (d : ℝ) < ((2 : ℝ)) ^ (d + 1) := by
    have hpow : (d : ℝ) < ((2 : ℝ)) ^ d := by
      exact_mod_cast Nat.lt_two_pow_self (n := d)
    have hmono : ((2 : ℝ)) ^ d ≤ ((2 : ℝ)) ^ (d + 1) := by
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ d)
    linarith
  unfold classicalHittingTimeOnelink
  push_cast
  linarith

/-- The two-link classical hitting-time scale exceeds every prescribed real bound in some
dimension. See [ChristandlEtAl2004]. -/
theorem exponential_separation_twolink :
    ∀ C : ℝ, ∃ d : ℕ, C < (classicalHittingTimeTwolink d : ℝ) := by
  intro C
  obtain ⟨d, hd⟩ := exists_nat_gt C
  refine ⟨d + 1, ?_⟩
  have hstep : (d : ℝ) < ((3 : ℝ)) ^ (d + 1) := by
    have h2 : (d : ℝ) < ((2 : ℝ)) ^ d := by
      exact_mod_cast Nat.lt_two_pow_self (n := d)
    have h23 : ((2 : ℝ)) ^ d ≤ ((3 : ℝ)) ^ d := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) d
    have hmono : ((3 : ℝ)) ^ d ≤ ((3 : ℝ)) ^ (d + 1) := by
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ d)
    linarith
  unfold classicalHittingTimeTwolink
  push_cast
  linarith

/-- For every real `C`, some one-link dimension has classical hitting-time scale greater than
`C` times the quantum constant. See [ChristandlEtAl2004]. -/
theorem hitting_time_ratio_unbounded_onelink :
    ∀ C : ℝ, ∃ d : ℕ,
      C * quantumHittingTimeOnelink < (classicalHittingTimeOnelink d : ℝ) := by
  intro C
  exact exponential_separation_onelink (C * quantumHittingTimeOnelink)

/-- For every real `C`, some two-link dimension has classical hitting-time scale greater than
`C` times the quantum constant. See [ChristandlEtAl2004]. -/
theorem hitting_time_ratio_unbounded_twolink :
    ∀ C : ℝ, ∃ d : ℕ,
      C * quantumHittingTimeTwolink < (classicalHittingTimeTwolink d : ℝ) := by
  intro C
  exact exponential_separation_twolink (C * quantumHittingTimeTwolink)

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
