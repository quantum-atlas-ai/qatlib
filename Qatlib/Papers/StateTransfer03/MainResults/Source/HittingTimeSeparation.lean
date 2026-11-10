/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

def classicalHittingTimeOnelink (d : ℕ) : ℕ := 2 ^ d

def classicalHittingTimeTwolink (d : ℕ) : ℕ := 3 ^ d

def quantumHittingTimeOnelink : ℝ := Real.pi / 2

def quantumHittingTimeTwolink : ℝ := Real.pi / Real.sqrt 2

theorem quantum_hitting_time_onelink_constant (d : ℕ) :
    quantumHittingTimeOnelink = Real.pi / 2 :=
  rfl

theorem quantum_hitting_time_twolink_constant (d : ℕ) :
    quantumHittingTimeTwolink = Real.pi / Real.sqrt 2 :=
  rfl

theorem classical_hitting_time_onelink_strictMono :
    StrictMono classicalHittingTimeOnelink := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by norm_num) hab

theorem classical_hitting_time_twolink_strictMono :
    StrictMono classicalHittingTimeTwolink := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by norm_num) hab

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

theorem hitting_time_ratio_unbounded_onelink :
    ∀ C : ℝ, ∃ d : ℕ,
      C * quantumHittingTimeOnelink < (classicalHittingTimeOnelink d : ℝ) := by
  intro C
  exact exponential_separation_onelink (C * quantumHittingTimeOnelink)

theorem hitting_time_ratio_unbounded_twolink :
    ∀ C : ℝ, ∃ d : ℕ,
      C * quantumHittingTimeTwolink < (classicalHittingTimeTwolink d : ℝ) := by
  intro C
  exact exponential_separation_twolink (C * quantumHittingTimeTwolink)

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
