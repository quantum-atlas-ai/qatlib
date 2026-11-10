/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

namespace Qatlib.Papers.HadamardAnn19.MainResults.BooleanReduction

set_option autoImplicit false

def hAnd (qi qj qk δ : ℝ) : ℝ :=
  δ * (3 * qk + qi * qj - 2 * qi * qk - 2 * qj * qk)

def substitutedPair (qi qj qk δ : ℝ) : ℝ :=
  qk + hAnd qi qj qk δ

theorem hAnd_nonneg {qi qj qk δ : ℝ}
    (hi : qi = 0 ∨ qi = 1) (hj : qj = 0 ∨ qj = 1) (hk : qk = 0 ∨ qk = 1)
    (hδ : 0 ≤ δ) : 0 ≤ hAnd qi qj qk δ := by
  unfold hAnd
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
    norm_num <;> try nlinarith [hδ]

theorem hAnd_eq_zero_iff {qi qj qk δ : ℝ}
    (hi : qi = 0 ∨ qi = 1) (hj : qj = 0 ∨ qj = 1) (hk : qk = 0 ∨ qk = 1)
    (hδ : δ ≠ 0) : hAnd qi qj qk δ = 0 ↔ qk = qi * qj := by
  unfold hAnd
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
    norm_num [hδ]

theorem hAnd_and {qi qj δ : ℝ} (hi : qi = 0 ∨ qi = 1) (hj : qj = 0 ∨ qj = 1) :
    hAnd qi qj (qi * qj) δ = 0 := by
  unfold hAnd
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num

theorem substitutedPair_eq_of_and {qi qj δ : ℝ}
    (hi : qi = 0 ∨ qi = 1) (hj : qj = 0 ∨ qj = 1) :
    substitutedPair qi qj (qi * qj) δ = qi * qj := by
  unfold substitutedPair
  rw [hAnd_and hi hj, add_zero]

theorem hAnd_penalty_attained {qi qj c R δ : ℝ}
    (hi : qi = 0 ∨ qi = 1) (hj : qj = 0 ∨ qj = 1)
    (hc : 0 ≤ c) (hR : 0 ≤ R) (hδ : 1 ≤ δ) :
    (∀ qk : ℝ, (qk = 0 ∨ qk = 1) →
        c * R * (qi * qj) ≤ c * R * (qk + hAnd qi qj qk δ)) ∧
      c * R * (qi * qj + hAnd qi qj (qi * qj) δ) = c * R * (qi * qj) := by
  constructor
  · intro qk hk
    have hcR : 0 ≤ c * R := mul_nonneg hc hR
    unfold hAnd
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
      norm_num <;> nlinarith [hcR, hδ]
  · rw [hAnd_and hi hj, add_zero]

end Qatlib.Papers.HadamardAnn19.MainResults.BooleanReduction
