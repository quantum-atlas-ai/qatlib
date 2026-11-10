/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.MainResults.InfiniteFamily

open Filter

theorem lemma15_countably_many_iccc_codes
    (q : ℕ) (hq : 2 ≤ q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ᶠ m in atTop, ε < (1 / 4) * (q : ℝ) ^ (m - 1 - m / 2) := by

  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (4 * ε) (show (1 : ℝ) < 2 by norm_num)
  rw [frequently_atTop]
  intro a
  set j := max a (N + 1) with hj
  have hja : a ≤ j := by omega
  have hNj : N + 1 ≤ j := by omega
  refine ⟨2 * j, by omega, ?_⟩
  have hhalf : (2 * j) / 2 = j := Nat.mul_div_cancel_left j (by norm_num)
  have hexp : 2 * j - 1 - (2 * j) / 2 = j - 1 := by rw [hhalf]; omega
  rw [hexp]
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have hpow : (2 : ℝ) ^ N ≤ (q : ℝ) ^ (j - 1) := by
    calc (2 : ℝ) ^ N ≤ (q : ℝ) ^ N := pow_le_pow_left₀ (by norm_num) hqR N
      _ ≤ (q : ℝ) ^ (j - 1) := pow_le_pow_right₀ hq1 (by omega)
  have hlt : 4 * ε < (q : ℝ) ^ (j - 1) := lt_of_lt_of_le hN hpow
  linarith

end Qatlib.Papers.PottsPartEval07.MainResults.InfiniteFamily
