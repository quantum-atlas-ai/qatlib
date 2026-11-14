/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# An unbounded precision inequality

The theorem `lemma15_countably_many_iccc_codes` proves that the numerical precision inequality ε
< q^(m - 1 - m / 2) / 4 holds for arbitrarily large natural numbers m when q ≥ 2 and 0 < ε < 1.
Natural-number subtraction and division occur in the exponent; the result supplies the
arithmetic growth step associated with the paper's infinite-family discussion [GeraciLidar2008].

## Main statements

* `lemma15_countably_many_iccc_codes`: The precision inequality holds frequently along the
  natural numbers.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.MainResults.InfiniteFamily

open Filter

/-- For `q ≥ 2` and `0 < ε < 1`, arbitrarily large natural numbers `m` satisfy `ε < q^(m - 1 - m
/ 2) / 4`, with natural-number arithmetic in the exponent [GeraciLidar2008]. -/
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
