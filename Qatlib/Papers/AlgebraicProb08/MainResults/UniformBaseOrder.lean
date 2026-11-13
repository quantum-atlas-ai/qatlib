/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.RandomBaseFactor
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.PrimeFin

/-!
# Probability of a good factoring base

Defines the event `algGoodBase` and its probability under the uniform distribution on units
modulo `N`. For an odd modulus with at least two distinct prime factors, this event agrees with
the checked factoring predicate and has probability at least `1 - 2^{-(k - 1)}`, hence at least
one half, where `k` counts distinct prime factors. See [ChildsVanDam2010].

## Main statements

* `alg08_good_base_event_iff_checked_program`: agreement with the checked good-base predicate.
* `alg08_lemma2_refined`: the bound in terms of the number of distinct prime factors.
* `alg08_lemma2_probability`: the uniform lower bound of one half.

## References

* [Childs and van Dam, 2010][ChildsVanDam2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.AlgebraicProb08.MainResults

open Qatlib
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open scoped Classical

/-- A unit is a good factoring base when its order is even and its half-order power is not −1
modulo `N`. -/
noncomputable def algGoodBase (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : Prop :=
  Even (orderOf a) ∧ ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1

/-- The proportion of units modulo `N` satisfying `algGoodBase`. -/
noncomputable def algGoodBaseProbability (N : ℕ) [NeZero N] : ℝ :=
  ((Finset.univ.filter (fun a : (ZMod N)ˣ => algGoodBase N a)).card : ℝ) /
    (Fintype.card (ZMod N)ˣ : ℝ)

/-- A natural number with at least two distinct prime factors is greater than one. -/
theorem alg08_one_lt_of_primeFactors_card (N : ℕ) (hk : 2 ≤ N.primeFactors.card) :
    1 < N := by
  have hne : N.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  exact Nat.nonempty_primeFactors.mp hne

/-- For odd `N > 1`, `algGoodBase N a` is equivalent to the checked predicate `randomBaseGood N
a`. -/
theorem alg08_good_base_event_iff_checked_program (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hN : 1 < N) (hodd : Odd N) :
    algGoodBase N a ↔ randomBaseGood N a :=
  (random_base_exact_order_factor_characterization N a hN hodd).symm

/-- For odd `N` with `k ≥ 2` distinct prime factors, the good-base probability is at least `1 -
2^{-(k - 1)}` [Childs and van Dam, Lemma 2][ChildsVanDam2010]. -/
theorem alg08_lemma2_refined (N : ℕ) [NeZero N] (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ algGoodBaseProbability N := by
  have hN : 1 < N := alg08_one_lt_of_primeFactors_card N hk
  have hfilter : (Finset.univ.filter (fun a : (ZMod N)ˣ => algGoodBase N a)) =
      Finset.univ.filter (fun a : (ZMod N)ˣ => randomBaseGood N a) := by
    refine Finset.filter_congr ?_
    intro a _
    exact alg08_good_base_event_iff_checked_program N a hN hodd
  rw [algGoodBaseProbability, hfilter, div_eq_inv_mul]
  exact random_base_crt_success_bound N hN hodd hk

/-- For odd `N` with at least two distinct prime factors, a uniform unit is a good factoring
base with probability at least one half [Childs and van Dam, Lemma 2][ChildsVanDam2010]. -/
theorem alg08_lemma2_probability (N : ℕ) [NeZero N] (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    (1 / 2 : ℝ) ≤ algGoodBaseProbability N := by
  have hbound := alg08_lemma2_refined N hodd hk
  have hcard : 1 ≤ N.primeFactors.card := by omega
  have hsub : (1 : ℤ) ≤ ((N.primeFactors.card - 1 : ℕ) : ℤ) := by
    have h : 1 ≤ N.primeFactors.card - 1 := by omega
    exact_mod_cast h
  have hle : -(N.primeFactors.card - 1 : ℤ) ≤ -(1 : ℤ) := by omega
  have hpow : (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ (2 : ℝ) ^ (-(1 : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) hle
  have hone : (2 : ℝ) ^ (-(1 : ℤ)) = 1 / 2 := by norm_num
  have hx : (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ 1 / 2 := hpow.trans hone.le
  linarith

end Qatlib.Papers.AlgebraicProb08.MainResults
