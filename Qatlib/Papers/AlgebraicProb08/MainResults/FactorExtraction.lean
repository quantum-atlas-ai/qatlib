/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AlgebraicProb08.MainResults.UniformBaseOrder
import Mathlib.Data.Nat.Prime.Basic

/-!
# Extracting factors from an even order

Proves that an even-order unit whose half-order power is not −1 yields a nontrivial divisor of
an odd modulus through a greatest common divisor. The checked routine `orderFactor` succeeds on
such bases, and for an odd modulus with at least two distinct prime factors its success
probability under a uniform unit is at least one half. See [ChildsVanDam2010].

## Main statements

* `alg08_gcd_nontrivial`: the half-order predecessor yields a proper nontrivial divisor.
* `alg08_half_order_step_succeeds`: the probability bound and correctness of every returned
  factor.

## References

* [Childs and van Dam, 2010][ChildsVanDam2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.AlgebraicProb08.MainResults

open Qatlib
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open scoped Classical

/-- For a unit of even order, the square of its half-order power is one. -/
theorem alg08_half_pow_sq (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (he : Even (orderOf a)) : (a ^ (orderOf a / 2)) ^ 2 = 1 := by
  rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp he), pow_orderOf_eq_one]

/-- For a unit of even order, its half-order power is not one. -/
theorem alg08_half_pow_ne_one (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (he : Even (orderOf a)) : a ^ (orderOf a / 2) ≠ 1 := by
  apply pow_ne_one_of_lt_orderOf
  · have hdiv := Nat.div_mul_cancel (even_iff_two_dvd.mp he)
    have hr := orderOf_pos a
    omega
  · exact Nat.div_lt_self (orderOf_pos a) (by omega)

/-- For odd `N > 1` and a unit `x` with `x^2 = 1`, the natural predecessor of its representative
is coprime to `N` exactly when `x = -1` modulo `N`. -/
theorem alg08_root_predecessor_coprime_iff (N : ℕ) [NeZero N]
    (hN : 1 < N) (hodd : Odd N) (x : (ZMod N)ˣ) (hx : x ^ 2 = 1) :
    (x.val.val - 1).Coprime N ↔ (x : ZMod N) = -1 := by
  letI : Fact (1 < N) := ⟨hN⟩
  have ht : 1 ≤ x.val.val := by
    have h : x.val.val ≠ 0 := by rw [ZMod.val_ne_zero]; exact x.isUnit.ne_zero
    omega
  have hcast : ((x.val.val - 1 : ℕ) : ZMod N) = (x : ZMod N) - 1 := by
    rw [Nat.cast_sub ht, ZMod.natCast_zmod_val, Nat.cast_one]
  rw [← ZMod.isUnit_iff_coprime, hcast]
  constructor
  · intro hu
    have hsq : (x : ZMod N) ^ 2 = 1 := congrArg Units.val hx
    have hp : ((x : ZMod N) - 1) * ((x : ZMod N) + 1) = 0 := by
      calc
        _ = (x : ZMod N) ^ 2 - 1 := by ring
        _ = 0 := by rw [hsq]; ring
    have hz := hu.mul_right_eq_zero.mp hp
    exact add_eq_zero_iff_eq_neg.mp hz
  · intro hxneg
    rw [hxneg]
    have hu : IsUnit (2 : ZMod N) :=
      (ZMod.isUnit_iff_coprime 2 N).mpr hodd.coprime_two_left
    convert! hu.neg using 1
    ring

/-- For odd `N > 1`, an even-order unit whose half-order power is not −1 yields a greatest
common divisor with `N` that is a proper nontrivial divisor [ChildsVanDam2010]. -/
theorem alg08_gcd_nontrivial (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hN : 1 < N) (hodd : Odd N) (he : Even (orderOf a))
    (hneg : ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1) :
    1 < Nat.gcd N (((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val - 1) ∧
      Nat.gcd N (((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val - 1) < N ∧
      Nat.gcd N (((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val - 1) ∣ N := by
  letI : Fact (1 < N) := ⟨hN⟩
  let x : (ZMod N)ˣ := a ^ (orderOf a / 2)
  set t := x.val.val with ht_def
  have ht : 1 ≤ t := by
    have h : x.val.val ≠ 0 := by rw [ZMod.val_ne_zero]; exact x.isUnit.ne_zero
    omega
  have hcast : ((t - 1 : ℕ) : ZMod N) = (x : ZMod N) - 1 := by
    rw [Nat.cast_sub ht, ZMod.natCast_zmod_val, Nat.cast_one]
  have hsq : x ^ 2 = 1 := by
    simpa [x] using! alg08_half_pow_sq N a he
  have hxne : x ≠ 1 := by
    simpa [x] using! alg08_half_pow_ne_one N a he
  have hcop := alg08_root_predecessor_coprime_iff N hN hodd x hsq
  have hneg' : (x : ZMod N) ≠ -1 := by simpa [x] using! hneg
  have hnc : ¬ (t - 1).Coprime N := by
    rw [hcop]
    exact hneg'
  refine ⟨?_, ?_, Nat.gcd_dvd_left N (t - 1)⟩
  · have hne1 : Nat.gcd N (t - 1) ≠ 1 := by
      intro h1
      exact hnc (by rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]; exact h1)
    have hpos : 0 < Nat.gcd N (t - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
    omega
  · have hle := Nat.gcd_le_left (t - 1) (show 0 < N by omega)
    have hne : Nat.gcd N (t - 1) ≠ N := by
      intro heq
      have hdvd : N ∣ t - 1 := by
        rw [← heq]
        exact Nat.gcd_dvd_right N (t - 1)
      have hz : ((t - 1 : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [hcast, sub_eq_zero] at hz
      exact hxne (Units.ext hz)
    omega

/-- For odd `N > 1`, a good base makes `orderFactor` return a proper nontrivial divisor when
supplied with the exact order. -/
theorem alg08_factor_of_good_base (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hN : 1 < N) (hodd : Odd N) (hgood : algGoodBase N a) :
    ∃ d, orderFactor N a (orderOf a) = some d ∧ 1 < d ∧ d < N ∧ d ∣ N := by
  have hgood' : (orderFactor N a (orderOf a)).isSome := by
    have h := (alg08_good_base_event_iff_checked_program N a hN hodd).mp hgood
    simpa [randomBaseGood] using! h
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hgood'
  exact ⟨d, hd, orderFactor_sound N a (orderOf a) d hd⟩

/-- For odd `N` with at least two distinct prime factors, the fraction of units for which
exact-order factor extraction returns a value is at least one half. -/
theorem alg08_factor_success_probability (N : ℕ) [NeZero N] (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    (1 / 2 : ℝ) ≤
      ((Finset.univ.filter (fun a : (ZMod N)ˣ =>
        (orderFactor N a (orderOf a)).isSome)).card : ℝ) /
        (Fintype.card (ZMod N)ˣ : ℝ) := by
  have hN : 1 < N := alg08_one_lt_of_primeFactors_card N hk
  have hfilter : (Finset.univ.filter (fun a : (ZMod N)ˣ =>
      (orderFactor N a (orderOf a)).isSome)) =
      Finset.univ.filter (fun a : (ZMod N)ˣ => algGoodBase N a) := by
    refine Finset.filter_congr ?_
    intro a _
    exact (alg08_good_base_event_iff_checked_program N a hN hodd).symm
  rw [hfilter, ← algGoodBaseProbability, div_eq_inv_mul]
  simpa using! alg08_lemma2_probability N hodd hk

/-- For odd `N` with at least two distinct prime factors, exact-order factor extraction succeeds
on at least half the units, and every returned value is a proper nontrivial divisor [Childs
and van Dam, Lemma 2][ChildsVanDam2010]. -/
theorem alg08_half_order_step_succeeds (N : ℕ) [NeZero N] (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    (1 / 2 : ℝ) ≤
        ((Finset.univ.filter (fun a : (ZMod N)ˣ =>
          (orderFactor N a (orderOf a)).isSome)).card : ℝ) /
          (Fintype.card (ZMod N)ˣ : ℝ) ∧
      ∀ (a : (ZMod N)ˣ) (d : ℕ), orderFactor N a (orderOf a) = some d →
        1 < d ∧ d < N ∧ d ∣ N :=
  ⟨alg08_factor_success_probability N hodd hk, fun a d hd => orderFactor_sound N a _ d hd⟩

end Qatlib.Papers.AlgebraicProb08.MainResults
