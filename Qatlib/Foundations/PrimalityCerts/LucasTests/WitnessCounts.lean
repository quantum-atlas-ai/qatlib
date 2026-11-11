/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PrimalityCerts.PrimePowerOrder.OrderCounts
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Defs

/-!
# Counting Lucas witnesses modulo a prime

For prime `N`, this module counts solutions of `a ^ d = 1` among units and among all residues
modulo `N`. The resulting gcd formula bounds below the fraction of residues satisfying a
reduced-power inequality, supplying a sampling estimate for primality certificates [ChauLo1995].

## Main statements

* `units_pow_eq_one_card`: The unit solution count is gcd(N - 1, d).
* `zmod_pow_eq_one_card`: The same count holds for all residues when d is positive.
* `witness_fraction_ge_half`: At least half of all residues satisfy the reduced-power
  inequality.

## References

* [Chau and Lo, 1995][ChauLo1995]
-/

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Foundations.PrimalityCerts.LucasTests

open Qatlib.Foundations.PrimalityCerts.PrimePowerOrder

/-- For prime `N` and positive `d`, exactly `Nat.gcd (N - 1) d` units modulo `N` satisfy `u ^ d
= 1`. -/
theorem units_pow_eq_one_card (N d : ℕ) [NeZero N] (hN : N.Prime) (_hd : 0 < d) :
    (Finset.univ.filter (fun u : (ZMod N)ˣ => u ^ d = 1)).card
      = Nat.gcd (N - 1) d := by
  classical
  haveI hcyc : IsCyclic (ZMod N)ˣ := ZMod.isCyclic_units_prime hN
  have hcard : Fintype.card (ZMod N)ˣ = N - 1 :=
    (Nat.prime_iff_card_units N).mp hN
  calc (Finset.univ.filter (fun u : (ZMod N)ˣ => u ^ d = 1)).card
      = (Finset.univ.filter (fun u : (ZMod N)ˣ => orderOf u ∣ d)).card := by
        congr 1
        apply Finset.filter_congr
        intro u _
        exact orderOf_dvd_iff_pow_eq_one.symm
    _ = Nat.gcd (Fintype.card (ZMod N)ˣ) d := filter_card_orderOf_dvd _ d
    _ = Nat.gcd (N - 1) d := by rw [hcard]

/-- For prime `N` and positive `d`, exactly `Nat.gcd (N - 1) d` residues modulo `N` satisfy `a ^
d = 1`. -/
theorem zmod_pow_eq_one_card (N d : ℕ) [NeZero N] (hN : N.Prime) (hd : 0 < d) :
    (Finset.univ.filter (fun a : ZMod N => a ^ d = 1)).card
      = Nat.gcd (N - 1) d := by
  classical
  haveI : Fact N.Prime := ⟨hN⟩
  have hset : (Finset.univ.filter (fun a : ZMod N => a ^ d = 1))
      = (Finset.univ.filter (fun u : (ZMod N)ˣ => u ^ d = 1)).image Units.val := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ha
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, zero_pow hd.ne'] at ha
        exact zero_ne_one ha
      have hunit : IsUnit a := isUnit_iff_ne_zero.mpr ha0
      obtain ⟨u, hu⟩ := hunit
      refine ⟨u, ?_, hu⟩
      have hpow : ((u ^ d : (ZMod N)ˣ) : ZMod N) = 1 := by
        rw [Units.val_pow_eq_pow_val, hu]
        exact ha
      exact Units.ext hpow
    · rintro ⟨u, hu, rfl⟩
      simpa using congrArg (Units.val) hu
  rw [hset, Finset.card_image_of_injective _ Units.val_injective]
  exact units_pow_eq_one_card N d hN hd

/-- For a prime divisor `q` of `N - 1` with `N` prime, at least half of all residues modulo `N`
satisfy `a ^ ((N - 1) / q) ≠ 1`. See [ChauLo1995]. -/
theorem witness_fraction_ge_half (N q : ℕ) [NeZero N] (hN : N.Prime) (hq : q.Prime)
    (hqd : q ∣ N - 1) :
    (1 : ℚ) / 2 ≤
      ((Finset.univ.filter (fun a : ZMod N => a ^ ((N - 1) / q) ≠ 1)).card : ℚ)
        / (Fintype.card (ZMod N) : ℚ) := by
  classical
  have hN2 : 2 ≤ N := hN.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hN1pos : 0 < N - 1 := by omega
  have hqle : q ≤ N - 1 := Nat.le_of_dvd hN1pos hqd
  have hdpos : 0 < (N - 1) / q := Nat.div_pos hqle hq.pos
  have hdvd : (N - 1) / q ∣ N - 1 := Nat.div_dvd_of_dvd hqd

  have hbad : (Finset.univ.filter (fun a : ZMod N => a ^ ((N - 1) / q) = 1)).card
      = (N - 1) / q := by
    rw [zmod_pow_eq_one_card N ((N - 1) / q) hN hdpos]
    exact Nat.gcd_eq_right hdvd
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod N)))
    (p := fun a : ZMod N => a ^ ((N - 1) / q) = 1)
  have hgood : (Finset.univ.filter (fun a : ZMod N => a ^ ((N - 1) / q) ≠ 1)).card
      = N - (N - 1) / q := by
    have hcomp : (Finset.univ.filter (fun a : ZMod N => ¬ a ^ ((N - 1) / q) = 1)).card
        = N - (N - 1) / q := by
      have hcard : (Finset.univ : Finset (ZMod N)).card = N := by
        rw [Finset.card_univ, ZMod.card]
      omega
    simpa only [ne_eq] using hcomp
  have hcardN : Fintype.card (ZMod N) = N := ZMod.card N
  rw [hcardN, hgood]

  have h2d : 2 * ((N - 1) / q) ≤ N - 1 := by
    have h1 : q * ((N - 1) / q) ≤ N - 1 := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self (N - 1) q
    have h2 : 2 * ((N - 1) / q) ≤ q * ((N - 1) / q) :=
      Nat.mul_le_mul_right _ hq2
    exact h2.trans h1
  have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast (by omega : 0 < N)
  rw [le_div_iff₀ hNq]
  have hcast : (2 : ℚ) * (((N - 1) / q : ℕ) : ℚ) ≤ (N : ℚ) - 1 := by
    have hcastN : ((2 * ((N - 1) / q) : ℕ) : ℚ) ≤ ((N - 1 : ℕ) : ℚ) := by
      exact_mod_cast h2d
    have hN1 : ((N - 1 : ℕ) : ℚ) = (N : ℚ) - 1 := by
      have h1 : (1 : ℕ) ≤ N := hN.one_le
      rw [Nat.cast_sub h1]
      norm_num
    push_cast at hcastN ⊢
    linarith
  have hsub : ((N - (N - 1) / q : ℕ) : ℚ) = (N : ℚ) - (((N - 1) / q : ℕ) : ℚ) := by
    have hle : (N - 1) / q ≤ N := by omega
    rw [Nat.cast_sub hle]
  rw [hsub]
  nlinarith

end Qatlib.Foundations.PrimalityCerts.LucasTests
