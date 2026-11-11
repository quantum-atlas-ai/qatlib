/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WeightEnum07.OrbitSieve.CosetSieve
import Mathlib.Data.Nat.Log

/-!
# Orbit counts and sieve cost identities

Orbit cardinalities are bounded by the order of the acting unit, giving upper and lower
estimates for the number of leaders. The cost expressions `sieveMarkSteps` and `sieveArrayTests`
count orbit entries and array tests, and evaluate to `N` and `2 * N`, respectively.

This development forms part of the formalization of [GeraciVanBussel2007].

## Main statements

* `leaders_card_bounds`: A positive exponent `k` with `u ^ k = 1` bounds the number of leaders
  between `N / k` and `N`.
* `sieve_cost_linear`: The sieve cost expressions are `N` marking steps and `2 * N` array tests,
  with at most `N` leaders.

## References

* [Geraci and Van Bussel, 2007][GeraciVanBussel2007]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.WeightEnum07.OrbitSieve

variable {N : ℕ} [NeZero N]

/-- The cardinality of a multiplication orbit is at most the order of `u`. -/
theorem orbitFinset_card_le_orderOf (u : (ZMod N)ˣ) (a : ZMod N) :
    (orbitFinset u a).card ≤ orderOf u := by
  unfold orbitFinset
  calc ((Finset.range (orderOf u)).image
          (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N) * a)).card
      ≤ (Finset.range (orderOf u)).card := Finset.card_image_le
    _ = orderOf u := Finset.card_range _

/-- If positive `k` satisfies `u ^ k = 1`, every multiplication orbit has cardinality at most
`k`. See [GeraciVanBussel2007]. -/
theorem orbitFinset_card_le_of_pow_eq_one {u : (ZMod N)ˣ} {k : ℕ} (hk : u ^ k = 1)
    (hkpos : 0 < k) (a : ZMod N) :
    (orbitFinset u a).card ≤ k := by
  have hdvd : orderOf u ∣ k := orderOf_dvd_of_pow_eq_one hk
  exact le_trans (orbitFinset_card_le_orderOf u a) (Nat.le_of_dvd hkpos hdvd)

/-- The number of orbit leaders is at most `N`. -/
theorem leaders_card_le (u : (ZMod N)ˣ) : (leaders u).card ≤ N := by
  classical
  have hsum := sum_orbit_card_eq u
  have h1 : (leaders u).card ≤ ∑ l ∈ leaders u, (orbitFinset u l).card := by
    calc (leaders u).card = ∑ _l ∈ leaders u, 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ l ∈ leaders u, (orbitFinset u l).card :=
          Finset.sum_le_sum (fun l _ => Nat.succ_le_of_lt (orbitFinset_card_pos u l))
  omega

/-- If positive `k` satisfies `u ^ k = 1`, the number of leaders is at least the natural
quotient `N / k`. -/
theorem div_le_leaders_card {u : (ZMod N)ˣ} {k : ℕ} (hk : u ^ k = 1) (hkpos : 0 < k) :
    N / k ≤ (leaders u).card := by
  classical
  have hsum := sum_orbit_card_eq u
  have hbound : ∑ l ∈ leaders u, (orbitFinset u l).card ≤ (leaders u).card * k := by
    calc ∑ l ∈ leaders u, (orbitFinset u l).card ≤ ∑ _l ∈ leaders u, k :=
          Finset.sum_le_sum (fun l _ => orbitFinset_card_le_of_pow_eq_one hk hkpos l)
      _ = (leaders u).card * k := by rw [Finset.sum_const, smul_eq_mul]
  have hN : N ≤ (leaders u).card * k := by omega
  calc N / k ≤ ((leaders u).card * k) / k := Nat.div_le_div_right hN
    _ = (leaders u).card := Nat.mul_div_cancel _ hkpos

/-- A positive exponent `k` with `u ^ k = 1` bounds the number of leaders between `N / k` and
`N`. See [GeraciVanBussel2007]. -/
theorem leaders_card_bounds {u : (ZMod N)ˣ} {k : ℕ} (hk : u ^ k = 1) (hkpos : 0 < k) :
    N / k ≤ (leaders u).card ∧ (leaders u).card ≤ N :=
  ⟨div_le_leaders_card hk hkpos, leaders_card_le u⟩

/-- The sum of the cardinalities of all leader orbits, used as the marking-step count. -/
noncomputable def sieveMarkSteps (u : (ZMod N)ˣ) : ℕ :=
  ∑ l ∈ leaders u, (orbitFinset u l).card

/-- The cost expression `N` plus the sum of the cardinalities of all leader orbits. -/
noncomputable def sieveArrayTests (u : (ZMod N)ˣ) : ℕ :=
  N + ∑ l ∈ leaders u, (orbitFinset u l).card

/-- The marking-step count equals `N`. -/
theorem sieveMarkSteps_eq (u : (ZMod N)ˣ) : sieveMarkSteps u = N :=
  sum_orbit_card_eq u

/-- The array-test count equals `2 * N`. -/
theorem sieveArrayTests_eq (u : (ZMod N)ˣ) : sieveArrayTests u = 2 * N := by
  unfold sieveArrayTests
  change N + sieveMarkSteps u = 2 * N
  rw [sieveMarkSteps_eq]
  ring

/-- The sieve has at most `N` leaders. -/
theorem sieveLeaders_le (u : (ZMod N)ˣ) : (leaders u).card ≤ N :=
  leaders_card_le u

/-- The sieve cost expressions are `N` marking steps and `2 * N` array tests, with at most `N`
leaders. See [GeraciVanBussel2007]. -/
theorem sieve_cost_linear (u : (ZMod N)ˣ) :
    sieveMarkSteps u = N ∧ sieveArrayTests u = 2 * N ∧ (leaders u).card ≤ N :=
  ⟨sieveMarkSteps_eq u, sieveArrayTests_eq u, sieveLeaders_le u⟩

end Qatlib.Papers.WeightEnum07.OrbitSieve
