/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PrimalityCerts.LucasTests.LucasWitnesses
import Qatlib.Papers.QPrimality95.MainResults.CostDefs

/-!
# Pocklington–Lehmer criteria and primality-cost assembly

This module proves primality criteria in `ZMod N` using witnesses for the prime divisors of `N -
1`, as presented in [ChauLo1995]. It includes a common-witness form, a separate-witness form,
and versions whose divisor coverage is supplied by a prime-power factorization.

The result `total_cost_bound_of_subroutine_bounds` combines assumed factorization and
verification cost bounds into a positive constant multiple of `mainCost`.

## Main statements

* `pocklington_lehmer_factorization_sound`: A prime-power factorization of `N - 1`, together
  with separate residue witnesses for each factor, proves that `N` is prime. This is the
  separate-witness criterion of [Chau and Lo, Theorem 2][ChauLo1995].
* `pocklington_lehmer_product_sound`: A prime-power factorization of `N - 1` and one residue
  satisfying all the stated power tests prove that `N` is prime. This is the common-witness
  criterion of [Chau and Lo, Theorem 1][ChauLo1995].
* `total_cost_bound_of_subroutine_bounds`: If factorization and verification costs are bounded
  by the stated multiples of `mainCost` for `N ≥ 3`, and the sum of the constants is positive,
  their combined cost has a positive constant bound of the same form.

## References

* [Chau and Lo, 1995][ChauLo1995]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPrimality95.MainResults

open scoped BigOperators

/-- If `S` covers every prime divisor of `N - 1` and one residue satisfies the full-power
equality and every specified reduced-power inequality, then `N` is prime. -/
theorem pocklington_lehmer_sound
    (N : ℕ) (a : ZMod N) (S : Finset ℕ)
    (_hSprime : ∀ p ∈ S, p.Prime)
    (hScover : ∀ q : ℕ, q.Prime → q ∣ N - 1 → q ∈ S)
    (ha : a ^ (N - 1) = 1)
    (hd : ∀ p ∈ S, a ^ ((N - 1) / p) ≠ 1) :
    N.Prime :=
  lucas_primality N a ha (fun q hq hqd => hd q (hScover q hq hqd))

/-- If `S` covers every prime divisor of `N - 1` and each member has a residue satisfying its
full-power equality and reduced-power inequality, then `N` is prime. -/
theorem pocklington_lehmer_separate_sound (N : ℕ) (S : Finset ℕ)
    (hcover : ∀ q : ℕ, q.Prime → q ∣ N - 1 → q ∈ S)
    (hw : ∀ q ∈ S, ∃ a : ZMod N,
      a ^ (N - 1) = 1 ∧ a ^ ((N - 1) / q) ≠ 1) : N.Prime :=
  Qatlib.Foundations.PrimalityCerts.LucasTests.separateLucas N
    (fun q hq hqd => hw q (hcover q hq hqd))

/-- A prime-power factorization of `N - 1`, together with separate residue witnesses for each
factor, proves that `N` is prime. This is the separate-witness criterion of [Chau and Lo,
Theorem 2][ChauLo1995]. -/
theorem pocklington_lehmer_factorization_sound (N : ℕ) (S : Finset ℕ) (β : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hfactor : N - 1 = ∏ p ∈ S, p ^ β p)
    (hw : ∀ p ∈ S, ∃ a : ZMod N,
      a ^ (N - 1) = 1 ∧ a ^ ((N - 1) / p) ≠ 1) : N.Prime :=
  Qatlib.Foundations.PrimalityCerts.LucasTests.separateLucasProduct N S β hprime hfactor hw

/-- A prime-power factorization of `N - 1` and one residue satisfying all the stated power tests
prove that `N` is prime. This is the common-witness criterion of [Chau and Lo, Theorem
1][ChauLo1995]. -/
theorem pocklington_lehmer_product_sound (N : ℕ) (S : Finset ℕ) (β : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hfactor : N - 1 = ∏ p ∈ S, p ^ β p)
    (a : ZMod N) (ha : a ^ (N - 1) = 1)
    (hd : ∀ p ∈ S, a ^ ((N - 1) / p) ≠ 1) : N.Prime :=
  pocklington_lehmer_factorization_sound N S β hprime hfactor
    (fun p hp => ⟨a, ha, hd p hp⟩)

/-- If factorization and verification costs are bounded by the stated multiples of `mainCost`
for `N ≥ 3`, and the sum of the constants is positive, their combined cost has a positive
constant bound of the same form. -/
theorem total_cost_bound_of_subroutine_bounds
    (factCost verifyCost : ℕ → ℝ) (Cf Cv : ℝ)
    (hCpos : 0 < Cf + Cv)
    (hfact : ∀ N : ℕ, 3 ≤ N → factCost N ≤ Cf * mainCost N)
    (hverify : ∀ N : ℕ, 3 ≤ N → verifyCost N ≤ Cv * mainCost N) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      factCost N + verifyCost N ≤ C * mainCost N := by
  refine ⟨Cf + Cv, hCpos, ?_⟩
  intro N hN
  calc
    factCost N + verifyCost N ≤ Cf * mainCost N + Cv * mainCost N :=
      add_le_add (hfact N hN) (hverify N hN)
    _ = (Cf + Cv) * mainCost N := by ring

end Qatlib.Papers.QPrimality95.MainResults
