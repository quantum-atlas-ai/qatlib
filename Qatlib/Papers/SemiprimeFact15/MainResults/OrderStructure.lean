/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiprimeFact15.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SemiprimeFact15 — multiplicative order of `2` modulo a safe semiprime

This file formalizes **Lemma 1(1)** of Grosshans--Lawson--Morain--Smith,
*Factoring Safe Semiprimes with a Single Quantum Query*, fixed version
arXiv:1511.04385v3 (2 Mar 2017), §III.C, Lemma 1, p.5:

> Let `N = p₁p₂ = (2q₁+1)(2q₂+1)` be a safe semiprime with `q₁ ≠ q₂`, `q₁,q₂ > 2`.
> Then `ord_N(2)` is either `q₁q₂` or `2q₁q₂`.

The paper route is followed exactly:

1. Chinese remainder theorem: `ZMod (p₁p₂) ≃+* ZMod p₁ × ZMod p₂`, and
   multiplicative order is preserved (`orderOf_injective`), giving
   `ord_N(2) = lcm (ord_{p₁}(2)) (ord_{p₂}(2))` (`Prod.orderOf`).
2. For a safe prime `p = 2q+1`, `ord_p(2) ∣ p - 1 = 2q`
   (`ZMod.orderOf_dvd_card_sub_one`), and `ord_p(2) ∉ {1, 2}`
   (`2 ≠ 1` and `2² = 4 ≠ 1` since `p > 3`), hence `ord_p(2) ∈ {q, 2q}`.
3. Taking the `lcm` of the two possibilities gives `q₁q₂` or `2q₁q₂`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SemiprimeFact15.MainResults

/-! ## Step 2: the order modulo each safe prime -/

/-- **Order modulo a safe prime.**  For a safe prime `p = 2q+1` with `q` prime
and `q > 2`, the multiplicative order of `2` modulo `p` is `q` or `2q`
(arXiv:1511.04385v3, §III.C, proof of Lemma 1). -/
theorem orderOf_two_zmod_of_safe_prime {p q : ℕ} (hp : p.Prime) (hpq : p = 2 * q + 1)
    (hq : q.Prime) (hq2 : 2 < q) :
    orderOf (2 : ZMod p) = q ∨ orderOf (2 : ZMod p) = 2 * q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by rw [hpq, two_mul]; omega
  have hne0 : (2 : ZMod p) ≠ 0 := by
    show ((2 : ℕ) : ZMod p) ≠ 0
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hd := (Nat.dvd_prime Nat.prime_two).mp h
    omega
  have hdvd : orderOf (2 : ZMod p) ∣ 2 * q := by
    have h := ZMod.orderOf_dvd_card_sub_one hne0
    have hpe : p - 1 = 2 * q := by omega
    rwa [hpe] at h
  have hne1 : orderOf (2 : ZMod p) ≠ 1 := by
    intro h
    have h21 : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp h
    have hone : ((1 : ℕ) : ZMod p) = 0 := by
      have hsub : (2 : ZMod p) - 1 = 0 := sub_eq_zero.mpr h21
      have h2 : (2 : ZMod p) - 1 = ((1 : ℕ) : ZMod p) := by push_cast; ring
      rw [h2] at hsub
      exact hsub
    rw [ZMod.natCast_eq_zero_iff] at hone
    have hp1 : p = 1 := Nat.dvd_one.mp hone
    omega
  have hne2 : orderOf (2 : ZMod p) ≠ 2 := by
    intro h
    have hpow : (2 : ZMod p) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    have h4 : ((4 : ℕ) : ZMod p) = 1 := by
      have hsq : (2 : ZMod p) ^ 2 = ((4 : ℕ) : ZMod p) := by push_cast; ring
      rw [← hsq]; exact hpow
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      have hsub : ((4 : ℕ) : ZMod p) - 1 = 0 := sub_eq_zero.mpr h4
      have h43 : ((4 : ℕ) : ZMod p) - 1 = ((3 : ℕ) : ZMod p) := by push_cast; ring
      rw [h43] at hsub
      exact hsub
    rw [ZMod.natCast_eq_zero_iff] at h3
    have hple3 := (Nat.dvd_prime Nat.prime_three).mp h3
    omega
  rcases dvd_two_mul_prime hq hdvd with h | h | h | h
  · exact absurd h hne1
  · exact absurd h hne2
  · left; exact h
  · right; exact h

/-! ## Step 3: the `lcm` of the two orders -/

/-- Taking the `lcm` of `q₁`-or-`2q₁` with `q₂`-or-`2q₂` for distinct odd primes
`q₁ ≠ q₂` gives `q₁q₂` or `2q₁q₂` (arXiv:1511.04385v3, §III.C, proof of Lemma 1). -/
theorem lcm_of_prime_orders (cs : SafeSemiprime) {a b : ℕ}
    (ha : a = cs.q1 ∨ a = 2 * cs.q1) (hb : b = cs.q2 ∨ b = 2 * cs.q2) :
    Nat.lcm a b = cs.q1 * cs.q2 ∨ Nat.lcm a b = 2 * cs.q1 * cs.q2 := by
  have hcqq : Nat.Coprime cs.q1 cs.q2 :=
    (Nat.coprime_primes cs.q1_prime cs.q2_prime).mpr cs.q1_ne_q2
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left; exact hcqq.lcm_eq_mul
  · right
    have hc : Nat.Coprime cs.q1 (2 * cs.q2) :=
      Nat.Coprime.mul_right (Nat.coprime_two_right.mpr cs.q1_odd) hcqq
    rw [hc.lcm_eq_mul]; ring
  · right
    have hc : Nat.Coprime (2 * cs.q1) cs.q2 :=
      Nat.Coprime.mul_left (Nat.coprime_two_left.mpr cs.q2_odd) hcqq
    rw [hc.lcm_eq_mul]
  · right
    rw [Nat.lcm_mul_left, hcqq.lcm_eq_mul]; ring

/-! ## Step 1 + 3: the order modulo `N` -/

/-- **Lemma 1(1)** (arXiv:1511.04385v3, §III.C, Lemma 1, p.5): for a safe
semiprime `N = p₁p₂ = (2q₁+1)(2q₂+1)` with `q₁ ≠ q₂` and `q₁,q₂ > 2`, the
multiplicative order of `2` modulo `N` is `q₁q₂` or `2q₁q₂`. -/
theorem orderOf_two_N (cs : SafeSemiprime) :
    orderOf (2 : ZMod cs.N) = cs.q1 * cs.q2 ∨
      orderOf (2 : ZMod cs.N) = 2 * cs.q1 * cs.q2 := by
  have hcrt : orderOf (2 : ZMod (cs.p1 * cs.p2)) =
      Nat.lcm (orderOf (2 : ZMod cs.p1)) (orderOf (2 : ZMod cs.p2)) := by
    have e : ZMod (cs.p1 * cs.p2) ≃+* ZMod cs.p1 × ZMod cs.p2 :=
      ZMod.chineseRemainder cs.coprime_p1_p2
    let f : ZMod (cs.p1 * cs.p2) →* ZMod cs.p1 × ZMod cs.p2 := e.toMonoidHom
    have hfinj : Function.Injective f := e.injective
    have h := orderOf_injective f hfinj (2 : ZMod (cs.p1 * cs.p2))
    rw [← h]
    have h2 : f (2 : ZMod (cs.p1 * cs.p2)) = (2, 2) := by
      change e (((2 : ℕ) : ZMod (cs.p1 * cs.p2))) =
        (((2 : ℕ) : ZMod cs.p1), ((2 : ℕ) : ZMod cs.p2))
      rw [map_natCast]
      rfl
    rw [h2, Prod.orderOf]
  rw [cs.N_eq, hcrt]
  exact lcm_of_prime_orders cs
    (orderOf_two_zmod_of_safe_prime cs.p1_prime cs.p1_eq cs.q1_prime cs.q1_gt_two)
    (orderOf_two_zmod_of_safe_prime cs.p2_prime cs.p2_eq cs.q2_prime cs.q2_gt_two)

end Qatlib.Papers.SemiprimeFact15.MainResults
