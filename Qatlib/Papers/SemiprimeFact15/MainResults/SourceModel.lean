/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Parity

set_option backward.isDefEq.respectTransparency false

/-!
# SemiprimeFact15 — source model

Grosshans--Lawson--Morain--Smith, *Factoring Safe Semiprimes with a Single
Quantum Query*, fixed version arXiv:1511.04385v3 (2 Mar 2017), §III.A–§III.C.

This file fixes the paper's model objects:

* a safe semiprime `N = p₁p₂ = (2q₁+1)(2q₂+1)` (`SafeSemiprime`);
* the ideal (perfect) quantum order-finding output `d = r/gcd(t,r)` produced by
  the continued-fraction post-processing on the uniform phase `t/ord_N(2)`
  (`qofaOutput`, §III.B, and the frozen decoder
  `QuantumAlgorithm.Papers.ShorFactoring97.OrderRecovery.reduced_order_denominator_of_every_good_phase`);
* the even/odd unification `s = d` (resp. `2d`) of Algorithm 1 lines 4–5
  (`sComplement`);
* the two output sets of Lemma 1(2): the six useful values and the two bad
  values `{1,2}` (`usefulSet`, `badSet`).

This module only holds definitions and elementary divisor facts consumed by the
claim modules; the claim theorems live in `SourceOrderStructure`,
`SourceQofaOutput`, `SourceCoreObservation` and `SourceMainTheorem`.

Boundary: the quantum order-finding primitive itself (QOFA) is the paper's
granted primitive.  The model studies the actual arithmetic it reports
(`ord_N(2)` and `d = ord_N(2)/gcd(t, ord_N(2))`), not a gate-level circuit.

## Source notes

PDF: arXiv:1511.04385v3 (Dated March 3, 2017).  §II "Number theoretic tools",
§III.C "Factoring safe semiprimes with one call to QOFA", Lemma 1; Algorithm 1.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SemiprimeFact15.MainResults

/-- A **safe semiprime** `N = p₁ p₂ = (2q₁+1)(2q₂+1)` with `p₁, p₂` safe primes
whose Sophie-Germain halves `q₁, q₂ > 2` are prime and distinct
(arXiv:1511.04385v3, §III.C, Lemma 1 hypotheses). -/
structure SafeSemiprime where
  /-- the semiprime `N = p₁ p₂` -/
  N : ℕ
  /-- first safe prime -/
  p1 : ℕ
  /-- second safe prime -/
  p2 : ℕ
  /-- Sophie-Germain half of `p₁`, `p₁ = 2q₁+1` -/
  q1 : ℕ
  /-- Sophie-Germain half of `p₂`, `p₂ = 2q₂+1` -/
  q2 : ℕ
  p1_prime : p1.Prime
  p2_prime : p2.Prime
  q1_prime : q1.Prime
  q2_prime : q2.Prime
  p1_eq : p1 = 2 * q1 + 1
  p2_eq : p2 = 2 * q2 + 1
  /-- `q₁ ≠ q₂` (Lemma 1 hypothesis) -/
  q1_ne_q2 : q1 ≠ q2
  /-- `q₁ > 2` (Lemma 1 hypothesis) -/
  q1_gt_two : 2 < q1
  /-- `q₂ > 2` (Lemma 1 hypothesis) -/
  q2_gt_two : 2 < q2
  /-- `N` is the product of the two safe primes -/
  N_eq : N = p1 * p2

namespace SafeSemiprime

variable (cs : SafeSemiprime)

/-- `q₁` is odd: it is a prime `> 2`. -/
lemma q1_odd : Odd cs.q1 := by
  have h := cs.q1_gt_two
  exact cs.q1_prime.odd_of_ne_two (by omega)

/-- `q₂` is odd: it is a prime `> 2`. -/
lemma q2_odd : Odd cs.q2 := by
  have h := cs.q2_gt_two
  exact cs.q2_prime.odd_of_ne_two (by omega)

/-- `3 ≤ q₁` since `q₁ > 2`. -/
lemma q1_ge_three : 3 ≤ cs.q1 := by have h := cs.q1_gt_two; omega

/-- `3 ≤ q₂` since `q₂ > 2`. -/
lemma q2_ge_three : 3 ≤ cs.q2 := by have h := cs.q2_gt_two; omega

/-- `p₁ > 2`. -/
lemma p1_gt_two : 2 < cs.p1 := by
  have h := cs.q1_gt_two; rw [cs.p1_eq, two_mul]; omega

/-- `p₂ > 2`. -/
lemma p2_gt_two : 2 < cs.p2 := by
  have h := cs.q2_gt_two; rw [cs.p2_eq, two_mul]; omega

/-- `p₁ > 3` (in fact `p₁ ≥ 7`), as stated parenthetically in Lemma 1. -/
lemma p1_gt_three : 3 < cs.p1 := by
  have h := cs.q1_gt_two; rw [cs.p1_eq, two_mul]; omega

/-- `p₂ > 3` (in fact `p₂ ≥ 7`), as stated parenthetically in Lemma 1. -/
lemma p2_gt_three : 3 < cs.p2 := by
  have h := cs.q2_gt_two; rw [cs.p2_eq, two_mul]; omega

/-- `p₁` is odd. -/
lemma p1_odd : Odd cs.p1 := ⟨cs.q1, cs.p1_eq⟩

/-- `p₂` is odd. -/
lemma p2_odd : Odd cs.p2 := ⟨cs.q2, cs.p2_eq⟩

/-- `p₁ ≠ p₂`: distinct Sophie-Germain halves give distinct safe primes. -/
lemma p1_ne_p2 : cs.p1 ≠ cs.p2 := by
  intro h
  apply cs.q1_ne_q2
  rw [cs.p1_eq, cs.p2_eq] at h
  omega

/-- `p₁` and `p₂` are coprime (they are distinct primes). -/
lemma coprime_p1_p2 : Nat.Coprime cs.p1 cs.p2 :=
  (Nat.coprime_primes cs.p1_prime cs.p2_prime).mpr cs.p1_ne_p2

/-- `N` is odd: a product of two odd primes. -/
lemma N_odd : Odd cs.N := by
  rw [cs.N_eq]
  exact cs.p1_odd.mul cs.p2_odd

/-- `2` is coprime to `N`. -/
lemma two_coprime_N : Nat.Coprime 2 cs.N := by
  rw [Nat.coprime_two_left]
  exact cs.N_odd

/-- `N > 0`. -/
lemma N_pos : 0 < cs.N := by
  rw [cs.N_eq]
  exact Nat.mul_pos cs.p1_prime.pos cs.p2_prime.pos

/-- Euler's totient of a safe semiprime: `φ(N) = (p₁-1)(p₂-1) = 4q₁q₂`
(arXiv:1511.04385v3, §II Eq. (1) and §III.B). -/
lemma totient_N : cs.N.totient = 4 * cs.q1 * cs.q2 := by
  have h1 : cs.p1 - 1 = 2 * cs.q1 := by rw [cs.p1_eq]; omega
  have h2 : cs.p2 - 1 = 2 * cs.q2 := by rw [cs.p2_eq]; omega
  rw [cs.N_eq, Nat.totient_mul cs.coprime_p1_p2, Nat.totient_prime cs.p1_prime,
    Nat.totient_prime cs.p2_prime, h1, h2]
  ring

/-- The exact factor pair `(p₁, p₂)` is a nontrivial factorization of `N`. -/
lemma p1_mul_p2 : cs.p1 * cs.p2 = cs.N := cs.N_eq.symm

/-- Sum of the two safe primes: `p₁ + p₂ = N + 1 - 4q₁q₂`. -/
lemma p1_add_p2 : cs.p1 + cs.p2 = cs.N + 1 - 4 * cs.q1 * cs.q2 := by
  apply Nat.eq_sub_of_add_eq
  rw [cs.N_eq, cs.p1_eq, cs.p2_eq]
  ring

end SafeSemiprime

/-! ## The ideal QOFA output and Algorithm 1's even/odd unification -/

/-- The **ideal (perfectly implemented) quantum order-finding output**.  For a
true order `r` and the uniformly random continued-fraction numerator
`t ∈ {1,…,r}`, the post-processing returns `d = r / gcd(t,r)`
(arXiv:1511.04385v3, §III.B, "QOFA then uses a continued fraction expansion to
get `d = ord_N(a)/gcd(t, ord_N(a))`").  This is the value computed by the frozen
decoder `QuantumAlgorithm.Papers.ShorFactoring97.OrderRecovery.reduced_order_denominator_of_every_good_phase`. -/
def qofaOutput (r t : ℕ) : ℕ := r / Nat.gcd t r

/-- Algorithm 1, lines 4–5: unify the odd and even cases of the QOFA output `d`
by `s = d` when `d` is even and `s = 2d` when `d` is odd
(arXiv:1511.04385v3, Algorithm 1). -/
def sComplement (d : ℕ) : ℕ := if 2 ∣ d then d else 2 * d

/-- The six **useful** QOFA outputs of Lemma 1(2). -/
def usefulSet (q1 q2 : ℕ) : Finset ℕ :=
  {q1, q2, q1 * q2, 2 * q1, 2 * q2, 2 * q1 * q2}

/-- The two **bad** QOFA outputs `{1, 2}` of Lemma 1(2). -/
def badSet : Finset ℕ := {1, 2}

/-! ## Elementary divisor classifications -/

/-- **Divisors of `2q` for a prime `q`**: `d ∣ 2q` forces
`d ∈ {1,2,q,2q}`. -/
theorem dvd_two_mul_prime {d q : ℕ} (hq : q.Prime) (h : d ∣ 2 * q) :
    d = 1 ∨ d = 2 ∨ d = q ∨ d = 2 * q := by
  obtain ⟨k, hk⟩ := h
  have hq0 : 0 < q := hq.pos
  by_cases hqd : q ∣ d
  · obtain ⟨m, hm⟩ := hqd
    subst hm
    have h1 : q * 2 = q * (m * k) := by
      calc q * 2 = 2 * q := by ring
        _ = q * m * k := hk
        _ = q * (m * k) := by ring
    have hmk : 2 = m * k := Nat.mul_left_cancel hq0 h1
    have hm2 : m ∣ 2 := ⟨k, hmk⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h1 | h1
    · subst h1; right; right; left; ring
    · subst h1; right; right; right; ring
  · have hq_dk : q ∣ d * k := by
      rw [← hk]; exact ⟨2, by ring⟩
    rcases hq.dvd_mul.mp hq_dk with h | h
    · exact absurd h hqd
    · obtain ⟨m, hm⟩ := h
      subst hm
      have h1 : q * 2 = q * (d * m) := by
        calc q * 2 = 2 * q := by ring
          _ = d * (q * m) := hk
          _ = q * (d * m) := by ring
      have hdm : 2 = d * m := Nat.mul_left_cancel hq0 h1
      have hd2 : d ∣ 2 := ⟨m, hdm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h1
      · subst h1; left; rfl
      · subst h1; right; left; rfl

/-- **Divisors of `m·q` with `q` prime and coprime to `m`**: any divisor is
either a divisor of `m` or `q` times a divisor of `m`. -/
theorem dvd_mul_prime_of_coprime {d m q : ℕ} (hq : q.Prime) (hmq : Nat.Coprime m q)
    (h : d ∣ m * q) : d ∣ m ∨ ∃ e, e ∣ m ∧ d = q * e := by
  have hg : Nat.gcd d q = 1 ∨ Nat.gcd d q = q := by
    exact (Nat.dvd_prime hq).mp (Nat.gcd_dvd_right d q)
  rcases hg with hg | hg
  · left
    have hcd : Nat.Coprime d q := Nat.coprime_iff_gcd_eq_one.mpr hg
    exact (hcd.dvd_mul_right).mp h
  · right
    have hqd : q ∣ d := by rw [← hg]; exact Nat.gcd_dvd_left d q
    obtain ⟨e, he⟩ := hqd
    refine ⟨e, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := h
      have h1 : m * q = e * k * q := by rw [hk, he]; ring
      have hm : m = e * k := Nat.mul_right_cancel hq.pos h1
      exact ⟨k, hm⟩
    · exact he

/-- **Eight-way divisor classification of `2q₁q₂`** for a safe semiprime
(arXiv:1511.04385v3, Table I: the eight divisors of `λ(N) = 2q₁q₂`). -/
theorem dvd_two_mul_q1q2 (cs : SafeSemiprime) {d : ℕ}
    (hd : d ∣ 2 * cs.q1 * cs.q2) :
    d = 1 ∨ d = 2 ∨ d = cs.q1 ∨ d = cs.q2 ∨ d = cs.q1 * cs.q2 ∨
      d = 2 * cs.q1 ∨ d = 2 * cs.q2 ∨ d = 2 * cs.q1 * cs.q2 := by
  have hcop2 : Nat.Coprime (2 * cs.q1) cs.q2 :=
    Nat.Coprime.mul_left (Nat.coprime_two_left.mpr cs.q2_odd)
      ((Nat.coprime_primes cs.q1_prime cs.q2_prime).mpr cs.q1_ne_q2)
  have hcop1 : Nat.Coprime 2 cs.q1 := Nat.coprime_two_left.mpr cs.q1_odd
  rcases dvd_mul_prime_of_coprime cs.q2_prime hcop2 hd with hdq | ⟨e, he, hde⟩
  · rcases dvd_mul_prime_of_coprime cs.q1_prime hcop1 hdq with hd2 | ⟨e, he, hde⟩
    · rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
      · subst h; left; rfl
      · subst h; right; left; rfl
    · rcases (Nat.dvd_prime Nat.prime_two).mp he with h | h
      · subst h; right; right; left; rw [hde]; ring
      · subst h; right; right; right; right; right; left; rw [hde]; ring
  · rcases dvd_mul_prime_of_coprime cs.q1_prime hcop1 he with he2 | ⟨e', he', hee⟩
    · rcases (Nat.dvd_prime Nat.prime_two).mp he2 with h | h
      · subst h; right; right; right; left; rw [hde]; ring
      · subst h; right; right; right; right; right; right; left; rw [hde]; ring
    · rcases (Nat.dvd_prime Nat.prime_two).mp he' with h | h
      · subst h; right; right; right; right; left; rw [hde, hee]; ring
      · subst h; right; right; right; right; right; right; right; rw [hde, hee]; ring

/-- The QOFA output always divides the true order. -/
theorem qofaOutput_dvd (r t : ℕ) : qofaOutput r t ∣ r := by
  unfold qofaOutput
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right t r)

/-- `qofaOutput r t = 1` exactly when `r ∣ t`. -/
theorem qofaOutput_eq_one_iff {r : ℕ} (hr : 0 < r) (t : ℕ) :
    qofaOutput r t = 1 ↔ r ∣ t := by
  unfold qofaOutput
  constructor
  · intro h
    have hg : Nat.gcd t r ∣ r := Nat.gcd_dvd_right t r
    have hmul : Nat.gcd t r * (r / Nat.gcd t r) = r := Nat.mul_div_cancel' hg
    rw [h] at hmul
    simp only [mul_one] at hmul
    rw [← hmul]
    exact Nat.gcd_dvd_left t r
  · intro h
    have hg : Nat.gcd t r = r := Nat.gcd_eq_right h
    rw [hg]
    exact Nat.div_self hr

/-- `qofaOutput r t = 2` (for positive even `r`) exactly when
`gcd(t,r) = r/2`. -/
theorem qofaOutput_eq_two_iff {r : ℕ} (hr : 0 < r) (heven : 2 ∣ r) (t : ℕ) :
    qofaOutput r t = 2 ↔ Nat.gcd t r = r / 2 := by
  unfold qofaOutput
  obtain ⟨c, hc⟩ := heven
  have h2c : r / 2 = c := by omega
  constructor
  · intro h
    have hg : Nat.gcd t r ∣ r := Nat.gcd_dvd_right t r
    have hmul : Nat.gcd t r * (r / Nat.gcd t r) = r := Nat.mul_div_cancel' hg
    rw [h] at hmul
    rw [h2c]
    omega
  · intro h
    rw [h, h2c, hc]
    have hcpos : 0 < c := by omega
    exact Nat.mul_div_cancel 2 hcpos

end Qatlib.Papers.SemiprimeFact15.MainResults
