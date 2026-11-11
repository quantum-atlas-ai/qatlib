/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 6: a logarithmic lower bound for the totient ratio

Fixed version: arXiv:2608.15545v1 (2026-08-16), Lemma 6 (p.14) and its proof
in Appendix F (p.25-26, Eqs. (F5)-(F6)).  Paper: *Quantum Advantage with
Adaptive Shallow Circuits*.

**Paper statement (Eq. (F5)).**  There is an absolute constant `α > 0` such
that for every integer `r ≥ 3`,

```
φ(r)/r ≥ α / log r.                                                   (F5)
```

The paper's proof writes the Euler product

```
φ(r)/r = ∏_{q | r} (1 - 1/q)                                          (F6)
```

and compares it with `∏_{q ≤ r} (1 - 1/q) = Θ(1/log r)` by Mertens' third
theorem.

**What is proved here.**  The Mertens comparison is not needed.  A purely
elementary argument already gives the stated form:

* `totient_ratio_eq_prod` — the exact Euler product (F6) over the distinct
  prime divisors, in `ℝ`;
* `prod_one_sub_inv_ge` — for any finite set `s` of primes,
  `∏_{q ∈ s} (1 - 1/q) ≥ 1/(|s| + 1)`.  The proof removes the largest prime
  `q` and uses `|s| ≤ q - 1` (the primes of `s` are distinct and all lie in
  `{2, …, q}`), which is enough for the induction step;
* `primeFactors_card_two_pow_le` — `2^{ω(r)} ≤ r`, because the product of the
  distinct prime divisors divides `r` and each is at least `2`;
* combining the two gives `φ(r)/r ≥ 1/(ω(r) + 1) ≥ 1/(log₂ r + 1) ≥ α/log r`
  with `α = (log 2)/2`, valid for every `r ≥ 3`.

The resulting constant is smaller than Mertens' but is absolute, which is all
Lemma 6 asserts.  No `sorry` remains and no additional axiom is used.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.TotientBound

/-- Euler's totient never exceeds its argument (`φ(r) ≤ r`). -/
theorem totient_le_self (r : ℕ) : Nat.totient r ≤ r :=
  Nat.totient_le r

/-- **Normalization of the totient ratio.**  For `r > 0`, `φ(r)/r ≤ 1`; the
ratio in Eq. (F5) is a probability. -/
theorem totient_ratio_le_one (r : ℕ) (hr : 0 < r) :
    (Nat.totient r : ℝ) / (r : ℝ) ≤ 1 := by
  have hle : (Nat.totient r : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast Nat.totient_le r
  have hpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  rw [div_le_one hpos]
  exact hle

/-- **Eq. (F6), Euler product over the distinct prime divisors.**  For `r ≠ 0`,
`φ(r)/r = ∏_{q | r} (1 - 1/q)` as a real product over `r.primeFactors`. -/
theorem totient_ratio_eq_prod (r : ℕ) (hr : r ≠ 0) :
    (Nat.totient r : ℝ) / (r : ℝ)
      = ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)) := by
  have hQ := Nat.totient_eq_mul_prod_factors r
  have hR : (Nat.totient r : ℝ) = (r : ℝ) * ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hQ
    push_cast at h
    simpa using h
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  rw [hR, mul_div_cancel_left₀ _ hrR]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [one_div]

/-- **Product bound for a set of primes.**  For any finite set `s` of primes,
`∏_{q ∈ s} (1 - 1/q) ≥ 1/(|s| + 1)`.

The proof peels off the largest prime `q`.  Since the elements of `s` are
`|s|` distinct primes all lying in `{2, …, q}`, we have `|s| ≤ q - 1`, which is
exactly the inequality needed for `(1 - 1/q) · 1/|s| ≥ 1/(|s|+1)`. -/
theorem prod_one_sub_inv_ge : ∀ (k : ℕ) (s : Finset ℕ), s.card = k →
    (∀ p ∈ s, p.Prime) → 1 / ((k : ℝ) + 1) ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ))
  | 0, s, hs, _ => by
    have hz : s = ∅ := Finset.card_eq_zero.mp hs
    subst hz
    simp
  | k + 1, s, hs, hp => by
    have hne : s.Nonempty := Finset.card_pos.mp (by omega : 0 < s.card)
    set q := s.max' hne with hq
    have hqmem : q ∈ s := Finset.max'_mem s hne
    have hqle : ∀ p ∈ s, p ≤ q := fun p hpm => Finset.le_max' s p hpm
    have hqprime : q.Prime := hp q hqmem
    set t := s.erase q with ht
    have htsub : t ⊆ s := fun p hpm => Finset.mem_of_mem_erase hpm
    have htprime : ∀ p ∈ t, p.Prime := fun p hpm => hp p (htsub hpm)
    have htcard : t.card = k := by
      rw [Finset.card_erase_of_mem hqmem]
      omega
    have hsq : s = insert q t := (Finset.insert_erase hqmem).symm
    have hIH := prod_one_sub_inv_ge k t htcard htprime
    have hq_ge : k + 2 ≤ q := by
      have hsub : s ⊆ Finset.Icc 2 q := fun p hpm =>
        Finset.mem_Icc.mpr ⟨(hp p hpm).two_le, hqle p hpm⟩
      have h1 : s.card ≤ (Finset.Icc 2 q).card := Finset.card_le_card hsub
      have h2 : (Finset.Icc 2 q).card = q + 1 - 2 := Nat.card_Icc 2 q
      omega
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have := hqprime.two_le
      exact_mod_cast (by omega : 0 < q)
    have hfac_nonneg : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := by
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqprime.two_le
      have h3 : 1 / (q : ℝ) ≤ 1 := by
        rw [div_le_one hqR]
        linarith
      linarith
    have hRHS : (1 - 1 / (q : ℝ)) * (1 / ((k : ℝ) + 1))
        = ((q : ℝ) - 1) / ((q : ℝ) * ((k : ℝ) + 1)) := by
      field_simp
      try ring
    have hkey : 1 / ((k : ℝ) + 2) ≤ (1 - 1 / (q : ℝ)) * (1 / ((k : ℝ) + 1)) := by
      have hq_geR : (k : ℝ) + 2 ≤ (q : ℝ) := by exact_mod_cast hq_ge
      rw [hRHS, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [hsq, Finset.prod_insert (Finset.notMem_erase q s)]
    have hL : (1 : ℝ) / (((k + 1 : ℕ)) + 1) = 1 / ((k : ℝ) + 2) := by
      congr 1
      push_cast
      ring
    rw [hL]
    exact le_trans hkey (mul_le_mul_of_nonneg_left hIH hfac_nonneg)

/-- **Prime-divisor count bound.**  `2^{ω(r)} ≤ r` for `r ≠ 0`: the product of
the distinct prime divisors divides `r`, and each divisor is at least `2`. -/
theorem primeFactors_card_two_pow_le (r : ℕ) (hr : r ≠ 0) :
    2 ^ r.primeFactors.card ≤ r := by
  have hdvd : (∏ p ∈ r.primeFactors, p) ∣ r := Nat.prod_primeFactors_dvd r
  have hle : (∏ p ∈ r.primeFactors, p) ≤ r := Nat.le_of_dvd (by omega) hdvd
  have hpow : 2 ^ r.primeFactors.card ≤ ∏ p ∈ r.primeFactors, p :=
    Finset.pow_card_le_prod r.primeFactors (fun p => p) 2
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  exact le_trans hpow hle

/-- **Lemma 6, Eq. (F5).**  There is an absolute constant `α = (log 2)/2 > 0`
such that for every integer `r ≥ 3`,

`φ(r)/r ≥ α / log r`.

See the module docstring for the elementary proof replacing Mertens' theorem. -/
theorem totient_lower_bound :
    ∃ α : ℝ, 0 < α ∧ ∀ r : ℕ, 3 ≤ r →
      α / Real.log (r : ℝ) ≤ (Nat.totient r : ℝ) / (r : ℝ) := by
  refine ⟨Real.log 2 / 2, by positivity, ?_⟩
  intro r hr
  have hr0 : r ≠ 0 := by omega
  have hr2 : 2 ≤ r := by omega
  have hrR : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 < r)
  set k := r.primeFactors.card with hk
  have hprod : 1 / ((k : ℝ) + 1) ≤ (Nat.totient r : ℝ) / (r : ℝ) := by
    rw [totient_ratio_eq_prod r hr0]
    exact prod_one_sub_inv_ge k r.primeFactors rfl
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have h2k : 2 ^ k ≤ r := primeFactors_card_two_pow_le r hr0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hrR
  have hk_le : (k : ℝ) ≤ Real.log (r : ℝ) / Real.log 2 := by
    have hlog : Real.log ((2 : ℝ) ^ k) ≤ Real.log (r : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast h2k
    rw [Real.log_pow] at hlog
    rw [le_div_iff₀ hlog2]
    linarith
  have hbound1 : 1 / (Real.log (r : ℝ) / Real.log 2 + 1) ≤ 1 / ((k : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (a := (k : ℝ) + 1)
    · positivity
    · linarith
  have hbound2 : (Real.log 2 / 2) / Real.log (r : ℝ)
      ≤ 1 / (Real.log (r : ℝ) / Real.log 2 + 1) := by
    have hle : Real.log 2 ≤ Real.log (r : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hr2)
    have h1 : (1 : ℝ) / (Real.log (r : ℝ) / Real.log 2 + 1)
        = Real.log 2 / (Real.log (r : ℝ) + Real.log 2) := by
      field_simp
      try ring
    have h2 : (Real.log 2 / 2) / Real.log (r : ℝ)
        = Real.log 2 / (2 * Real.log (r : ℝ)) := by
      field_simp
    rw [h1, h2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc (Real.log 2 / 2) / Real.log (r : ℝ)
      ≤ 1 / (Real.log (r : ℝ) / Real.log 2 + 1) := hbound2
    _ ≤ 1 / ((k : ℝ) + 1) := hbound1
    _ ≤ (Nat.totient r : ℝ) / (r : ℝ) := hprod

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.TotientBound
