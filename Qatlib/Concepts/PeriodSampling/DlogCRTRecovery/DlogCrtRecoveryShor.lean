/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogCRTRecovery.DlogCrtRecoveryStat
import Mathlib.Tactic.NormNum.Prime

/-!
# CRT uniqueness with a bounded discrete logarithm

This module proves `DlogCrtRecovery`: sampling congruences determine an exponent in the range
below `p - 1` when large prime divisors have nondivisibility witnesses and residues agree at the
full powers of small prime divisors. The proof combines prime-power divisibility with equality
of bounded representatives, in the modular recovery setting of [Shor1997].

The module also defines `DlogCrtRecoveryOriginal`, which omits the target exponent's range
restriction, and refutes it using `p = 3`, `q = 4`, and target exponent two.

## Main statements

* `DlogCrtRecoveryOriginal`: the uniqueness proposition without a target range hypothesis.
* `dlogCrtRecovery_false`: a counterexample to that proposition.
* `dlogCrtRecovery`: the corrected uniqueness theorem for bounded target and competing
  exponents.

## References

* [Shor, 1997, Section 6][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.DlogCRTRecovery

/-- The CRT recovery uniqueness statement with range restriction on the competing exponent but
no range restriction on the target exponent. -/
def DlogCrtRecoveryOriginal : Prop :=
  ∀ (p q r : ℕ) [NeZero p], Nat.Prime p → 3 ≤ p → (p : ℕ) < q →
    ∀ (t : ℕ) (c : Fin t → Fin q) (d' : Fin t → ℤ),
      (∀ i, (d' i + r * dlogCprime p q (c i) : ℤ)
          % ((p - 1 : ℕ) : ℤ) = 0) →
      (∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ p - 1 → 18 < ℓ →
          ∃ i, ¬ (ℓ : ℤ) ∣ dlogCprime p q (c i)) →
      ∀ r' : ℕ, r' < p - 1 →
        (∀ i, (d' i + r' * dlogCprime p q (c i) : ℤ)
            % ((p - 1 : ℕ) : ℤ) = 0) →
        (∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ p - 1 → ℓ ≤ 18 →
            r' % ℓ ^ ((p - 1).factorization ℓ)
              = r % ℓ ^ ((p - 1).factorization ℓ)) →
        r' = r

/-- The unrestricted-target CRT recovery statement is false, as witnessed by `p = 3`, `q = 4`,
`r = 2`, and competing exponent zero. -/
theorem dlogCrtRecovery_false : ¬ DlogCrtRecoveryOriginal := by
  intro h
  have hh := h 3 4 2 (by norm_num) (by norm_num) (by norm_num)
    1 (fun _ => (0 : Fin 4)) (fun _ => (0 : ℤ))
    (by intro i; norm_num [dlogCprime, centeredResidue])
    (by
      intro ℓ hprime hdiv hlarge
      have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) (by simpa using! hdiv)
      omega)
    0 (by norm_num)
    (by intro i; norm_num [dlogCprime, centeredResidue])
    (by
      intro ℓ hprime hdiv hsmall
      have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) (by simpa using! hdiv)
      have hge := hprime.two_le
      have heq : ℓ = 2 := by omega
      subst ℓ
      norm_num [Nat.Prime.factorization Nat.prime_two])
  norm_num at hh

/-- For a target exponent in `[0, p - 1)`, the sampling congruences, large-prime nondivisibility
witnesses, and matching small-prime-power residues uniquely determine the exponent in that
range [Shor1997]. -/
theorem dlogCrtRecovery : DlogCrtRecovery := by
  intro p q r _ _ hp hpq hr t c d' hcong hlarge r' hr' hcong' hsmall
  let δ : ℤ := (r' : ℤ) - (r : ℤ)
  have hm : p-1 ≠ 0 := by omega
  have hdiv : (p-1) ∣ δ.natAbs := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd δ.natAbs (p-1)).2
    intro ℓ a hℓ hpow
    by_cases ha : a = 0
    · simp [ha]
    apply Int.natCast_dvd.mp
    by_cases hs : ℓ ≤ 18
    · have hld : ℓ ∣ p-1 := dvd_trans (dvd_pow_self ℓ ha) hpow
      have hexp : a ≤ (p-1).factorization ℓ :=
        (hℓ.pow_dvd_iff_le_factorization hm).mp hpow
      have hmax : ((ℓ ^ (p-1).factorization ℓ : ℕ) : ℤ) ∣ δ :=
        Nat.ModEq.dvd (hsmall ℓ hℓ hld hs).symm
      exact dvd_trans (by exact_mod_cast (pow_dvd_pow ℓ hexp)) hmax
    · have hld : ℓ ∣ p-1 := dvd_trans (dvd_pow_self ℓ ha) hpow
      obtain ⟨i,hi⟩ := hlarge ℓ hℓ hld (by omega)
      have hdelta : ((p-1 : ℕ) : ℤ) ∣ δ * dlogCprime p q (c i) := by
        have h1 := Int.dvd_of_emod_eq_zero (hcong' i)
        have h2 := Int.dvd_of_emod_eq_zero (hcong i)
        convert! dvd_sub h1 h2 using 1
        dsimp [δ]
        ring
      have hprod : ((ℓ^a : ℕ) : ℤ) ∣ δ * dlogCprime p q (c i) :=
        dvd_trans (by exact_mod_cast hpow) hdelta
      have hc : Nat.Coprime ℓ (dlogCprime p q (c i)).natAbs :=
        hℓ.coprime_iff_not_dvd.mpr (fun h => hi (Int.natCast_dvd.mpr h))
      have hn := Int.natCast_dvd.mp hprod
      rw [Int.natAbs_mul] at hn
      exact Int.natCast_dvd.mpr ((hc.pow_left a).dvd_of_dvd_mul_right hn)
  have hmod : Nat.ModEq (p-1) r r' :=
    Nat.modEq_iff_dvd.mpr (Int.natCast_dvd.mpr hdiv)
  exact (hmod.eq_of_lt_of_lt hr hr').symm

end Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
