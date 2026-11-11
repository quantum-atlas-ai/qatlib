/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

/-!
# Automorphisms preserve coprime prime-power factors

Additive automorphisms of the product of cyclic groups of orders `q ^ s` and `p ^ r` preserve
each factor when `p` and `q` are distinct primes. `lemma1_componentwise` expresses this by
showing that the off-factor coordinates vanish. See [ChiKimLee2006] for the mathematical
setting.

## Main statements

* `zmod_eq_zero_of_nsmul_eq_zero`: eliminates torsion killed by an integer coprime to the
  modulus.
* `lemma1_componentwise`: proves vanishing of the off-factor coordinates under an additive
  automorphism.

## References

* [Chi et al., 2006][ChiKimLee2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

/-- If `k` is coprime to `n`, a residue modulo `n` annihilated by `k` is zero. -/
lemma zmod_eq_zero_of_nsmul_eq_zero {n k : ℕ} (hcop : Nat.Coprime k n) {x : ZMod n}
    (h : k • x = 0) : x = 0 := by
  have hunit : IsUnit ((k : ℕ) : ZMod n) := (ZMod.isUnit_iff_coprime k n).2 hcop
  have hk : ((k : ℕ) : ZMod n) * x = 0 := by rw [← nsmul_eq_mul]; exact h
  obtain ⟨v, hv⟩ := hunit
  rw [← hv] at hk
  have : x = ↑v⁻¹ * (↑v * x) := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hk, mul_zero] at this
  exact this

/-- Powers of distinct primes are coprime. -/
lemma coprime_prime_powers {p q s r : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime (q ^ s) (p ^ r) := by
  have hqnp : ¬ q ∣ p := by
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have hcqp : Nat.Coprime q p := (Nat.Prime.coprime_iff_not_dvd hq).2 hqnp
  exact hcqp.pow s r

/-- For distinct primes `p` and `q` and positive exponents, an additive automorphism of `ZMod (q
^ s) × ZMod (p ^ r)` maps each coordinate factor into itself. See [Chi et al., 2006, Lemma
1][ChiKimLee2006]. -/
theorem lemma1_componentwise {p q s r : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hs : 0 < s) (hr : 0 < r)
    (F : ZMod (q ^ s) × ZMod (p ^ r) ≃+ ZMod (q ^ s) × ZMod (p ^ r))
    (a : ZMod (q ^ s)) (b : ZMod (p ^ r)) :
    (F (a, 0)).2 = 0 ∧ (F (0, b)).1 = 0 := by
  have hcop : Nat.Coprime (q ^ s) (p ^ r) := coprime_prime_powers hp hq hpq
  constructor
  · have hsmul : (q ^ s) • (a, 0) = (0 : ZMod (q ^ s) × ZMod (p ^ r)) := by
      apply Prod.ext
      · show (q ^ s) • a = 0
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      · show (q ^ s) • (0 : ZMod (p ^ r)) = 0
        simp
    have h0 : (q ^ s) • F (a, 0) = 0 := by
      have hmap : F ((q ^ s) • (a, 0)) = (q ^ s) • F (a, 0) := map_nsmul F (q ^ s) (a, 0)
      rw [hsmul, map_zero] at hmap
      exact hmap.symm
    have h0' : (q ^ s) • (F (a, 0)).2 = 0 := by
      simpa using congrArg Prod.snd h0
    exact zmod_eq_zero_of_nsmul_eq_zero hcop h0'
  · have hsmul : (p ^ r) • (0, b) = (0 : ZMod (q ^ s) × ZMod (p ^ r)) := by
      apply Prod.ext
      · show (p ^ r) • (0 : ZMod (q ^ s)) = 0
        simp
      · show (p ^ r) • b = 0
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have h0 : (p ^ r) • F (0, b) = 0 := by
      have hmap : F ((p ^ r) • (0, b)) = (p ^ r) • F (0, b) := map_nsmul F (p ^ r) (0, b)
      rw [hsmul, map_zero] at hmap
      exact hmap.symm
    have h0' : (p ^ r) • (F (0, b)).1 = 0 := by
      simpa using congrArg Prod.fst h0
    exact zmod_eq_zero_of_nsmul_eq_zero hcop.symm (by simpa using h0')

end Qatlib.Papers.SemiDirectHSP06.MainResults
