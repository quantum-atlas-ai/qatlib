/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPreprocessingStat
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Soundness of factoring preprocessing

Proves the properties of the perfect-power search and uses them to establish
`factoringPreprocessing`. Returned factors are proper nontrivial divisors, while the residue
branch leaves an odd input that is prime or has at least two distinct prime factors, as needed
in the framework of [Shor1997].

## Main statements

* `factoringPreprocessing`: Establishes factor soundness and the residue-branch conditions.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open scoped Classical

/-- Any base returned by `shorPerfectPowerDivisor` is a proper nontrivial divisor of `N`. -/
private theorem perfectPower_sound (N d : ℕ)
    (h : shorPerfectPowerDivisor N = some d) : 1 < d ∧ d < N ∧ d ∣ N := by
  have hd : d ∈ ((Finset.range N).filter fun m =>
      2 ≤ m ∧ ∃ e ∈ Finset.Icc 2 N, m ^ e = N).toList :=
    List.mem_of_mem_head? (by simpa [shorPerfectPowerDivisor] using! h)
  simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Icc] at hd
  obtain ⟨hlt, htwo, e, ⟨he, _⟩, hpow⟩ := hd
  refine ⟨by omega, hlt, ?_⟩
  rw [← hpow]
  exact dvd_pow_self d (by omega)

/-- If the perfect-power search returns `none`, no base in the stated range and exponent in `[2,
N]` represent `N` as a perfect power. -/
private theorem perfectPower_none (N : ℕ) (h : shorPerfectPowerDivisor N = none) :
    ¬ ∃ m < N, 2 ≤ m ∧ ∃ e ∈ Finset.Icc 2 N, m ^ e = N := by
  intro ⟨m, hm, hm2, e, he, hpow⟩
  have hempty : ((Finset.range N).filter fun m =>
      2 ≤ m ∧ ∃ e ∈ Finset.Icc 2 N, m ^ e = N) = ∅ := by
    simpa [shorPerfectPowerDivisor] using! h
  have hmem : m ∈ ((Finset.range N).filter fun m =>
      2 ≤ m ∧ ∃ e ∈ Finset.Icc 2 N, m ^ e = N) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hm, hm2, e, he, hpow⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty m hmem

/-- Establishes soundness of factoring preprocessing and the stated oddness and prime-factor
conditions for its residue branch in the framework of [Shor1997]. -/
theorem factoringPreprocessing : FactoringPreprocessing := by
  constructor
  · intro N d hN h
    unfold shorPreprocess at h
    split at h
    · rename_i he
      cases h
      exact ⟨by omega, by omega, he.2⟩
    · split at h
      · rename_i m hm
        cases h
        exact perfectPower_sound N d hm
      · cases h
  · intro N hN h
    unfold shorPreprocess at h
    split at h
    · cases h
    · rename_i he
      split at h
      · cases h
      · rename_i hp
        have hnotdvd : ¬ 2 ∣ N := by
          intro hd
          have h4 : 4 ≤ N := by omega
          exact he ⟨h4, hd⟩
        refine ⟨Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using! hnotdvd), ?_⟩
        by_cases hprime : Nat.Prime N
        · exact Or.inl hprime
        · right
          by_contra hc
          have hpos : 0 < N.primeFactors.card :=
            Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
          have hcard : N.primeFactors.card = 1 := by omega
          obtain ⟨p, hpN, e, heN, hprimep, hepos, hpow⟩ :=
            (isPrimePow_nat_iff_bounded N).mp
              (isPrimePow_iff_card_primeFactors_eq_one.mpr hcard)
          have he2 : 2 ≤ e := by
            by_contra hh
            have he1 : e = 1 := by omega
            simp only [he1, pow_one] at hpow
            exact hprime (hpow ▸ hprimep)
          have hpLt : p < N := by
            rw [← hpow]
            calc p = p ^ 1 := (pow_one p).symm
                 _ < p ^ e := Nat.pow_lt_pow_right hprimep.one_lt (by omega)
          exact perfectPower_none N hp ⟨p, hpLt, hprimep.two_le, e,
            Finset.mem_Icc.mpr ⟨he2, heN⟩, hpow⟩

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
