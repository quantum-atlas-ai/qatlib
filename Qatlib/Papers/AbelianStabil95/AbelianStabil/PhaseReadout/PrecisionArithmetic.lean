/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout.ReadoutParameters

/-!
# Precision arithmetic for phase recovery

This module collects the dyadic precision identities and rational-separation estimates used in
phase recovery. `rational_separation` bounds the distance between distinct rational numbers with
bounded denominators, and `rational_readout_unique` proves uniqueness inside the corresponding
common approximation window. The development follows [Kitaev1995].

## Main statements

* `rational_separation`: separates distinct rationals with denominators at most `2 ^ n`.
* `rational_readout_unique`: proves equality of two bounded-denominator candidates close to the
  same estimate.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

/-- Multiplying the dyadic factor `2 ^ (-l + 1)` by one eighth gives `2 ^ (-l - 2)`, the
precision identity used in [Kitaev, 1995, Lemma 10][Kitaev1995]. -/
theorem bisect_combine (l : ℕ) :
    (1 / 8 : ℝ) * (2 : ℝ) ^ (-(l : ℤ) + 1) = (2 : ℝ) ^ (-(l : ℤ) - 2) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hsplit : (-(l : ℤ) - 2 : ℤ) = (-(l : ℤ) + 1) - 3 := by ring
  rw [hsplit, zpow_sub₀ h2]
  have h3 : (2 : ℝ) ^ (3 : ℤ) = 8 := by norm_num
  rw [h3]
  ring

/-- For positive `l`, summing `l` identical error allocations `ε / l` gives `ε`, as used in the
readout analysis of [Kitaev1995]. -/
theorem per_coordinate_failure_sum {l : ℕ} (hl : 0 < l) (ε : ℝ) :
    (l : ℝ) * (ε / (l : ℝ)) = ε := by
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  field_simp

/-- The difference of two rational expressions with nonzero natural denominators equals their
cross numerator divided by the product of denominators. -/
theorem div_sub_div_eq (p q p' q' : ℕ) (hq : q ≠ 0) (hq' : q' ≠ 0) :
    (p : ℝ) / (q : ℝ) - (p' : ℝ) / (q' : ℝ)
      = ((p : ℝ) * (q' : ℝ) - (p' : ℝ) * (q : ℝ))
          / ((q : ℝ) * (q' : ℝ)) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hq'R : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'
  field_simp

/-- If two rational expressions with nonzero natural denominators differ, the absolute value of
their integer cross numerator is at least one. -/
theorem cross_numerator_abs_ge_one {p q p' q' : ℕ} (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hne : (p : ℝ) / (q : ℝ) ≠ (p' : ℝ) / (q' : ℝ)) :
    (1 : ℝ) ≤ |(p : ℝ) * (q' : ℝ) - (p' : ℝ) * (q : ℝ)| := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq'
  have hNne : p * q' ≠ p' * q := by
    intro h
    apply hne
    have hreal : (p : ℝ) * (q' : ℝ) = (p' : ℝ) * (q : ℝ) := by
      exact_mod_cast h
    rw [div_eq_div_iff hqR.ne' hq'R.ne']
    linarith
  rcases lt_or_gt_of_ne hNne with hlt | hgt
  · have hstep : p * q' + 1 ≤ p' * q := Nat.succ_le_of_lt hlt
    have hreal : (p : ℝ) * (q' : ℝ) + 1 ≤ (p' : ℝ) * (q : ℝ) := by
      exact_mod_cast hstep
    have hnonpos : (p : ℝ) * (q' : ℝ) - (p' : ℝ) * (q : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  · have hstep : p' * q + 1 ≤ p * q' := Nat.succ_le_of_lt hgt
    have hreal : (p' : ℝ) * (q : ℝ) + 1 ≤ (p : ℝ) * (q' : ℝ) := by
      exact_mod_cast hstep
    have hnonneg : 0 ≤ (p : ℝ) * (q' : ℝ) - (p' : ℝ) * (q : ℝ) := by linarith
    rw [abs_of_nonneg hnonneg]
    linarith

/-- For positive `n`, distinct rational expressions with positive denominators at most `2 ^ n`
differ by more than `1 / (2 ^ n * 2 ^ n)`. This is the separation estimate used for [Kitaev,
1995, Theorem 1][Kitaev1995]. -/
theorem rational_separation {p q p' q' n : ℕ} (hn : 0 < n)
    (hq : 0 < q) (hq' : 0 < q') (hqle : q ≤ 2 ^ n) (hq'le : q' ≤ 2 ^ n)
    (hne : (p : ℝ) / (q : ℝ) ≠ (p' : ℝ) / (q' : ℝ)) :
    (1 : ℝ) / ((2 : ℝ) ^ n * (2 : ℝ) ^ n) <
      |(p : ℝ) / (q : ℝ) - (p' : ℝ) / (q' : ℝ)| := by
  have hqne : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  have hq'ne : q' ≠ 0 := Nat.pos_iff_ne_zero.mp hq'
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have hpow1 : (1 : ℝ) < (2 : ℝ) ^ n := by
    have : (2 : ℝ) ^ 0 < (2 : ℝ) ^ n := by
      exact pow_lt_pow_right₀ (by norm_num) hn
    simpa using this
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hnum := cross_numerator_abs_ge_one hqne hq'ne hne
  have hdiff := div_sub_div_eq p q p' q' hqne hq'ne
  have hqqpos : (0 : ℝ) < (q : ℝ) * (q' : ℝ) := mul_pos hqR hq'R
  have habs : |(p : ℝ) / (q : ℝ) - (p' : ℝ) / (q' : ℝ)|
      = |(p : ℝ) * (q' : ℝ) - (p' : ℝ) * (q : ℝ)| / ((q : ℝ) * (q' : ℝ)) := by
    rw [hdiff, abs_div, abs_of_pos hqqpos]
  rw [habs]

  by_cases hqq : q = q'
  · subst hqq

    have hpp' : p ≠ p' := by
      intro hpp
      exact hne (by rw [hpp])
    have hnum' : (1 : ℝ) ≤ |(p : ℝ) - (p' : ℝ)| := by
      rcases lt_or_gt_of_ne hpp' with hlt | hgt
      · have hstep : p + 1 ≤ p' := Nat.succ_le_of_lt hlt
        have hreal : (p : ℝ) + 1 ≤ (p' : ℝ) := by exact_mod_cast hstep
        have : (p : ℝ) - (p' : ℝ) ≤ 0 := by linarith
        rw [abs_of_nonpos this]; linarith
      · have hstep : p' + 1 ≤ p := Nat.succ_le_of_lt hgt
        have hreal : (p' : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hstep
        have : 0 ≤ (p : ℝ) - (p' : ℝ) := by linarith
        rw [abs_of_nonneg this]; linarith
    have hsimp : |(p : ℝ) * (q : ℝ) - (p' : ℝ) * (q : ℝ)|
        = |(p : ℝ) - (p' : ℝ)| * (q : ℝ) := by
      rw [show (p : ℝ) * (q : ℝ) - (p' : ℝ) * (q : ℝ)
            = ((p : ℝ) - (p' : ℝ)) * (q : ℝ) by ring]
      rw [abs_mul, abs_of_pos hqR]
    rw [hsimp]
    have hgoal : (1 : ℝ) / ((2 : ℝ) ^ n * (2 : ℝ) ^ n) <
        |(p : ℝ) - (p' : ℝ)| * (q : ℝ) / ((q : ℝ) * (q : ℝ)) := by
      have hq2 : (0 : ℝ) < (q : ℝ) * (q : ℝ) := mul_pos hqR hqR
      have hqleR : (q : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hqle

      have hval : |(p : ℝ) - (p' : ℝ)| * (q : ℝ) / ((q : ℝ) * (q : ℝ))
          = |(p : ℝ) - (p' : ℝ)| / (q : ℝ) := by
        field_simp
      rw [hval]
      have h1 : (1 : ℝ) / (q : ℝ) ≤ |(p : ℝ) - (p' : ℝ)| / (q : ℝ) := by
        have := div_le_div_of_nonneg_right hnum' hqR.le
        simpa using this
      have h2 : (1 : ℝ) / ((2 : ℝ) ^ n * (2 : ℝ) ^ n) < (1 : ℝ) / (q : ℝ) := by
        have hAA : (2 : ℝ) ^ n < (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
          have hpos : 0 < (2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1) :=
            mul_pos hpowpos (by linarith)
          nlinarith
        have hqlt : (q : ℝ) < (2 : ℝ) ^ n * (2 : ℝ) ^ n := lt_of_le_of_lt hqleR hAA
        exact one_div_lt_one_div_of_lt hqR hqlt
      linarith
    exact hgoal
  · have hqleR : (q : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hqle
    have hq'leR : (q' : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hq'le
    have hstrict : (q : ℝ) * (q' : ℝ) < (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
      rcases lt_or_gt_of_ne hqq with hlt | hgt
      · have hqlt : (q : ℝ) < (2 : ℝ) ^ n := by
          have hqltNat : q < 2 ^ n := by omega
          exact_mod_cast hqltNat
        nlinarith [hqR, hq'R, hqleR, hq'leR, hqlt, hpowpos]
      · have hq'ltNat : q' < 2 ^ n := by omega
        have hq'lt : (q' : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast hq'ltNat
        nlinarith [hqR, hq'R, hqleR, hq'leR, hq'lt, hpowpos]
    have hdiv : (1 : ℝ) / ((2 : ℝ) ^ n * (2 : ℝ) ^ n) < 1 / ((q : ℝ) * (q' : ℝ)) :=
      one_div_lt_one_div_of_lt hqqpos hstrict
    have hfracge : (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤
        |(p : ℝ) * (q' : ℝ) - (p' : ℝ) * (q : ℝ)| / ((q : ℝ) * (q' : ℝ)) := by
      have := div_le_div_of_nonneg_right hnum hqqpos.le
      simpa using this
    linarith

/-- For positive `n`, two rational candidates with positive denominators at most `2 ^ n` are
equal if each is within `1 / (2 * 2 ^ n * 2 ^ n)` of the same real estimate. -/
theorem rational_readout_unique {φ ψ φ' : ℝ} {p q p' q' n : ℕ} (hn : 0 < n)
    (hq : 0 < q) (hq' : 0 < q') (hqle : q ≤ 2 ^ n) (hq'le : q' ≤ 2 ^ n)
    (hφ : φ = (p : ℝ) / (q : ℝ)) (hψ : ψ = (p' : ℝ) / (q' : ℝ))
    (hφ' : |φ' - φ| ≤ (1 : ℝ) / (2 * (2 : ℝ) ^ n * (2 : ℝ) ^ n))
    (hψ' : |φ' - ψ| ≤ (1 : ℝ) / (2 * (2 : ℝ) ^ n * (2 : ℝ) ^ n)) :
    φ = ψ := by
  by_contra hne
  have hne' : (p : ℝ) / (q : ℝ) ≠ (p' : ℝ) / (q' : ℝ) := by
    intro h
    exact hne (by rw [hφ, hψ, h])
  have hsep := rational_separation hn hq hq' hqle hq'le hne'
  have hsum : |φ - ψ| ≤ 2 * ((1 : ℝ) / (2 * (2 : ℝ) ^ n * (2 : ℝ) ^ n)) := by
    calc |φ - ψ| = |(φ - φ') + (φ' - ψ)| := by
            congr 1
            ring
      _ ≤ |φ - φ'| + |φ' - ψ| := abs_add_le _ _
      _ ≤ _ := by
          have h1 : |φ - φ'| ≤ (1 : ℝ) / (2 * (2 : ℝ) ^ n * (2 : ℝ) ^ n) := by
            simpa [abs_sub_comm] using hφ'
          linarith
  have hsimple : 2 * ((1 : ℝ) / (2 * (2 : ℝ) ^ n * (2 : ℝ) ^ n))
      = 1 / ((2 : ℝ) ^ n * (2 : ℝ) ^ n) := by
    field_simp
  rw [hsimple] at hsum
  have hdiff : |φ - ψ| = |(p : ℝ) / (q : ℝ) - (p' : ℝ) / (q' : ℝ)| := by
    rw [hφ, hψ]
  rw [hdiff] at hsum
  linarith

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
