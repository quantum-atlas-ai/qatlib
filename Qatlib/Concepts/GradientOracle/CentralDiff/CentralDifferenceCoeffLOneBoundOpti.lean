/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceCoeffLOneBoundStat
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A one-sided mass bound for central-difference coefficients

`centralDiffCoeff_nat_abs_le` bounds each nonnegative-index coefficient by the reciprocal index,
with the zero-index case interpreted using real division. Summing these bounds proves
`centralDifferenceCoeffLOneBound`, the one-sided logarithmic mass estimate. See
[GilyenArunachalamWiebe2019] for background.

## Main statements

* `centralDiffCoeff_nat_abs_le`: The absolute central-difference coefficient at natural index
  `k` is at most `1 / k`.
* `centralDifferenceCoeffLOneBound`: For positive order `m`, the sum of absolute coefficients
  over integer indices from zero through `m` is at most `Real.log m + 1`.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

namespace Qatlib.Concepts.GradientOracle.CentralDiff

/-- The absolute central-difference coefficient at natural index `k` is at most `1 / k`. -/
theorem centralDiffCoeff_nat_abs_le (m k : ℕ) :
    |centralDiffCoeff m (k : ℤ)| ≤ 1 / (k : ℝ) := by
  by_cases hk : k = 0
  · simp [hk, centralDiffCoeff]
  · have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hden : 0 < (Nat.choose (m + k) k : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : k ≤ m + k)
    have hnum : (Nat.choose m k : ℝ) ≤ Nat.choose (m + k) k := by
      exact_mod_cast Nat.choose_le_add m k k
    rw [centralDiffCoeff, if_neg (by exact_mod_cast hk)]
    simp only [Int.natAbs_natCast, Int.cast_natCast, abs_div, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
      abs_of_nonneg (Nat.cast_nonneg (Nat.choose m k) : (0 : ℝ) ≤ Nat.choose m k),
      abs_of_nonneg (Nat.cast_nonneg (Nat.choose (m + k) k) : (0 : ℝ) ≤ Nat.choose (m + k) k)]
    calc
      _ = (1 / (k : ℝ)) * ((Nat.choose m k : ℝ) / Nat.choose (m + k) k) := by ring
      _ ≤ (1 / (k : ℝ)) * 1 := mul_le_mul_of_nonneg_left ((div_le_one hden).2 hnum)
        (by positivity)
      _ = _ := mul_one _

/-- For positive order `m`, the sum of absolute coefficients over integer indices from zero
through `m` is at most `Real.log m + 1`. -/
theorem centralDifferenceCoeffLOneBound : CentralDifferenceCoeffLOneBound := by
  classical
  intro m _
  have hs : (∑ ℓ ∈ Finset.Ico (0 : ℤ) ((m : ℤ) + 1), |centralDiffCoeff m ℓ|) =
      ∑ k ∈ Finset.range (m + 1), |centralDiffCoeff m (k : ℤ)| := by
    apply Finset.sum_bij (fun ℓ _ => ℓ.toNat)
    · intro ℓ hℓ
      simp only [Finset.mem_Ico, Finset.mem_range] at hℓ ⊢
      omega
    · intro a ha b hb he
      simp only [Finset.mem_Ico] at ha hb
      omega
    · intro k hk
      refine ⟨(k : ℤ), ?_, ?_⟩
      · simp only [Finset.mem_range] at hk
        simp only [Finset.mem_Ico]
        omega
      · simp
    · intro ℓ hℓ
      congr 1
      simp only [Finset.mem_Ico] at hℓ
      rw [Int.toNat_of_nonneg hℓ.1]
  have hh : (∑ k ∈ Finset.range (m + 1), 1 / (k : ℝ)) = (harmonic m : ℝ) := by
    rw [Finset.sum_range_succ']
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, one_div]
  calc
    _ = ∑ k ∈ Finset.range (m + 1), |centralDiffCoeff m (k : ℤ)| := hs
    _ ≤ ∑ k ∈ Finset.range (m + 1), 1 / (k : ℝ) :=
      Finset.sum_le_sum (fun k _ => centralDiffCoeff_nat_abs_le m k)
    _ = (harmonic m : ℝ) := hh
    _ ≤ Real.log m + 1 := by simpa only [add_comm] using harmonic_le_one_add_log m

end Qatlib.Concepts.GradientOracle.CentralDiff
