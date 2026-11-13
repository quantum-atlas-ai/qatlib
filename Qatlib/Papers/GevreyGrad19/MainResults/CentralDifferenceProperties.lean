/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Exactness, Coefficient Bounds, and Power-Sum Growth of Central Differences

This module formalizes Definition 3.3 and Theorem 3.4 of Cornelissen on the
central-difference coefficients `a_ℓ^{(2m)}`, establishing equivalence with the
printed factorial formula `(-1)^{ℓ+1} (m!)^2 / (ℓ (m+ℓ)! (m-ℓ)!)`, polynomial moment
exactness through degree `2m`, the strict magnitude bound `|a_ℓ^{(2m)}| < 1 / |ℓ|`,
and the higher-moment bound `|∑_{ℓ=-m}^m a_ℓ^{(2m)} ℓ^k| ≤ 2 m^k` for `k ≥ 2m + 1`.

## Main statements

* `paperCentralCoeff_eq_source_formula`: Definition 3.3, equivalence with the factorial formula.
* `paperCentralDifferenceExactness`: Theorem 3.4(1), moment exactness for `k ≤ 2m`.
* `paperCentralCoeff_abs_lt_inv`: Theorem 3.4(2), strict bound `|a_ℓ^{(2m)}| < 1 / |ℓ|`.
* `paperCentralCoeff_powerSumBound`: Theorem 3.4(3), moment growth bound `≤ 2 m^k` for `k ≥ 2m + 1`.

## References

* [Cornelissen, 2019][Cornelissen2019], Section 3, Definition 3.3 and Theorem 3.4, pp. 22--23.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.GevreyGrad19.MainResults

open Qatlib.Concepts.GradientOracle.CentralDiff (centralDiffCoeff
  centralDifferenceExactness)

/-- `a_0^(2m) = 1` (paper Definition 3.3). -/
@[simp] theorem paperCentralCoeff_zero (m : ℕ) : paperCentralCoeff m 0 = 1 := by
  simp [paperCentralCoeff]

/-- For `ℓ ≠ 0` the paper coefficient is the Frozen binomial coefficient. -/
theorem paperCentralCoeff_eq_centralDiffCoeff {m : ℕ} {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    paperCentralCoeff m ℓ = centralDiffCoeff m ℓ := by
  simp [paperCentralCoeff, hℓ]

/-- The `ℓ = 0` value of the Frozen coefficient is zero. -/
@[simp] theorem centralDiffCoeff_zero (m : ℕ) : centralDiffCoeff m 0 = 0 := by
  simp [centralDiffCoeff]

/-- Pointwise bridge: the paper coefficient equals the Frozen coefficient plus a
Kronecker mass at `ℓ = 0`. -/
theorem paperCentralCoeff_eq_add_delta (m : ℕ) (ℓ : ℤ) :
    paperCentralCoeff m ℓ = centralDiffCoeff m ℓ + (if ℓ = 0 then 1 else 0) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ; simp
  · rw [paperCentralCoeff_eq_centralDiffCoeff hℓ]; simp [hℓ]

/-- Paper Definition 3.3, literal factorial formula, for `−m ≤ ℓ ≤ m`, `ℓ ≠ 0`:
`a_ℓ^(2m) = (−1)^(ℓ+1) (m!)^2 / (ℓ (m+ℓ)! (m−ℓ)!)`.

This is the equality between the paper's printed factorial formula and the
binomial form used as the definition of `paperCentralCoeff`; it is the
faithfulness bridge for Definition 3.3. The proof uses the rearrangement
`C(m,|ℓ|)/C(m+|ℓ|,|ℓ|) = (m!)^2 / ((m−|ℓ|)! (m+|ℓ|)!)`
(following from `Nat.choose_mul_factorial_mul_factorial`) together with the
sign parity `(−1)^(ℓ+1) = (−1)^(|ℓ|−1)` (the exponents differ by an even
integer). -/
theorem paperCentralCoeff_eq_source_formula (m : ℕ) (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (hmem : ℓ.natAbs ≤ m) :
    paperCentralCoeff m ℓ =
      (-1 : ℝ) ^ (ℓ + 1) * ((m.factorial : ℝ) ^ 2) /
        ((ℓ : ℝ) * (((m : ℤ) + ℓ).toNat.factorial : ℝ) *
          (((m : ℤ) - ℓ).toNat.factorial : ℝ)) := by
  let k := ℓ.natAbs
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkm : k ≤ m := hmem
  have hratio : (Nat.choose m k : ℝ) / (Nat.choose (m + k) k : ℝ) =
      (m.factorial : ℝ) ^ 2 /
        (((m + k).factorial : ℝ) * ((m - k).factorial : ℝ)) := by
    have h₁ : (Nat.choose m k : ℝ) * (k.factorial : ℝ) *
        ((m - k).factorial : ℝ) = (m.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
    have h₂ : (Nat.choose (m + k) k : ℝ) * (k.factorial : ℝ) *
        (m.factorial : ℝ) = ((m + k).factorial : ℝ) := by
      exact_mod_cast (by
        simpa only [Nat.add_sub_cancel_right] using
          Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k m))
    have hC : (Nat.choose (m + k) k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_left k m)).ne'
    have hp : ((m + k).factorial : ℝ) ≠ 0 := by positivity
    have hn : ((m - k).factorial : ℝ) ≠ 0 := by positivity
    apply (div_eq_div_iff hC (mul_ne_zero hp hn)).mpr
    calc
      _ = ((Nat.choose m k : ℝ) * (k.factorial : ℝ) *
          ((m - k).factorial : ℝ)) *
          ((Nat.choose (m + k) k : ℝ) * (m.factorial : ℝ)) := by
        rw [← h₂]
        ring
      _ = _ := by rw [h₁]; ring
  have hsign : (-1 : ℝ) ^ (ℓ + 1) = (-1 : ℝ) ^ (k - 1) := by
    rcases lt_or_gt_of_ne hℓ with hneg | hpos
    · have he : ℓ + 1 = -((k - 1 : ℕ) : ℤ) := by dsimp [k] at *; omega
      rw [he, zpow_neg, zpow_natCast, ← inv_pow]
      norm_num
    · have he : ℓ + 1 = ((k - 1 : ℕ) : ℤ) + 2 := by dsimp [k] at *; omega
      rw [he, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_natCast]
      norm_num
  have hfactorials :
      (((m : ℤ) + ℓ).toNat.factorial : ℝ) *
          (((m : ℤ) - ℓ).toNat.factorial : ℝ) =
        ((m + k).factorial : ℝ) * ((m - k).factorial : ℝ) := by
    rcases lt_or_gt_of_ne hℓ with hneg | hpos
    · have hp : ((m : ℤ) + ℓ).toNat = m - k := by dsimp [k] at *; omega
      have hn : ((m : ℤ) - ℓ).toNat = m + k := by dsimp [k] at *; omega
      rw [hp, hn, mul_comm]
    · have hp : ((m : ℤ) + ℓ).toNat = m + k := by dsimp [k] at *; omega
      have hn : ((m : ℤ) - ℓ).toNat = m - k := by dsimp [k] at *; omega
      rw [hp, hn]
  rw [paperCentralCoeff_eq_centralDiffCoeff hℓ]
  simp only [centralDiffCoeff, hℓ, ite_false]
  change (-1 : ℝ) ^ (k - 1) / (ℓ : ℝ) * (Nat.choose m k : ℝ) /
    (Nat.choose (m + k) k : ℝ) = _
  calc
    _ = ((-1 : ℝ) ^ (k - 1) / (ℓ : ℝ)) *
        ((Nat.choose m k : ℝ) / (Nat.choose (m + k) k : ℝ)) := by ring
    _ = _ := by
      rw [hratio, hsign, mul_assoc (ℓ : ℝ), hfactorials]
      ring

/-- Theorem 3.4, first display (p. 22): for `2 ≤ m` and `k ≤ 2m`,
`Σ_{ℓ=−m}^m a_ℓ^(2m) ℓ^k = 1` if `k ∈ {0,1}` and `0` otherwise.  Proved by
reducing to the Frozen exactness theorem. -/
theorem paperCentralDifferenceExactness (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ 2 * m) :
    (∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1), paperCentralCoeff m ℓ * (ℓ : ℝ) ^ k) =
      if k = 0 ∨ k = 1 then 1 else 0 := by
  have hm0 : 0 < m := by omega
  have hfr := centralDifferenceExactness m hm0 k hk
  have hzero_mem : (0 : ℤ) ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1) := by
    simp only [Finset.mem_Ico]
    omega
  have hdelta :
      (∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
          (if ℓ = 0 then 1 else 0) * (ℓ : ℝ) ^ k) = if k = 0 then 1 else 0 := by
    rw [Finset.sum_eq_single (0 : ℤ)]
    · by_cases hk0 : k = 0
      · simp [hk0]
      · simp [hk0, zero_pow hk0]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hzero_mem h
  calc (∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1), paperCentralCoeff m ℓ * (ℓ : ℝ) ^ k)
      = ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
          (centralDiffCoeff m ℓ + (if ℓ = 0 then 1 else 0)) * (ℓ : ℝ) ^ k := by
        refine Finset.sum_congr rfl ?_
        intro ℓ _
        rw [paperCentralCoeff_eq_add_delta]
    _ = (∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1), centralDiffCoeff m ℓ * (ℓ : ℝ) ^ k)
          + ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
              (if ℓ = 0 then 1 else 0) * (ℓ : ℝ) ^ k := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro ℓ _
        ring
    _ = (if k = 1 then 1 else 0) + (if k = 0 then 1 else 0) := by
        rw [hfr, hdelta]
    _ = if k = 0 ∨ k = 1 then 1 else 0 := by
        by_cases hk0 : k = 0
        · subst hk0; simp
        · by_cases hk1 : k = 1
          · subst hk1; simp
          · simp [hk0, hk1]

/-- Theorem 3.4, second display (p. 22): for `ℓ ∈ {−m,…,m} \ {0}`,
`|a_ℓ^(2m)| < 1/|ℓ|`.

Strictness follows from `choose m |ℓ| < choose (m + |ℓ|) |ℓ|`, using
monotonicity and Pascal's identity. -/
theorem paperCentralCoeff_abs_lt_inv (m : ℕ) (hm : 2 ≤ m) (ℓ : ℤ)
    (hℓmem : ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1)) (hℓ : ℓ ≠ 0) :
    |paperCentralCoeff m ℓ| < 1 / |(ℓ : ℝ)| := by
  let k := ℓ.natAbs
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkm : k ≤ m := by
    have hbounds := Finset.mem_Ico.mp hℓmem
    dsimp [k]
    omega
  have hstep : Nat.choose (m + k - 1) k < Nat.choose (m + k) k := by
    have hp : 0 < Nat.choose (m + k - 1) (k - 1) :=
      Nat.choose_pos (Nat.le_trans (Nat.sub_le k 1)
        (Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_left
          (lt_of_lt_of_le (by decide : 0 < 2) hm))))
    have he : Nat.choose (m + k) k =
        Nat.choose (m + k - 1) (k - 1) + Nat.choose (m + k - 1) k := by
      simpa only [Nat.sub_add_cancel hk,
        Nat.sub_add_cancel (by omega : 1 ≤ m + k)] using
          Nat.choose_succ_succ' (m + k - 1) (k - 1)
    rw [he]
    omega
  have hchoose : Nat.choose m k < Nat.choose (m + k) k :=
    (Nat.choose_le_choose k (by omega : m ≤ m + k - 1)).trans_lt hstep
  have hC : (0 : ℝ) < Nat.choose (m + k) k := by
    exact_mod_cast Nat.choose_pos (hkm.trans (Nat.le_add_right m k))
  have hratio : (Nat.choose m k : ℝ) / (Nat.choose (m + k) k : ℝ) < 1 := by
    apply (div_lt_one hC).mpr
    exact_mod_cast hchoose
  have hℓpos : 0 < |(ℓ : ℝ)| := abs_pos.mpr (by exact_mod_cast hℓ)
  rw [paperCentralCoeff_eq_centralDiffCoeff hℓ]
  simp only [centralDiffCoeff, hℓ, ite_false, abs_div, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, Nat.abs_cast]
  change 1 / |(ℓ : ℝ)| * (Nat.choose m k : ℝ) /
    (Nat.choose (m + k) k : ℝ) < _
  calc
    _ = ((Nat.choose m k : ℝ) / (Nat.choose (m + k) k : ℝ)) /
        |(ℓ : ℝ)| := by ring
    _ < _ := div_lt_div_of_pos_right hratio hℓpos

/-- Theorem 3.4, third display (p. 22): for every integer `k ≥ 2m+1`,
`|Σ_{ℓ=−m}^m a_ℓ^(2m) ℓ^k| ≤ 2 m^k`.

Each of the `2m` nonzero-index summands has magnitude at most `m^(k−1)`;
the zero-index summand vanishes because `k ≥ 1`. -/
theorem paperCentralCoeff_powerSumBound (m k : ℕ) (hm : 2 ≤ m) (hk : 2 * m + 1 ≤ k) :
    |∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1), paperCentralCoeff m ℓ * (ℓ : ℝ) ^ k| ≤
      2 * (m : ℝ) ^ k := by
  have hkpos : 1 ≤ k := by omega
  have hzero : (0 : ℤ) ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1) := by
    simp only [Finset.mem_Ico]
    omega
  have hsum : (∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
      paperCentralCoeff m ℓ * (ℓ : ℝ) ^ k) =
      ∑ ℓ ∈ (Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1)).erase 0,
        paperCentralCoeff m ℓ * (ℓ : ℝ) ^ k := by
    rw [← Finset.sum_erase_add _ _ hzero]
    simp [zero_pow (by omega : k ≠ 0)]
  have hcard : ((Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1)).erase 0).card = 2 * m := by
    rw [Finset.card_erase_of_mem hzero, Int.card_Ico]
    omega
  rw [hsum]
  calc
    _ ≤ ∑ ℓ ∈ (Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1)).erase 0,
        |paperCentralCoeff m ℓ * (ℓ : ℝ) ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ℓ ∈ (Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1)).erase 0,
        (m : ℝ) ^ (k - 1) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hℓ
      have hbound := (paperCentralCoeff_abs_lt_inv m hm ℓ hmem hne).le
      have hℓpos : 0 < |(ℓ : ℝ)| := abs_pos.mpr (by exact_mod_cast hne)
      have hℓle : |(ℓ : ℝ)| ≤ (m : ℝ) := by
        have hbounds := Finset.mem_Ico.mp hmem
        rw [abs_le]
        constructor
        · exact_mod_cast hbounds.1
        · exact_mod_cast (by omega : ℓ ≤ (m : ℤ))
      calc
        _ = |paperCentralCoeff m ℓ| * |(ℓ : ℝ)| ^ k := by rw [abs_mul, abs_pow]
        _ ≤ (1 / |(ℓ : ℝ)|) * |(ℓ : ℝ)| ^ k :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
        _ = |(ℓ : ℝ)| ^ (k - 1) := by
          rw [show |(ℓ : ℝ)| ^ k = |(ℓ : ℝ)| ^ (k - 1) * |(ℓ : ℝ)| by
            rw [← pow_succ, Nat.sub_add_cancel hkpos]]
          field_simp [hℓpos.ne']
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hℓle _
    _ = 2 * (m : ℝ) ^ k := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
        show (m : ℝ) ^ k = (m : ℝ) ^ (k - 1) * (m : ℝ) by
          rw [← pow_succ, Nat.sub_add_cancel hkpos]]
      ring

end Qatlib.Papers.GevreyGrad19.MainResults
