/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrotterSuzuki14.MainResults.CisdPreparation.Defs
import Mathlib.Tactic

/-!
# CISD preparation resource bounds

This module bounds the rounded precision exponent `cisdExponent` and the resource ledger
`cisdReductionTCount`. Under the stated dimension and precision hypotheses, the ledger is
bounded by a universal positive constant times `D log₂(D / δ) + N D`. See [BabbushEtAl2015].

## Main statements

* `cisdExponent_le`: Explicit logarithmic upper bound on the rounded exponent.
* `cisd_ledger_bound`: Uniform bound on the CISD reduction T-count ledger.

## References

* [Babbush et al., 2015][BabbushEtAl2015]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TrotterSuzuki14.MainResults

/-- For `D ≥ 1` and `0 < δ ≤ 1`, the rounded CISD exponent is at most `11/4 + (1/2) log₂(D /
δ)`. See [BabbushEtAl2015]. -/
theorem cisdExponent_le (D : ℕ) (δ : ℝ) (hD : 1 ≤ D) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (cisdExponent D δ : ℝ) ≤ 11 / 4 + (1 / 2) * Real.logb 2 ((D : ℝ) / δ) := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith

  have hs_ge : δ / 4 ≤ Real.sqrt (1 + δ) - 1 := by
    have hsqrt : 1 + δ / 4 ≤ Real.sqrt (1 + δ) := by
      apply Real.le_sqrt_of_sq_le
      have hδ8 : δ ≤ 8 := by linarith
      nlinarith [mul_nonneg (le_of_lt hδ) (sub_nonneg.mpr hδ8)]
    linarith
  have hs_sq : (δ / 4) ^ 2 ≤ (Real.sqrt (1 + δ) - 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ δ / 4) hs_ge 2
  have hden_pos : (0 : ℝ) < (Real.sqrt (1 + δ) - 1) ^ 2 := by
    have hpos : (0 : ℝ) < δ / 4 := by linarith
    nlinarith [sq_pos_of_pos hpos]

  have hnum_nonneg : (0 : ℝ) ≤ (D : ℝ) + 2 := by linarith
  have hratio : ((D : ℝ) + 2) / (Real.sqrt (1 + δ) - 1) ^ 2
      ≤ 16 * ((D : ℝ) + 2) / δ ^ 2 := by
    have hmain := div_le_div_of_nonneg_left hnum_nonneg
      (by positivity : (0 : ℝ) < (δ / 4) ^ 2) hs_sq
    calc ((D : ℝ) + 2) / (Real.sqrt (1 + δ) - 1) ^ 2
        ≤ ((D : ℝ) + 2) / (δ / 4) ^ 2 := hmain
      _ = 16 * ((D : ℝ) + 2) / δ ^ 2 := by field_simp; ring
  have harg_pos : (0 : ℝ) < ((D : ℝ) + 2) / (Real.sqrt (1 + δ) - 1) ^ 2 :=
    div_pos (by linarith) hden_pos
  have hlogmono : Real.logb 2 (((D : ℝ) + 2) / (Real.sqrt (1 + δ) - 1) ^ 2)
      ≤ Real.logb 2 (16 * ((D : ℝ) + 2) / δ ^ 2) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) harg_pos hratio

  have hlog16 : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (b := 2) (by norm_num)]
    norm_num
  have hlogsplit : Real.logb 2 (16 * ((D : ℝ) + 2) / δ ^ 2)
      = 4 + Real.logb 2 ((D : ℝ) + 2) - 2 * Real.logb 2 δ := by
    rw [show 16 * ((D : ℝ) + 2) / δ ^ 2 = 16 * (((D : ℝ) + 2) / δ ^ 2) by ring]
    rw [Real.logb_mul (by norm_num) (by positivity)]
    rw [Real.logb_div (by positivity) (by positivity)]
    rw [Real.logb_pow]
    rw [hlog16]
    ring
  have hlog3 : Real.logb 2 (3 : ℝ) ≤ 2 := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
    have h4 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (b := 2) (by norm_num)]
      ring
    linarith
  have hneglog : -2 * Real.logb 2 δ = 2 * Real.logb 2 (1 / δ) := by
    rw [one_div, Real.logb_inv]
    ring
  have hL_nonneg : 0 ≤ Real.logb 2 ((D : ℝ) / δ) := by
    apply Real.logb_nonneg (b := 2) (by norm_num)
    rw [le_div_iff₀ hδ]
    nlinarith
  have hLsplit : Real.logb 2 ((D : ℝ) / δ)
      = Real.logb 2 (D : ℝ) + Real.logb 2 (1 / δ) := by
    rw [div_eq_mul_inv, Real.logb_mul (ne_of_gt hDpos) (by positivity), one_div]

  have hlogarg : Real.logb 2 (((D : ℝ) + 2) / (Real.sqrt (1 + δ) - 1) ^ 2)
      ≤ 6 + 2 * Real.logb 2 ((D : ℝ) / δ) := by
    have hlogD : Real.logb 2 ((D : ℝ) + 2) ≤ 2 + Real.logb 2 (D : ℝ) := by
      have hle : ((D : ℝ) + 2) ≤ 3 * (D : ℝ) := by nlinarith
      have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num)
        (by positivity : (0 : ℝ) < (D : ℝ) + 2) hle
      rw [Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hDpos)] at hmono
      linarith
    have hlogDnonneg : 0 ≤ Real.logb 2 (D : ℝ) := by
      apply Real.logb_nonneg (b := 2) (by norm_num)
      exact hD1
    have hlogInv_nonneg : 0 ≤ Real.logb 2 (1 / δ) := by
      apply Real.logb_nonneg (b := 2) (by norm_num)
      rw [le_div_iff₀ hδ]
      linarith
    calc Real.logb 2 (((D : ℝ) + 2) / (Real.sqrt (1 + δ) - 1) ^ 2)
        ≤ Real.logb 2 (16 * ((D : ℝ) + 2) / δ ^ 2) := hlogmono
      _ = 4 + Real.logb 2 ((D : ℝ) + 2) - 2 * Real.logb 2 δ := hlogsplit
      _ = 4 + Real.logb 2 ((D : ℝ) + 2) + 2 * Real.logb 2 (1 / δ) := by
          rw [← hneglog]; ring
      _ ≤ 4 + (2 + Real.logb 2 (D : ℝ)) + 2 * Real.logb 2 (1 / δ) := by linarith
      _ ≤ 6 + 2 * Real.logb 2 ((D : ℝ) / δ) := by
          rw [hLsplit]; linarith

  have hk_real : cisdExponentReal D δ ≤ 7 / 4 + (1 / 2) * Real.logb 2 ((D : ℝ) / δ) := by
    unfold cisdExponentReal
    nlinarith [hlogarg]

  have hnonneg_real : 0 ≤ cisdExponentReal D δ := by
    unfold cisdExponentReal
    apply mul_nonneg (by norm_num)
    have hlog_nonneg : 0 ≤ Real.logb 2 (((D : ℝ) + 2) / (Real.sqrt (1 + δ) - 1) ^ 2) := by
      apply Real.logb_nonneg (b := 2) (by norm_num)
      rw [le_div_iff₀ hden_pos]
      have hs_le_two : Real.sqrt (1 + δ) ≤ 2 := by
        calc Real.sqrt (1 + δ) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
          _ = 2 := by norm_num
      have hs_nonneg : 0 ≤ Real.sqrt (1 + δ) - 1 := le_trans (by linarith) hs_ge
      nlinarith [sq_nonneg (Real.sqrt (1 + δ) - 1), hD1]
    linarith
  have hceil := Nat.ceil_lt_add_one hnonneg_real
  unfold cisdExponent
  linarith

/-- There is a universal positive constant bounding `cisdReductionTCount` by that constant times
`D log₂(D / δ) + N D` whenever `D ≥ 1`, `N ≥ 5`, and `0 < δ ≤ 1`. See [BabbushEtAl2015]. -/
theorem cisd_ledger_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D N : ℕ) (δ : ℝ),
        1 ≤ D → 5 ≤ N → 0 < δ → δ ≤ 1 →
        cisdReductionTCount D N δ ≤
          C * ((D : ℝ) * Real.logb 2 ((D : ℝ) / δ) + (N : ℝ) * (D : ℝ)) := by
  refine ⟨200, by norm_num, ?_⟩
  intro D N δ hD hN hδ hδ1
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := by linarith
  have hN5 : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hL_nonneg : 0 ≤ Real.logb 2 ((D : ℝ) / δ) := by
    apply Real.logb_nonneg (b := 2) (by norm_num)
    rw [le_div_iff₀ hδ]
    nlinarith
  have hk := cisdExponent_le D δ hD hδ hδ1
  have hk_nonneg : (0 : ℝ) ≤ (cisdExponent D δ : ℝ) := Nat.cast_nonneg _

  have hstep1 : 22 * (cisdExponent D δ : ℝ) + 64 * ((N : ℝ) - 3)
      ≤ 22 * (11 / 4 + (1 / 2) * Real.logb 2 ((D : ℝ) / δ)) + 64 * (N : ℝ) := by
    nlinarith
  have hstep2 : (22 * (cisdExponent D δ : ℝ) + 64 * ((N : ℝ) - 3)) * ((D : ℝ) + 1)
      ≤ (22 * (11 / 4 + (1 / 2) * Real.logb 2 ((D : ℝ) / δ)) + 64 * (N : ℝ))
          * (2 * (D : ℝ)) := by
    have hinner_nonneg : 0 ≤ 22 * (11 / 4 + (1 / 2) * Real.logb 2 ((D : ℝ) / δ))
        + 64 * (N : ℝ) := by nlinarith
    have hDadd : (D : ℝ) + 1 ≤ 2 * (D : ℝ) := by linarith
    calc (22 * (cisdExponent D δ : ℝ) + 64 * ((N : ℝ) - 3)) * ((D : ℝ) + 1)
        ≤ (22 * (11 / 4 + (1 / 2) * Real.logb 2 ((D : ℝ) / δ)) + 64 * (N : ℝ))
            * ((D : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_right hstep1 (by linarith)
      _ ≤ (22 * (11 / 4 + (1 / 2) * Real.logb 2 ((D : ℝ) / δ)) + 64 * (N : ℝ))
            * (2 * (D : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hDadd hinner_nonneg
  unfold cisdReductionTCount
  refine le_trans hstep2 ?_

  have hLprod : 0 ≤ Real.logb 2 ((D : ℝ) / δ) * (D : ℝ) := mul_nonneg hL_nonneg hD0
  have hNprod : 0 ≤ (N : ℝ) * (D : ℝ) := mul_nonneg hN0 hD0
  nlinarith [hLprod, hNprod, hN5, hD0]

end Qatlib.Papers.TrotterSuzuki14.MainResults
