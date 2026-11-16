/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Angular separation and the scalar fast-OR cost expression

The angular separation is a real-analysis input to the fast-OR construction of
arXiv:1710.02581. Its proof uses the one-Lipschitz cosine function. The cost theorem
below bounds the explicitly defined scalar expression; it does not construct a
controlled reflection, phase-estimation circuit, or executable query-cost model.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QSDPSolvers17.MainResults.FastOrGap

/-- The two square-root acceptance thresholds are separated by at least the stated angular gap. -/
theorem arccos_gap_lower {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    (1 : ℝ) / (20 * Real.sqrt m) ≤
      Real.arccos (Real.sqrt (0.8 * ((1 - ε) / (2 * m)))) -
        Real.arccos (Real.sqrt ((1 - ε) / (2 * m))) := by
  let lam : ℝ := (1 - ε) / (2 * m)
  change (1 : ℝ) / (20 * Real.sqrt m) ≤
    Real.arccos (Real.sqrt (0.8 * lam)) - Real.arccos (Real.sqrt lam)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hm
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hlam : 0 ≤ lam := by
    dsimp [lam]
    exact div_nonneg (by linarith) (by positivity)
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))]
    nlinarith
  have hsq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam
  have hroot0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have hroot1 : Real.sqrt lam ≤ 1 :=
    (sq_le_sq₀ hroot0 zero_le_one).mp (by simpa [hsq] using hlam1)
  have hsmall0 : 0 ≤ Real.sqrt (0.8 * lam) := Real.sqrt_nonneg _
  have hsmallsq : Real.sqrt (0.8 * lam) ^ 2 = 0.8 * lam :=
    Real.sq_sqrt (by positivity)
  have hshrink : Real.sqrt (0.8 * lam) ≤ (9 / 10 : ℝ) * Real.sqrt lam := by
    apply (sq_le_sq₀ hsmall0 (by positivity : 0 ≤ (9 / 10 : ℝ) * Real.sqrt lam)).mp
    rw [hsmallsq, mul_pow, hsq]
    nlinarith
  have hsmall : Real.sqrt (0.8 * lam) ≤ Real.sqrt lam := by linarith
  have hsmall1 : Real.sqrt (0.8 * lam) ≤ 1 := hsmall.trans hroot1
  have hangle : 0 ≤ Real.arccos (Real.sqrt (0.8 * lam)) - Real.arccos (Real.sqrt lam) :=
    sub_nonneg.mpr (Real.arccos_le_arccos hsmall)
  have hcos := Real.abs_cos_sub_cos_le
    (Real.arccos (Real.sqrt (0.8 * lam))) (Real.arccos (Real.sqrt lam))
  rw [Real.cos_arccos (by linarith : -1 ≤ Real.sqrt (0.8 * lam)) hsmall1,
    Real.cos_arccos (by linarith : -1 ≤ Real.sqrt lam) hroot1,
    abs_of_nonpos (sub_nonpos.mpr hsmall), abs_of_nonneg hangle] at hcos
  have hratio : lam * (2 * (m : ℝ)) = 1 - ε := by
    dsimp [lam]
    exact div_mul_cancel₀ _ (by positivity)
  have hprodSq : (2 * Real.sqrt (m : ℝ) * Real.sqrt lam) ^ 2 = 2 * (1 - ε) := by
    calc (2 * Real.sqrt (m : ℝ) * Real.sqrt lam) ^ 2
        = 4 * Real.sqrt (m : ℝ) ^ 2 * Real.sqrt lam ^ 2 := by ring
      _ = 4 * (m : ℝ) * lam := by rw [Real.sq_sqrt hmR.le, hsq]
      _ = 2 * (1 - ε) := by nlinarith
  have hprod0 : 0 ≤ 2 * Real.sqrt (m : ℝ) * Real.sqrt lam := by positivity
  have hprod : 1 ≤ 2 * Real.sqrt (m : ℝ) * Real.sqrt lam := by
    apply (sq_le_sq₀ zero_le_one hprod0).mp
    rw [hprodSq]
    nlinarith
  have hrootLower : (1 : ℝ) / (2 * Real.sqrt (m : ℝ)) ≤ Real.sqrt lam := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt (m : ℝ))]
    nlinarith
  calc (1 : ℝ) / (20 * Real.sqrt m)
      = (1 / 10 : ℝ) * (1 / (2 * Real.sqrt (m : ℝ))) := by
        field_simp [hsqrtm.ne']
        ring
    _ ≤ (1 / 10 : ℝ) * Real.sqrt lam :=
      mul_le_mul_of_nonneg_left hrootLower (by norm_num)
    _ ≤ Real.sqrt lam - Real.sqrt (0.8 * lam) := by linarith
    _ ≤ Real.arccos (Real.sqrt (0.8 * lam)) - Real.arccos (Real.sqrt lam) := by linarith

/-- The explicit reciprocal-gap scalar expression used in the fast-OR operation estimate. -/
def fastOrOperations (lam ξ p : ℝ) (m : ℕ) : ℝ :=
  (1 / ξ) * (1 / (Real.arccos (Real.sqrt (0.8 * lam)) - Real.arccos (Real.sqrt lam))) *
    (p + (Real.log m + 1) ^ 2)

/-- The scalar reciprocal-gap expression is bounded with the explicit constant twenty. -/
theorem fast_or_operations_bound {m : ℕ} (hm : 0 < m) {ε ξ p : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hξ : 0 < ξ) (hp : 0 ≤ p) :
    fastOrOperations ((1 - ε) / (2 * m)) ξ p m ≤
      20 * ξ⁻¹ * Real.sqrt m * (p + (Real.log m + 1) ^ 2) := by
  unfold fastOrOperations
  have hgap := arccos_gap_lower hm hε0 hε1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hpos : 0 < 1 / (20 * Real.sqrt (m : ℝ)) := by positivity
  have hinv : 1 / (Real.arccos (Real.sqrt (0.8 * ((1 - ε) / (2 * m)))) -
      Real.arccos (Real.sqrt ((1 - ε) / (2 * m)))) ≤ 20 * Real.sqrt m := by
    have h := one_div_le_one_div_of_le hpos hgap
    simpa only [one_div_one_div] using h
  have hfac : 0 ≤ p + (Real.log m + 1) ^ 2 := by positivity
  have hξinv : 0 ≤ 1 / ξ := by positivity
  calc (1 / ξ) * (1 / (Real.arccos (Real.sqrt (0.8 * ((1 - ε) / (2 * m)))) -
          Real.arccos (Real.sqrt ((1 - ε) / (2 * m))))) * (p + (Real.log m + 1) ^ 2)
      ≤ (1 / ξ) * (20 * Real.sqrt m) * (p + (Real.log m + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hξinv) hfac
    _ = 20 * ξ⁻¹ * Real.sqrt m * (p + (Real.log m + 1) ^ 2) := by ring

end Qatlib.Papers.QSDPSolvers17.MainResults.FastOrGap
