/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # Preserved large-D scalar arithmetic
The remainder inequality is an explicit numerical hypothesis. This does not
prove existence of an odd cutoff or the QAOA expectation bound.
-/
set_option autoImplicit false
namespace Qatlib.Papers.QAOABddOcc14.MainResults

/-- **Source (43): the large-`D` numeric step.**  With `k ≥ 1` odd and
`k ≤ 5 ln D` — i.e. the paper's "run at no more than `5 ln D` values of `γ`" —
and the explicit "large `D`" side condition that the exponentially small
remainder `(9/10)^{k+2}` is below `1/(10100 √D ln D)`, the bound (42) dominates
`m/(101√D ln D)`.

The side condition is exactly the paper's "for large `D`" (p. 8, under (43)): it
holds for the largest odd `k = 5 ln D + O(1)`, since `(9/10)^{k+2} ≤ D^{5 ln(0.9)}
· (9/10)` with `5 ln(0.9) ≈ −0.527`, which beats `1/(10100 √D ln D)` for all `D`
beyond an explicit finite threshold. -/
theorem largeD_numeric (m D : ℝ) (hm : 0 < m) (hD : 1 < D) (k : ℕ)
    (hk1 : 1 ≤ k) (hk_le : (k : ℝ) ≤ 5 * Real.log D)
    (hnum : (9 / 10) ^ (k + 2) ≤ 1 / (10100 * Real.sqrt D * Real.log D)) :
    m / (20 * Real.sqrt D * (k : ℝ)) - m * (9 / 10) ^ (k + 2) ≥
      m / (101 * Real.sqrt D * Real.log D) := by
  have hDpos : (0 : ℝ) < D := by linarith
  have hspos : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr hDpos
  have hlogpos : (0 : ℝ) < Real.log D := Real.log_pos hD
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hden20 : (0 : ℝ) < 20 * Real.sqrt D * (k : ℝ) := by positivity
  have hden100 : (0 : ℝ) < 100 * Real.sqrt D * Real.log D := by positivity
  have hstep1 : m / (100 * Real.sqrt D * Real.log D) ≤
      m / (20 * Real.sqrt D * (k : ℝ)) := by
    have hb : 20 * Real.sqrt D * (k : ℝ) ≤ 100 * Real.sqrt D * Real.log D := by
      nlinarith [hk_le, hspos]
    exact div_le_div_of_nonneg_left (le_of_lt hm) hden20 hb
  have hnum' : m * (9 / 10) ^ (k + 2) ≤ m * (1 / (10100 * Real.sqrt D * Real.log D)) :=
    mul_le_mul_of_nonneg_left hnum (le_of_lt hm)
  have hsplit : m / (100 * Real.sqrt D * Real.log D) - m / (101 * Real.sqrt D * Real.log D)
      = m * (1 / (10100 * Real.sqrt D * Real.log D)) := by
    have hs : Real.sqrt D ≠ 0 := ne_of_gt hspos
    have hl : Real.log D ≠ 0 := ne_of_gt hlogpos
    field_simp [hs, hl]
    ring
  linarith [hstep1, hnum', hsplit]

end Qatlib.Papers.QAOABddOcc14.MainResults
