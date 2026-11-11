/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# GroundStPrep17.MainResults.ProjectionCore.CosProjection

The analytic core of Section III of Ge, Tura and Cirac,
*Faster ground state preparation and high-precision ground energy estimation with
fewer qubits*, arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018), pp. 5-6.

For a spectral value `E` with `x = τ + δE` (`τ` the ground energy estimate,
`δE` the spectral shift) the paper evaluates the cosine filter:

* eq. (8): `(cos x - sin x · Δ)/cos x = 1 - tan x · Δ`, where `Δ` plays the
  role of the spectral gap (the paper writes this ratio as the per-filter
  suppression factor);
* eq. (10): the tail factor is at most `exp(-x Δ)`, so at `x_HI ≥ τ`,
  `cos^M x_HI ≤ exp(-M x_HI Δ)` (eqs. (11)-(12));
* eqs. (13)-(15): near the ground state `cos^M τ ≥ exp(-M τ²)`.

All four statements are proved here; they are the only real-analytic inputs of
the ground-state preparation argument (everything else in Section III is
Ledger arithmetic, see `MainResults.SourceModel`).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.ProjectionCore

/-- Eq. (8) of arXiv:1712.03193v2: `(cos x - sin x · Δ) / cos x = 1 - tan x · Δ`
for `cos x ≠ 0`. -/
theorem cos_shift_ratio {x Δ : ℝ} (hcos : Real.cos x ≠ 0) :
    (Real.cos x - Real.sin x * Δ) / Real.cos x = 1 - Real.tan x * Δ := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]

/-- Elementary: `1 - y ≤ exp(-y)`. -/
lemma one_sub_le_exp_neg {y : ℝ} : 1 - y ≤ Real.exp (-y) := by
  have := Real.add_one_le_exp (-y)
  linarith

/-- Powers: if `y ≤ 1` then `(1 - y)^M ≤ exp(-M y)`. -/
theorem pow_one_sub_le_exp {y : ℝ} (hy : y ≤ 1) (M : ℕ) :
    (1 - y) ^ M ≤ Real.exp (-(M * y)) := by
  have hy0 : 0 ≤ 1 - y := by linarith
  have hbase : 1 - y ≤ Real.exp (-y) := one_sub_le_exp_neg
  have hpow : (1 - y) ^ M ≤ Real.exp (-y) ^ M := pow_le_pow_left₀ hy0 hbase M
  have harg : (M : ℝ) * -y = -(M * y) := by ring
  calc (1 - y) ^ M ≤ Real.exp (-y) ^ M := hpow
    _ = Real.exp ((M : ℝ) * -y) := by rw [Real.exp_nat_mul]
    _ = Real.exp (-(M * y)) := by rw [harg]

/-- Eq. (10) of the paper: at `x ≤ 1` the suppressed cosine ratio is at most
`exp(-x Δ)`.  Here `x ∈ [0,1]` ensures `0 ≤ tan x` and `x ≤ tan x`. -/
theorem cos_shift_ratio_le_exp {x Δ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hΔ : 0 < Δ)
    (hcos : Real.cos x ≠ 0) :
    (Real.cos x - Real.sin x * Δ) / Real.cos x ≤ Real.exp (-(x * Δ)) := by
  rw [cos_shift_ratio hcos]
  have hπ : x < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have htan_ge : x ≤ Real.tan x := Real.le_tan hx0 hπ
  have h1 : 1 - Real.tan x * Δ ≤ Real.exp (-(Real.tan x * Δ)) := one_sub_le_exp_neg
  have h2 : Real.exp (-(Real.tan x * Δ)) ≤ Real.exp (-(x * Δ)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right htan_ge (le_of_lt hΔ)
    linarith
  linarith

/-- For `0 ≤ y ≤ 1/2`, `log(1 - y) ≥ -2y`. -/
lemma log_one_sub_ge_neg_two_mul {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    -2 * y ≤ Real.log (1 - y) := by
  have h1 : 0 < 1 - y := by linarith
  have hlog : Real.log (1 - y) = -Real.log (1 / (1 - y)) := by
    rw [one_div, Real.log_inv]
    ring
  rw [hlog]
  have hpos : 0 < 1 / (1 - y) := by positivity
  have hle : Real.log (1 / (1 - y)) ≤ 1 / (1 - y) - 1 :=
    Real.log_le_sub_one_of_pos hpos
  have hfrac : 1 / (1 - y) - 1 = y / (1 - y) := by
    field_simp [h1.ne']
    ring
  have hdiv : y / (1 - y) ≤ 2 * y := by
    rw [div_le_iff₀ h1]
    have : 0 ≤ y * (1 - 2 * y) := mul_nonneg hy0 (by linarith)
    nlinarith
  linarith

/-- Eq. (13)-(15) of the paper: for `x ≤ 1`, `cos^M x ≥ exp(-M x²)`.
Proof: `cos x ≥ 1 - x²/2`, and `log(1 - y) ≥ -2y` at `y = x²/2`. -/
theorem exp_neg_sq_le_cos_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (M : ℕ) :
    Real.exp (-(M * x ^ 2)) ≤ Real.cos x ^ M := by
  set y : ℝ := x ^ 2 / 2 with hy_def
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 / 2 := by
    rw [hy_def]
    nlinarith [sq_nonneg x, hx0, hx1, mul_nonneg hx0 (by linarith : (0:ℝ) ≤ 1 - x)]
  have hbase_pos : 0 < 1 - y := by linarith
  have hcos_ge : 1 - y ≤ Real.cos x := by
    have h := Real.one_sub_sq_div_two_le_cos (x := x)
    rw [hy_def]
    exact h
  have hlogy : -2 * y ≤ Real.log (1 - y) := log_one_sub_ge_neg_two_mul hy0 hy1
  have h2y : 2 * y = x ^ 2 := by
    rw [hy_def]
    ring
  have hexp_le : Real.exp (-(M * x ^ 2)) ≤ Real.exp ((M : ℝ) * Real.log (1 - y)) := by
    apply Real.exp_le_exp.mpr
    have hcast : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hmul : (M : ℝ) * (-2 * y) ≤ M * Real.log (1 - y) :=
      mul_le_mul_of_nonneg_left hlogy hcast
    have hneg : (M : ℝ) * (-2 * y) = -(M * x ^ 2) := by
      have h2 : -2 * y = -(x ^ 2) := by
        rw [show -2 * y = -(2 * y) by ring, h2y]
      rw [h2]
      ring
    linarith
  have hpow : Real.exp ((M : ℝ) * Real.log (1 - y)) = (1 - y) ^ M := by
    rw [Real.exp_nat_mul, Real.exp_log hbase_pos]
  have hcos_pow : (1 - y) ^ M ≤ Real.cos x ^ M :=
    pow_le_pow_left₀ (le_of_lt hbase_pos) hcos_ge M
  calc Real.exp (-(M * x ^ 2)) ≤ Real.exp ((M : ℝ) * Real.log (1 - y)) := hexp_le
    _ = (1 - y) ^ M := hpow
    _ ≤ Real.cos x ^ M := hcos_pow

/-- Eq. (11)-(12) of the paper: the filter tail at `x` satisfies
`(1 - tan x · Δ)^M ≤ exp(-M x Δ)` for `0 ≤ x ≤ 1` and `tan x · Δ ≤ 1`. -/
theorem cos_pow_residual_le_exp {x Δ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hΔ : 0 < Δ)
    (htan : Real.tan x * Δ ≤ 1) (M : ℕ) :
    (1 - Real.tan x * Δ) ^ M ≤ Real.exp (-(M * x * Δ)) := by
  have hbase : (1 - Real.tan x * Δ) ^ M
      ≤ Real.exp (-((M : ℝ) * (Real.tan x * Δ))) :=
    pow_one_sub_le_exp htan M
  have hexp_le : Real.exp (-((M : ℝ) * (Real.tan x * Δ)))
      ≤ Real.exp (-(M * x * Δ)) := by
    apply Real.exp_le_exp.mpr
    have hπ : x < Real.pi / 2 := by linarith [Real.pi_gt_three]
    have htan_ge : x ≤ Real.tan x := Real.le_tan hx0 hπ
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hmul : (M : ℝ) * x * Δ ≤ M * Real.tan x * Δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htan_ge hM0) (le_of_lt hΔ)
    linarith
  linarith [hbase, hexp_le]

end Qatlib.Papers.GroundStPrep17.MainResults.ProjectionCore
