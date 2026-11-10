/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CBMD

open Complex Metric Set
open scoped BigOperators NNReal ENNReal

noncomputable def cauchyCoefficient (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  (cauchyPowerSeries f c R).coeff n

theorem cauchyCoefficient_hasSum
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R))
    (u : ℂ) (hu : ‖u‖ < R) :
    HasSum (fun n : ℕ => cauchyCoefficient f c R n * u ^ n) (f (c + u)) := by
  let R' : ℝ≥0 := ⟨R, hR.le⟩
  have hp := hf.hasFPowerSeriesOnBall (R := R') (by exact hR)
  have hu' : u ∈ Metric.eball (0 : ℂ) (R' : ℝ≥0∞) := by
    simpa only [mem_eball_zero_iff, enorm_lt_coe, NNReal.coe_mk, R'] using! hu
  have h := hp.hasSum hu'
  convert! h using 1
  funext n
  simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul,
    cauchyCoefficient, R']
  exact mul_comm _ _

theorem cauchyCoefficient_norm_le
    (f : ℂ → ℂ) (c : ℂ) (R M : ℝ) (hR : 0 < R)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖cauchyCoefficient f c R n‖ ≤ M * R⁻¹ ^ n := by
  rw [cauchyCoefficient, ← FormalMultilinearSeries.norm_apply_eq_norm_coef]
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.norm_mkPiRing]
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (c := c) hR.le
    (f := fun z => (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z)
    (C := R⁻¹ ^ n * R⁻¹ * M) (fun z hz => ?_)
  · calc
      _ ≤ R * (R⁻¹ ^ n * R⁻¹ * M) := h
      _ = M * R⁻¹ ^ n := by field_simp [hR.ne']
  · have hzR : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
    simp only [norm_smul, norm_pow, norm_inv, hzR]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound z hz)
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) n) (inv_nonneg.mpr hR.le))

theorem cauchyCoefficient_weighted_sum_le
    (f : ℂ → ℂ) (c : ℂ) (R r M : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hrR : r < R)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    Summable (fun n : ℕ => ‖cauchyCoefficient f c R n‖ * r ^ n) ∧
      (∑' n : ℕ, ‖cauchyCoefficient f c R n‖ * r ^ n) ≤ M / (1 - r / R) := by
  have hq0 : 0 ≤ r / R := div_nonneg hr0 hR.le
  have hq1 : r / R < 1 := (div_lt_one hR).mpr hrR
  have hgeom := (summable_geometric_of_lt_one hq0 hq1).mul_left M
  have hterm (n : ℕ) : ‖cauchyCoefficient f c R n‖ * r ^ n ≤ M * (r / R) ^ n := by
    calc
      ‖cauchyCoefficient f c R n‖ * r ^ n ≤ (M * R⁻¹ ^ n) * r ^ n :=
        mul_le_mul_of_nonneg_right (cauchyCoefficient_norm_le f c R M hR hbound n)
          (pow_nonneg hr0 n)
      _ = M * (r / R) ^ n := by rw [div_eq_mul_inv, mul_pow]; ring
  have hsum := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n)) hterm hgeom
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, M * (r / R) ^ n := hsum.tsum_le_tsum hterm hgeom
    _ = M / (1 - r / R) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      exact (div_eq_mul_inv M (1 - r / R)).symm

theorem cbmd_cauchy_coefficient_budget
    (f : ℂ → ℂ) (g M : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1 / 2)
    (hbound : ∀ z ∈ sphere (((1 + g) / 2 : ℝ) : ℂ) (1 / 2), ‖f z‖ ≤ M) :
    let r := (1 - g) / 2 + g / 4
    Summable (fun n : ℕ => ‖cauchyCoefficient f (((1 + g) / 2 : ℝ) : ℂ) (1 / 2) n‖ * r ^ n) ∧
      (∑' n : ℕ, ‖cauchyCoefficient f (((1 + g) / 2 : ℝ) : ℂ) (1 / 2) n‖ * r ^ n) ≤
        (2 / g) * M := by
  (try dsimp only)
  obtain ⟨hsum, hboundSum⟩ := cauchyCoefficient_weighted_sum_le f
    (((1 + g) / 2 : ℝ) : ℂ) (1 / 2) ((1 - g) / 2 + g / 4) M
    (by norm_num) (by linarith) (by linarith) hbound
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ M / (1 - ((1 - g) / 2 + g / 4) / (1 / 2)) := hboundSum
    _ = (2 / g) * M := by
      have hid : 1 - ((1 - g) / 2 + g / 4) / (1 / 2) = g / 2 := by ring
      rw [hid]
      field_simp

end CBMD

end Qatlib.Papers.Cbmd26.Algorithms
