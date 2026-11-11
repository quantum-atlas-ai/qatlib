/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceTaylor
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Globally convergent analytic ray series

This module bounds Taylor coefficients with derivative growth `A^n * n^(n/2)` and proves
convergence at every real argument. These scalar estimates support analytic central-difference
error bounds in the gradient framework of [GilyenArunachalamWiebe2019].

## Main statements

* `centralDiff_growth_summable`: the growth majorant is summable at every real argument.
* `centralDiff_scalar_entire_hasSum`: the Taylor series at zero sums to the analytic function.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators Topology NNReal ENNReal
open Filter

/-- For nonnegative `A` and positive degree `n`, bounds `A^n * n^(n/2) / n!` by `(exp 1 * A /
sqrt n)^n`. -/
theorem centralDiff_growth_coefficient_le (A : ℝ) (hA : 0≤A) (n : ℕ) (hn : 0<n) :
    A^n*(n : ℝ)^((n : ℝ)/2)/(Nat.factorial n : ℝ)≤(Real.exp 1*A/Real.sqrt n)^n := by
  have hnr : (0 : ℝ)<n := by exact_mod_cast hn
  have he : (0 : ℝ)<Real.exp 1 := Real.exp_pos _
  have hs := Stirling.le_factorial_stirling n
  have hsqrt : 1≤Real.sqrt (2*Real.pi*n) := by
    have hπ := Real.pi_gt_three
    have hnn : (1 : ℝ)≤n := by exact_mod_cast hn
    have hp : (1 : ℝ)^2≤2*Real.pi*n := by nlinarith
    have h := Real.sqrt_le_sqrt hp
    simpa using! h
  have hbase : 0<(n : ℝ)/Real.exp 1 := div_pos hnr he
  have hf0 : ((n : ℝ)/Real.exp 1)^n≤Real.sqrt (2*Real.pi*n)*((n : ℝ)/Real.exp 1)^n := by
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right hsqrt (pow_nonneg hbase.le n)
  have hf : ((n : ℝ)/Real.exp 1)^n≤(Nat.factorial n : ℝ) := hf0.trans hs
  have hp : (n : ℝ)^((n : ℝ)/2)=(Real.sqrt n)^n := by
    rw [show (n : ℝ)/2=(1/2 : ℝ)*(n : ℝ) by ring,
      Real.rpow_mul hnr.le,Real.rpow_natCast,← Real.sqrt_eq_rpow]
  have h := div_le_div_of_nonneg_left (by positivity : 0≤A^n*(n : ℝ)^((n : ℝ)/2))
    (pow_pos hbase n) hf
  rw [hp] at h ⊢
  apply h.trans_eq
  rw [← mul_pow,← div_pow]
  congr 1
  have hsq : (Real.sqrt n)^2=(n : ℝ) := Real.sq_sqrt hnr.le
  field_simp
  nlinarith

/-- For nonnegative `A`, the factorially scaled growth majorant `A^n * n^(n/2) * |t|^n / n!` is
summable at every real `t`. -/
theorem centralDiff_growth_summable (A t : ℝ) (hA : 0≤A) :
    Summable (fun n : ℕ => A^n*(n : ℝ)^((n : ℝ)/2)/(Nat.factorial n : ℝ)*|t|^n) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ((2*Real.exp 1*A*|t|)^2)
  have hg : Summable (fun n : ℕ => (1/2 : ℝ)^n) := summable_geometric_of_norm_lt_one (by norm_num)
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [eventually_atTop.2 ⟨max N 1,fun n hn => hn⟩] with n hn
  have hnp : 0<n := by omega
  have hnr : (0 : ℝ)<n := by exact_mod_cast hnp
  have hns : (2*Real.exp 1*A*|t|)^2≤(n : ℝ) := hN.trans (by exact_mod_cast (by omega : N≤n))
  have hs : 2*Real.exp 1*A*|t|≤Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hns
    rw [Real.sqrt_sq (by positivity : 0≤2*Real.exp 1*A*|t|)] at h
    exact h
  have hspos : 0<Real.sqrt n := Real.sqrt_pos.mpr hnr
  have hb : Real.exp 1*A*|t|/Real.sqrt n≤1/2 := (div_le_iff₀ hspos).mpr (by linarith)
  have hcoeff :=
      mul_le_mul_of_nonneg_right (centralDiff_growth_coefficient_le A hA n hnp)
      (pow_nonneg (abs_nonneg t) n)
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ _ := hcoeff
    _ = (Real.exp 1*A*|t|/Real.sqrt n)^n := by rw [← mul_pow]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hb n

/-- A real function analytic near every real point, with derivatives at zero bounded by `A^n *
n^(n/2)`, equals its Taylor series at zero at every real argument. -/
theorem centralDiff_scalar_entire_hasSum (g : ℝ → ℝ)
    (hg : AnalyticOnNhd ℝ g Set.univ) (A : ℝ) (hA : 0≤A)
    (hb : ∀ n : ℕ,|iteratedDeriv n g 0|≤A^n*(n : ℝ)^((n : ℝ)/2)) (t : ℝ) :
    HasSum (fun n : ℕ => iteratedDeriv n g 0/(Nat.factorial n : ℝ)*t^n) (g t) := by
  let a := fun n : ℕ => iteratedDeriv n g 0/(Nat.factorial n : ℝ)
  let p := FormalMultilinearSeries.ofScalars ℝ a
  have hs (r : ℝ≥0) : Summable (fun n : ℕ => ‖p n‖*(r : ℝ)^n) := by
    have h := centralDiff_growth_summable A (r : ℝ) hA
    apply Summable.of_nonneg_of_le (fun n => by positivity) _
        (by simpa only [abs_of_nonneg r.2] using! h)
    intro n
    rw [FormalMultilinearSeries.ofScalars_norm]
    simp only [a,Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg (Nat.factorial n) : (0 : ℝ)≤Nat.factorial n)]
    simpa only [abs_of_nonneg (show (0 : ℝ)≤(r : ℝ) from r.2)] using!
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hb n) (Nat.cast_nonneg (Nat.factorial n))) (pow_nonneg r.2 n)
  have hp : p.radius=∞ := p.radius_eq_top_of_summable_norm hs
  have hseries : AnalyticOnNhd ℝ p.sum Set.univ := by
    simpa only [hp,Metric.eball_top] using! p.analyticOnNhd
  have hlocal : g=ᶠ[𝓝 (0 : ℝ)] p.sum := by
    obtain ⟨r,hr⟩ := (hg 0 (Set.mem_univ _)).hasFPowerSeriesAt
    filter_upwards [Metric.eball_mem_nhds (0 : ℝ) hr.r_pos] with x hx
    simpa only [zero_add] using! hr.sum hx
  have he := hg.eq_of_eventuallyEq hseries hlocal
  have hsum := p.hasSum (x := t) (by simp [hp])
  rw [← he] at hsum
  convert! hsum using 1
  ext n
  simp [p,a,FormalMultilinearSeries.apply_eq_prod_smul_coeff,mul_comm]
end Qatlib.Concepts.GradientOracle.GradientAlgo
