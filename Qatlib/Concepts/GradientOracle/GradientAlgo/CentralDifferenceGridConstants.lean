/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferencePowerSumBoundOpti
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Constants for central-difference grid errors

This module combines signed stencil moments, exponential decay, and factorial estimates into a
geometric bound for each high-degree term. The constants support the analytic gradient
approximation considered in [GilyenArunachalamWiebe2019].

## Main statements

* `centralDiff_signed_moment_bound`: an exponentially decaying bound for signed stencil moments.
* `centralDiff_grid_degree_constant`: the combined degree factor is bounded by `(8*R*c*m*sqrt
  d)^k`.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

open Qatlib.Concepts.GradientOracle.CentralDiff

set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators

/-- For positive stencil order `m` and degree `k ≥ 2*m+1`, the absolute signed stencil moment is
at most `6*exp (-(7/6)*m)*m^k*sqrt m`. -/
theorem centralDiff_signed_moment_bound (m k : ℕ) (hm : 0<m) (hk : 2*m+1≤k) :
    |∑ l∈Finset.Ico (-(m : ℤ)) ((m : ℤ)+1),centralDiffCoeff m l*(l : ℝ)^k|
      ≤6*Real.exp (-(7/6 : ℝ)*m)*(m : ℝ)^k*Real.sqrt m := by
  have hmr : (0 : ℝ)<m := by exact_mod_cast hm
  have hn : k-1+1=k := by omega
  have he : ((k-1 : ℕ) : ℝ)+3/2=(k : ℝ)+1/2 := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hn
    push_cast at h
    linarith
  have h := centralDifferencePowerSumBound m (k-1) hm (by omega)
  rw [hn,he,Real.rpow_add hmr,Real.rpow_natCast,← Real.sqrt_eq_rpow] at h
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa only [mul_assoc] using h)

/-- For positive natural `m`, the exponential prefactor `exp (-(7/6)*m)` is at most `1/3`. -/
private theorem centralDiff_exp_prefactor (m : ℕ) (hm : 0<m) :
    Real.exp (-(7/6 : ℝ)*m)≤1/3 := by
  have hmr : (1 : ℝ)≤m := by exact_mod_cast hm
  have he1 : (8/3 : ℝ)≤Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
  have he6 : (7/6 : ℝ)≤Real.exp (1/6 : ℝ) := by
    have h := Real.add_one_le_exp (1/6 : ℝ)
    linarith
  have he : (3 : ℝ)≤Real.exp (7/6 : ℝ) := by
    have h := mul_le_mul he1 he6 (by norm_num) (Real.exp_pos _).le
    rw [← Real.exp_add,show (1 : ℝ)+1/6=7/6 by ring] at h
    norm_num at h
    linarith
  calc
    _ ≤ Real.exp (-(7/6 : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ 1/3 := by
      rw [Real.exp_neg]
      rw [← one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      linarith

/-- For positive `m` and `k ≥ 2*m+1`, bounds the stencil prefactor `6*sqrt 2*exp (-(7/6)*m)*sqrt
m` by `sqrt (2*π*k)`. -/
theorem centralDiff_grid_prefactor (m k : ℕ) (hm : 0<m) (hk : 2*m+1≤k) :
    6*Real.sqrt 2*Real.exp (-(7/6 : ℝ)*m)*Real.sqrt m≤Real.sqrt (2*Real.pi*k) := by
  have he := centralDiff_exp_prefactor m hm
  have hle := mul_le_mul_of_nonneg_right he (by positivity : (0 : ℝ)≤6*Real.sqrt 2*Real.sqrt m)
  have hroot : 2*Real.sqrt 2*Real.sqrt m≤Real.sqrt (2*Real.pi*k) := by
    have hm0 : (0 : ℝ)≤m := Nat.cast_nonneg _
    have hkR : (2 : ℝ)*m≤k := by exact_mod_cast (show 2*m≤k by omega)
    have hsq : (2*Real.sqrt 2*Real.sqrt m)^2≤2*Real.pi*k := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sq_sqrt hm0]
      have hπ := Real.pi_gt_three
      have hk0 : (0 : ℝ)≤k := Nat.cast_nonneg _
      nlinarith
    have h := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq (by positivity : (0 : ℝ)≤2*Real.sqrt 2*Real.sqrt m)] using h
  apply (show 6*Real.sqrt 2*Real.exp (-(7/6 : ℝ)*m)*Real.sqrt m≤2*Real.sqrt 2*Real.sqrt m by nlinarith).trans hroot

/-- The numerical constant `2*sqrt 2*exp 1` is at most eight. -/
theorem centralDiff_grid_base : 2*Real.sqrt 2*Real.exp 1≤8 := by
  have hs : Real.sqrt 2≤16/11 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have he : Real.exp 1≤11/4 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have h := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ)≤2*Real.sqrt 2)
  nlinarith

/-- Under the positive parameter and degree assumptions, the product of the tensor, derivative,
radius, stencil-moment, and inverse-factorial factors is at most `(8*R*c*m*sqrt d)^k`. -/
theorem centralDiff_grid_degree_constant (d m k : ℕ) (hd : 0<d) (hm : 0<m)
    (hk : 2*m+1≤k) (R c : ℝ) (hR : 0<R) (hc : 0<c) :
    Real.sqrt 2*(4*Real.sqrt ((d : ℝ)*k/2))^k*
        (c^k*(k : ℝ)^((k : ℝ)/2))*R^k*
        (6*Real.exp (-(7/6 : ℝ)*m)*(m : ℝ)^k*Real.sqrt m)/(Nat.factorial k : ℝ)
      ≤(8*R*c*m*Real.sqrt d)^k := by
  have hk0 : 0<k := by omega
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk0
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have he : (0 : ℝ)<Real.exp 1 := Real.exp_pos _
  have hs2 : 0<Real.sqrt (2 : ℝ) := by positivity
  have hsk : 0<Real.sqrt k := Real.sqrt_pos.mpr hkR
  have hden : 0<Real.sqrt (2*Real.pi*k)*((k : ℝ)/Real.exp 1)^k := by positivity
  have hf := Stirling.le_factorial_stirling k
  have hpow : (k : ℝ)^((k : ℝ)/2)=(Real.sqrt k)^k := by
    rw [show (k : ℝ)/2=(1/2 : ℝ)*(k : ℝ) by ring,Real.rpow_mul hkR.le,Real.rpow_natCast,← Real.sqrt_eq_rpow]
  have hroot : Real.sqrt ((d : ℝ)*k/2)=Real.sqrt d*Real.sqrt k/Real.sqrt 2 := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ)≤(d : ℝ)*k),Real.sqrt_mul hdR.le]
  have hfour : (4 : ℝ)/Real.sqrt 2=2*Real.sqrt 2 := by
    apply (div_eq_iff hs2.ne').mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  have hfactor : (4*Real.sqrt ((d : ℝ)*k/2))*c*Real.sqrt k*R*m/((k : ℝ)/Real.exp 1)=
      2*Real.sqrt 2*Real.exp 1*R*c*m*Real.sqrt d := by
    rw [hroot]
    have hs := Real.sq_sqrt hkR.le
    calc
      _ = (4/Real.sqrt 2)*(Real.exp 1)*R*c*m*Real.sqrt d := by
        field_simp
        nlinarith
      _ = _ := by rw [hfour]
  let P := 6*Real.sqrt 2*Real.exp (-(7/6 : ℝ)*m)*Real.sqrt m/Real.sqrt (2*Real.pi*k)
  have hP : P≤1 := (div_le_one (by positivity)).mpr (centralDiff_grid_prefactor m k hm hk)
  have hrewrite : Real.sqrt 2*(4*Real.sqrt ((d : ℝ)*k/2))^k*
      (c^k*(k : ℝ)^((k : ℝ)/2))*R^k*
      (6*Real.exp (-(7/6 : ℝ)*m)*(m : ℝ)^k*Real.sqrt m)/
      (Real.sqrt (2*Real.pi*k)*((k : ℝ)/Real.exp 1)^k)=
      P*(2*Real.sqrt 2*Real.exp 1*R*c*m*Real.sqrt d)^k := by
    rw [hpow,← hfactor]
    simp only [div_pow,mul_pow,P]
    ring
  have hbase : 2*Real.sqrt 2*Real.exp 1*R*c*m*Real.sqrt d≤8*R*c*m*Real.sqrt d := by
    have h :=
        mul_le_mul_of_nonneg_right centralDiff_grid_base (by positivity : (0 : ℝ)≤R*c*m*Real.sqrt d)
    simpa only [mul_assoc] using h
  calc
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden hf
    _ = _ := hrewrite
    _ ≤ (2*Real.sqrt 2*Real.exp 1*R*c*m*Real.sqrt d)^k := by
      simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hP
          (by positivity : (0 : ℝ)≤(2*Real.sqrt 2*Real.exp 1*R*c*m*Real.sqrt d)^k)
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase k
end Qatlib.Concepts.GradientOracle.GradientAlgo
