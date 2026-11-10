/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeometric
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom

namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler

def binCoeff (n : ℕ) : ℝ := (n.factorial:ℝ)⁻¹*(ascPochhammer ℝ n).eval (1/2)

theorem choose_half_eq_binCoeff (n : ℕ) : Ring.choose ((1/2:ℝ)+n-1) n=binCoeff n := by
  rw [Ring.choose_eq_smul,Polynomial.descPochhammer_smeval_eq_ascPochhammer,smul_eq_mul]
  have he : (1/2:ℝ)+n-1-n+1=1/2 := by ring
  rw [he,Polynomial.ascPochhammer_smeval_eq_eval]
  rfl

theorem binCoeff_pos (n : ℕ) : 0<binCoeff n := by
  unfold binCoeff
  exact mul_pos (inv_pos.mpr (by positivity)) (ascPochhammer_pos _ _ (by norm_num))

theorem binCoeff_succ (n : ℕ) :
    binCoeff (n+1)=binCoeff n*((n+1/2:ℝ)/(n+1)) := by
  unfold binCoeff
  rw [Nat.factorial_succ,ascPochhammer_succ_eval]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_inv_rev]
  ring

theorem gauss_coeff_from_binomial (n : ℕ) :
    coeff n=3*binCoeff n/((2*(n:ℝ)+1)*(2*(n:ℝ)+3)) := by
  induction n with
  | zero => norm_num [coeff_zero,binCoeff,ascPochhammer_zero]
  | succ n ih =>
    rw [coeff_succ,ih,binCoeff_succ]
    push_cast
    have hn : (0:ℝ)≤n := by positivity
    field_simp
    ring

theorem inverse_sqrt_hasSum (x : ℝ) (hx0 : 0≤x) (hx1 : x<1) :
    HasSum (fun n : ℕ => binCoeff n*x^n) (1/Real.sqrt (1-x)) := by
  have hx : x∈Metric.eball (0:ℝ) 1 := by
    rw [← ENNReal.ofReal_one,Metric.eball_ofReal]
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hx0] using hx1
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1/2)).hasSum_sub hx
  simpa only [sub_zero,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,
    choose_half_eq_binCoeff,← Real.sqrt_eq_rpow] using h

def kernel (z u : ℝ) : ℝ := (1-u^2)/Real.sqrt (1-z*u^2)

def eulerTerm (z : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (3/2:ℝ)*binCoeff n*z^n*((1-u^2)*u^(2*n))

theorem euler_hasSum {z : ℝ} (hz0 : 0≤z) (hz1 : z≤1) (u : ℝ)
    (hu : u∈Set.Icc (0:ℝ) 1) :
    HasSum (fun n : ℕ => eulerTerm z n u) ((3/2:ℝ)*kernel z u) := by
  by_cases hx : z*u^2<1
  · have h := (inverse_sqrt_hasSum (z*u^2) (by positivity) hx).mul_left ((3/2:ℝ)*(1-u^2))
    convert! h using 1
    · funext n
      unfold eulerTerm
      rw [mul_pow,← pow_mul]
      ring
    · unfold kernel
      ring
  · have hu0 := hu.1
    have hu1 := hu.2
    have he : u^2=1 := by nlinarith [sq_nonneg u]
    have hez : z=1 := by nlinarith
    simp only [eulerTerm,he,sub_self,zero_mul,mul_zero,kernel,hez,one_mul,Real.sqrt_zero,zero_div]
    exact hasSum_zero

end Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler
