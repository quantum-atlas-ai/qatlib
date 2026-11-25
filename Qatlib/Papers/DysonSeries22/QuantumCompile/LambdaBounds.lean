/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-!
# Normalization bounds for truncated Dyson series

The nonnegative exponential Taylor coefficients bound the finite normalization sums.
For the inhomogeneous series, convexity of the exponential on the unit interval gives a
linear bound after removing its constant term, so the factor of the system normalization cancels.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.DysonSeries22.QuantumCompile

/-- The finite homogeneous normalization in Eq. (57) is bounded by the exponential
and hence by Euler's number at the source step-size limit. -/
theorem dyson_lambda_le_exp (K : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ Finset.range (K + 1), x ^ k / (k.factorial : ℝ)) ≤ Real.exp x ∧
      Real.exp x ≤ Real.exp 1 :=
  ⟨Real.sum_le_exp_of_nonneg hx0 _, Real.exp_le_exp.2 hx1⟩

/-- The truncated forcing normalization in Eq. (60) is at most `(e - 1) * lamB * dt`. -/
theorem forcing_lambda_bound (K : ℕ) (lamA lamB dt : ℝ) (hA : 0 < lamA) (hb : 0 ≤ lamB)
    (hdt : 0 ≤ dt) (hstep : lamA * dt ≤ 1) :
    (lamB / lamA) * (∑ k ∈ Finset.Icc 1 K, (lamA * dt) ^ k / (k.factorial : ℝ)) ≤
      (Real.exp 1 - 1) * lamB * dt := by
  let x := lamA * dt
  have hx : 0 ≤ x := mul_nonneg hA.le hdt
  have hexp : Real.exp x - 1 ≤ (Real.exp 1 - 1) * x := by
    have hh := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
      (show 0 ≤ 1 - x from sub_nonneg.mpr hstep) hx (by ring : (1 - x) + x = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hh
    linarith
  have hIcc : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsum : (∑ k ∈ Finset.Icc 1 K, x ^ k / (k.factorial : ℝ)) ≤ Real.exp x - 1 := by
    rw [hIcc, Finset.sum_Ico_eq_sub _ (by omega)]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one]
    exact sub_le_sub_right (Real.sum_le_exp_of_nonneg hx _) _
  calc
    _ ≤ (lamB / lamA) * ((Real.exp 1 - 1) * x) :=
      mul_le_mul_of_nonneg_left (hsum.trans hexp) (div_nonneg hb hA.le)
    _ = _ := by dsimp [x]; field_simp

end Qatlib.Papers.DysonSeries22.QuantumCompile
