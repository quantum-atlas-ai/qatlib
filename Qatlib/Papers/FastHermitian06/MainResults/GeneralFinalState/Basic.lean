/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Qatlib.Papers.FastHermitian06.MainResults.Defs

/-!
# General two-level Hamiltonian parameters

`H4` defines a general two-level matrix with traceless part `sigmaNGen` and squared-gap
expression `omegaSqGen`. Its scalar-square identity gives a dimensionless hyperbolic constraint;
explicit solutions show that the associated time parameter can have arbitrarily small absolute
value. See [BenderEtAl2007].

## Main statements

* `sigmaNGen_sq`: the traceless part squares to `omegaSqGen / 4` times the identity.
* `laurent_small_T`: constructs small time parameters on the hyperbola.
* `small_T_leading_Z`: realizes these parameters at angle `π / 3` with squared gap one.

## References

* [Bender et al., 2007][BenderEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix ComplexOrder

namespace Qatlib.Papers.FastHermitian06.MainResults.GeneralFinalState

open Qatlib.Papers.FastHermitian06.MainResults.Defs

/-- The squared-gap expression `4 * z^2 / sin(γ)^2 - 4 * y^2 / cos(γ)^2`. -/
def omegaSqGen (y z γ : ℝ) : ℝ :=
  4 * z ^ 2 / (Real.sin γ) ^ 2 - 4 * y ^ 2 / (Real.cos γ) ^ 2

/-- The two-level matrix with diagonal entries `x ± (z + I * y)` and common off-diagonal entry
`z / tan γ - I * y * tan γ`. -/
def H4 (x y z γ : ℝ) : Mat2 :=
  !![ ((x : ℂ) + (z : ℂ) + (y : ℂ) * Complex.I),
      ((z / Real.tan γ : ℝ) : ℂ) - ((y * Real.tan γ : ℝ) : ℂ) * Complex.I;
      ((z / Real.tan γ : ℝ) : ℂ) - ((y * Real.tan γ : ℝ) : ℂ) * Complex.I,
      ((x : ℂ) - (z : ℂ) - (y : ℂ) * Complex.I) ]

/-- The real parity matrix with rows `(sin γ, cos γ)` and `(cos γ, -sin γ)`. -/
def parityGamma (γ : ℝ) : Mat2 :=
  !![(Real.sin γ : ℂ), (Real.cos γ : ℂ); (Real.cos γ : ℂ), -(Real.sin γ : ℂ)]

/-- The matrix transformation `P * conjT M * P` for a specified matrix `P`. -/
def PTg (P M : Mat2) : Mat2 := P * conjT M * P

/-- The traceless part of `H4 x y z γ`, independent of `x`. -/
def sigmaNGen (y z γ : ℝ) : Mat2 :=
  !![ ((z : ℂ) + (y : ℂ) * Complex.I),
      ((z / Real.tan γ : ℝ) : ℂ) - ((y * Real.tan γ : ℝ) : ℂ) * Complex.I;
      ((z / Real.tan γ : ℝ) : ℂ) - ((y * Real.tan γ : ℝ) : ℂ) * Complex.I,
      -((z : ℂ) + (y : ℂ) * Complex.I) ]

/-- Decomposes `H4` into `x` times the identity and `sigmaNGen`. -/
theorem H4_decomp (x y z γ : ℝ) :
    H4 x y z γ = (x : ℂ) • (1 : Mat2) + sigmaNGen y z γ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H4, sigmaNGen, Matrix.smul_apply] <;> ring

/-- When both `sin γ` and `cos γ` are nonzero, the square of `sigmaNGen` is `omegaSqGen / 4`
times the identity. -/
theorem sigmaNGen_sq (y z γ : ℝ) (hsin : Real.sin γ ≠ 0)
    (hcos : Real.cos γ ≠ 0) :
    sigmaNGen y z γ * sigmaNGen y z γ = (omegaSqGen y z γ / 4) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaNGen, omegaSqGen, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Real.tan_eq_sin_div_cos]
  all_goals rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
  all_goals
    have hsc : ((Real.sin γ : ℂ)) ≠ 0 := by exact_mod_cast hsin
    have hcc : ((Real.cos γ : ℂ)) ≠ 0 := by exact_mod_cast hcos
    field_simp [hsc, hcc]
  all_goals ring_nf
  all_goals rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]]
  all_goals norm_cast
  all_goals norm_num
  all_goals ring_nf
  all_goals
    linear_combination (z ^ 2 * Real.cos γ ^ 2 - y ^ 2 * Real.sin γ ^ 2)
      * Real.sin_sq_add_cos_sq γ

/-- The dimensionless parameters determined by a positive gap satisfy `1 = Z^2 - Y^2 * (1 / cos
γ)^2`. -/
theorem dimensionless_hyperbolic_constraint (y z γ ω Z Y : ℝ) (hω : 0 < ω)
    (hsin : Real.sin γ ≠ 0) (hcos : Real.cos γ ≠ 0)
    (hωsq : ω ^ 2 = omegaSqGen y z γ)
    (hZ : Z = 2 * z / (ω * Real.sin γ)) (hY : Y = 2 * y / ω) :
    1 = Z ^ 2 - Y ^ 2 * (1 / Real.cos γ) ^ 2 := by
  subst hZ
  subst hY
  unfold omegaSqGen at hωsq
  have hkey : ω ^ 2 * (Real.sin γ) ^ 2 * (Real.cos γ) ^ 2
      = 4 * z ^ 2 * (Real.cos γ) ^ 2 - 4 * y ^ 2 * (Real.sin γ) ^ 2 := by
    have h := congrArg (fun t : ℝ => t * ((Real.sin γ) ^ 2 * (Real.cos γ) ^ 2)) hωsq
    field_simp [hsin, hcos] at h
    linarith [h]
  field_simp [ne_of_gt hω, hsin, hcos]
  linear_combination hkey

/-- The hyperbola `1 = Z^2 - 4 * Y^2` has positive `Z` coordinates exceeding any prescribed
lower bound. -/
theorem hyperbolic_constraint_unbounded (Z₀ : ℝ) :
    ∃ Z Y : ℝ, Z₀ ≤ Z ∧ 0 < Z ∧ 1 = Z ^ 2 - 4 * Y ^ 2 := by
  set k : ℝ := max Z₀ 0 with hk
  have hk0 : 0 ≤ k := le_max_right Z₀ 0
  have hZ₀ : Z₀ ≤ k := le_max_left Z₀ 0
  refine ⟨Real.sqrt (1 + 4 * k ^ 2), k, ?_, ?_, ?_⟩
  · have h1 : 0 ≤ 4 * k ^ 2 := by positivity
    have h2 : k ≤ Real.sqrt (1 + 4 * k ^ 2) := by
      have h3 : k ^ 2 ≤ 1 + 4 * k ^ 2 := by nlinarith
      calc k = Real.sqrt (k ^ 2) := (Real.sqrt_sq hk0).symm
        _ ≤ Real.sqrt (1 + 4 * k ^ 2) := Real.sqrt_le_sqrt h3
    linarith
  · have h1 : 0 < 1 + 4 * k ^ 2 := by positivity
    exact Real.sqrt_pos.mpr h1
  · have hsq : (Real.sqrt (1 + 4 * k ^ 2)) ^ 2 = 1 + 4 * k ^ 2 :=
      Real.sq_sqrt (by positivity)
    rw [hsq]
    ring

/-- For nonzero `u` and positive `ε`, the hyperbola has a point with `T = -u / Z`, `|T| < ε`,
and `Z > |u| / ε`. -/
theorem laurent_small_T (u : ℝ) (hu : u ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Z Y T : ℝ, 0 < Z ∧ 1 = Z ^ 2 - 4 * Y ^ 2 ∧
      T = -u / Z ∧ |T| < ε ∧ |u| / ε < Z := by
  set Z : ℝ := |u| / ε + 1 with hZdef
  have hZpos : 0 < Z := by positivity
  have hZgt : |u| / ε < Z := by linarith
  have hYnonneg : 0 ≤ (Z ^ 2 - 1) / 4 := by
    have : 1 ≤ Z := by
      have h0 : 0 ≤ |u| / ε := by positivity
      linarith
    nlinarith
  refine ⟨Z, Real.sqrt ((Z ^ 2 - 1) / 4), -u / Z, hZpos, ?_, rfl, ?_, hZgt⟩
  · have hsq : (Real.sqrt ((Z ^ 2 - 1) / 4)) ^ 2 = (Z ^ 2 - 1) / 4 :=
      Real.sq_sqrt hYnonneg
    rw [hsq]
    ring
  · rw [abs_div, abs_of_pos hZpos]
    simp only [abs_neg]
    have h1 : |u| < Z * ε := by
      rw [div_lt_iff₀ hε] at hZgt
      linarith
    rw [div_lt_iff₀ hZpos]
    linarith

/-- For nonzero `u` and positive `ε`, constructs parameters at angle `π / 3` with squared gap
one and the stated small-time and lower-bound relations. -/
theorem small_T_leading_Z (u : ℝ) (hu : u ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ _x y z t T : ℝ,
      0 < z ∧
      omegaSqGen y z (Real.pi / 3) = 1 ∧
      T = t / 2 ∧
      T = -(u / (2 * z / Real.sin (Real.pi / 3))) ∧
      |T| < ε ∧
      |u| / (4 * ε) < z := by
  obtain ⟨Z, Y, T, hZpos, hcon, hT, hTsmall, hZbig⟩ := laurent_small_T u hu ε hε
  have hsin3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have hcos3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  set z : ℝ := Z * Real.sin (Real.pi / 3) / 2 with hzdef
  set y : ℝ := Y / 2 with hydef
  have hzpos : 0 < z := by
    have hspos : 0 < Real.sin (Real.pi / 3) := by
      rw [hsin3]
      positivity
    simpa [hzdef] using mul_pos hZpos hspos
  have hzbig : |u| / (4 * ε) < z := by
    have hspos : 0 < Real.sin (Real.pi / 3) := by
      rw [hsin3]
      positivity
    have hsc : (1 : ℝ) / 2 < Real.sin (Real.pi / 3) := by
      rw [hsin3]
      have : (1 : ℝ) < Real.sqrt 3 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    have hZgt : |u| / ε < Z := hZbig
    have hpos : 0 < |u| / ε := by positivity
    have hprod1 : (|u| / ε) * (1 / 2) < Z * (1 / 2) :=
      mul_lt_mul_of_pos_right hZgt (by norm_num)
    have hprod2 : Z * (1 / 2) < Z * Real.sin (Real.pi / 3) :=
      mul_lt_mul_of_pos_left hsc hZpos
    have hprod : (|u| / ε) * (1 / 2) < Z * Real.sin (Real.pi / 3) :=
      lt_trans hprod1 hprod2
    have hhalf : |u| / (4 * ε) = (|u| / ε) * (1 / 2) / 2 := by
      field_simp
      ring
    rw [hzdef, hhalf]
    linarith
  have homega : omegaSqGen y z (Real.pi / 3) = 1 := by
    have hsin2 : (Real.sin (Real.pi / 3)) ^ 2 = 3 / 4 := Real.sq_sin_pi_div_three
    have hcos2 : (Real.cos (Real.pi / 3)) ^ 2 = 1 / 4 := by
      rw [hcos3]
      norm_num
    have hZ2 : Z ^ 2 - 4 * Y ^ 2 = 1 := by linarith
    unfold omegaSqGen
    rw [hsin2, hcos2, hzdef, hydef]
    field_simp
    nlinarith [hZ2]
  have hZT : 2 * z / Real.sin (Real.pi / 3) = Z := by
    rw [hzdef]
    have hspos : Real.sin (Real.pi / 3) ≠ 0 := by
      rw [hsin3]
      positivity
    field_simp
  refine ⟨0, y, z, 2 * T, T, hzpos, homega, ?_, ?_, hTsmall, hzbig⟩
  · ring
  · rw [hZT, hT]
    ring

end Qatlib.Papers.FastHermitian06.MainResults.GeneralFinalState
