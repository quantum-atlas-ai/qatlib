/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.EulerDecomposition
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Tactic.ComputeDegree
import Mathlib.NumberTheory.Real.Irrational
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.CliffordTAngle

/-!
# Clifford-T Density in SU(2)

The submonoid `cliffordT` consists of finite products of the Hadamard and T matrices, and
`cliffordTLim` is its topological closure. Using the irrational angles `htAngle` and `wAngle`,
`axisRot_mem_of_irrational` promotes a rotation and its inverse in a closed submonoid to
rotations through every angle about the same unit axis. This supplies the rotation families
needed for the single-qubit universality argument discussed in [NielsenChuang2010].

The decomposition `exists_euler_two_axes` expresses each determinant-one unitary as three
rotations about two explicit axes. Combining this decomposition with `axisRot_uAxis_mem` and
`axisRot_wAxis_mem` gives `det_one_mem_cliffordTLim`. For an arbitrary two-dimensional unitary,
`exists_phase_mem_cliffordTLim` gives membership after multiplication by a suitable global
phase, a density input for the approximation framework of [DawsonNielsen2006].

## Main statements

* `irrational_wAngle_div_four_pi` establishes the second irrational rotation angle with the
  SU(2) period.
* `axisRot_mem_of_irrational` gives all rotations about a fixed unit axis from one irrational
  rotation and its inverse.
- `exists_euler_two_axes` gives a three-factor decomposition using the two specified axes.
- `det_one_mem_cliffordTLim` places every SU(2) matrix in the closure of Clifford-T products.
* `exists_phase_mem_cliffordTLim` extends the result to two-dimensional unitaries up to global
  phase.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010], *Quantum Computation and Quantum Information*.
- [Dawson and Nielsen, 2006][DawsonNielsen2006], *The Solovay-Kitaev algorithm*.
-/

set_option warningAsError false
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.Euler
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.CliffordT

section

open Matrix Polynomial
open scoped Real

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

/-- An irrational real root of `X ^ 2 + p * X + q`, with rational coefficients and nonintegral
`p`, is not integral over the integers. The argument identifies this monic quadratic with
the minimal polynomial over the rationals. -/
theorem not_isIntegral_of_quadratic {x : ℝ} {p q : ℚ}
    (hx : x ^ 2 + (p : ℝ) * x + (q : ℝ) = 0) (hirr : Irrational x) (hp : p.den ≠ 1) :
    ¬ IsIntegral ℤ x := by
  intro h
  set P : ℚ[X] := X ^ 2 + C p * X + C q with hP
  have hPmonic : P.Monic := by rw [hP]; monicity!
  have hPdeg : P.natDegree = 2 := by rw [hP]; compute_degree!
  have hroot : (aeval x) P = 0 := by
    rw [hP]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast]
    linear_combination hx
  have hxint : IsIntegral ℚ x := ⟨P, hPmonic, hroot⟩
  have hdvd : minpoly ℚ x ∣ P := minpoly.dvd ℚ x hroot
  have hge : 2 ≤ (minpoly ℚ x).natDegree := by
    refine (minpoly.two_le_natDegree_iff hxint).mpr ?_
    intro hmem
    obtain ⟨y, hy⟩ := hmem
    exact hirr ⟨y, by rw [← hy]; simp⟩
  have hle : (minpoly ℚ x).natDegree ≤ 2 := by
    rw [← hPdeg]
    exact Polynomial.natDegree_le_of_dvd hdvd hPmonic.ne_zero
  have hdeg2 : (minpoly ℚ x).natDegree = 2 := le_antisymm hle hge
  have heq : minpoly ℚ x = P := by
    obtain ⟨C', hC'⟩ := hdvd
    have hC'ne : C' ≠ 0 := fun hz => hPmonic.ne_zero (by rw [hC', hz, mul_zero])
    have hdegs : P.natDegree = (minpoly ℚ x).natDegree + C'.natDegree := by
      rw [hC', Polynomial.natDegree_mul (minpoly.ne_zero hxint) hC'ne]
    have hC'deg : C'.natDegree = 0 := by
      rw [hPdeg, hdeg2] at hdegs
      omega
    have hC'monic : C'.Monic :=
      Polynomial.Monic.of_mul_monic_left (minpoly.monic hxint) (hC' ▸ hPmonic)
    rw [hC', Polynomial.eq_one_of_monic_natDegree_zero hC'monic hC'deg, mul_one]
  have hmap : minpoly ℚ x = Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ x) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ h
  have h1 : (minpoly ℚ x).coeff 1 = p := by
    rw [heq, hP]
    simp
  rw [hmap, Polynomial.coeff_map] at h1
  exact hp (by rw [← h1]; simp)

namespace QuantumInfo

namespace SU2

/-- The axis coordinate `htB` is strictly positive. -/
theorem htB_pos : 0 < htB := by
  rw [htB]
  have h1 : Real.sqrt 2 < 2 := sqrt_two_lt_two
  exact div_pos (by linarith) htSin_pos

/-- The squared axis coordinate `htA` equals `(5 + 2 * Real.sqrt 2) / 17`. -/
theorem htA_sq : htA ^ 2 = (5 + 2 * Real.sqrt 2) / 17 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlt : Real.sqrt 2 < 2 := sqrt_two_lt_two
  have hd : (10 : ℝ) - 4 * Real.sqrt 2 ≠ 0 := by nlinarith
  have hprod : htA ^ 2 * htSin ^ 2 = 2 / 16 := by
    rw [htA, div_pow, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 htSin_ne_zero),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have key : htA ^ 2 * ((10 : ℝ) - 4 * Real.sqrt 2) = 2 := by
    rw [htSin_sq] at hprod
    linear_combination 16 * hprod
  have expand : (5 + 2 * Real.sqrt 2) * ((10 : ℝ) - 4 * Real.sqrt 2) = 34 := by nlinarith [h2]
  have h17 : (17 : ℝ) * htA ^ 2 = 5 + 2 * Real.sqrt 2 := by
    refine mul_right_cancel₀ hd ?_
    rw [expand]
    linear_combination 17 * key
  linarith

/-- The squared axis coordinate `htB` equals `(7 - 4 * Real.sqrt 2) / 17`. -/
theorem htB_sq : htB ^ 2 = (7 - 4 * Real.sqrt 2) / 17 := by
  have h := htAxis_unit
  rw [htA_sq] at h
  linarith

/-- This is the real number `-(Real.sqrt 2 * htA)`, used as the cosine of half the second
rotation angle. -/
noncomputable def wHalfCos : ℝ := -(Real.sqrt 2 * htA)

/-- The second rotation angle is defined as `2 * Real.arccos wHalfCos`. -/
noncomputable def wAngle : ℝ := 2 * Real.arccos wHalfCos

/-- The square of `wHalfCos` is `(10 + 4 * Real.sqrt 2) / 17`. -/
theorem wHalfCos_sq : wHalfCos ^ 2 = (10 + 4 * Real.sqrt 2) / 17 := by
  rw [wHalfCos, neg_sq, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), htA_sq]
  ring

/-- The real square root of two is strictly less than `7 / 4`. -/
theorem sqrt_two_lt_seven_quarters : Real.sqrt 2 < 7 / 4 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- The square of `wHalfCos` is strictly less than one. -/
theorem wHalfCos_sq_lt_one : wHalfCos ^ 2 < 1 := by
  rw [wHalfCos_sq]
  nlinarith [sqrt_two_lt_seven_quarters]

/-- The value `wHalfCos` lies in the closed interval from negative one to one, allowing the
inverse-cosine identities to apply. -/
theorem wHalfCos_mem : -1 ≤ wHalfCos ∧ wHalfCos ≤ 1 := by
  have h := wHalfCos_sq_lt_one
  constructor <;> nlinarith [sq_nonneg (wHalfCos + 1), sq_nonneg (wHalfCos - 1)]

/-- The cosine of `wAngle / 2` is `wHalfCos`. -/
theorem cos_wAngle_half : Real.cos (wAngle / 2) = wHalfCos := by
  rw [wAngle, show 2 * Real.arccos wHalfCos / 2 = Real.arccos wHalfCos by ring,
    Real.cos_arccos wHalfCos_mem.1 wHalfCos_mem.2]

/-- The sine of `wAngle / 2` is the positive axis coordinate `htB`. -/
theorem sin_wAngle_half : Real.sin (wAngle / 2) = htB := by
  have hb := htB_sq
  rw [wAngle, show 2 * Real.arccos wHalfCos / 2 = Real.arccos wHalfCos by ring, Real.sin_arccos,
    show 1 - wHalfCos ^ 2 = htB ^ 2 by rw [wHalfCos_sq, hb]; ring, Real.sqrt_sq htB_pos.le]

/-- Twice the cosine of `wAngle` equals `(6 + 16 * Real.sqrt 2) / 17`. -/
theorem two_mul_cos_wAngle : 2 * Real.cos wAngle = (6 + 16 * Real.sqrt 2) / 17 := by
  have hdouble : Real.cos wAngle = 2 * Real.cos (wAngle / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (wAngle / 2)
    rwa [show 2 * (wAngle / 2) = wAngle by ring] at h
  rw [hdouble, cos_wAngle_half, wHalfCos_sq]
  ring

/-- The real number `2 * Real.cos wAngle` is irrational. -/
theorem irrational_two_mul_cos_wAngle : Irrational (2 * Real.cos wAngle) := by
  rw [two_mul_cos_wAngle]
  rintro ⟨q, hq⟩
  refine irrational_sqrt_two ⟨(17 * q - 6) / 16, ?_⟩
  push_cast at hq ⊢
  field_simp at hq ⊢
  linarith [hq]

/-- The real number `2 * Real.cos wAngle` is not integral over the integers, using its
irrationality and its monic quadratic with a nonintegral rational coefficient. -/
theorem not_isIntegral_two_mul_cos_wAngle : ¬ IsIntegral ℤ (2 * Real.cos wAngle) := by
  refine not_isIntegral_of_quadratic (p := -12 / 17) (q := -28 / 17) ?_
    irrational_two_mul_cos_wAngle (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [two_mul_cos_wAngle]
  push_cast
  nlinarith [h2]

/-- The ratio `wAngle / (2 * π)` is irrational, since a rational ratio would make twice its
cosine integral over the integers. -/
theorem irrational_wAngle_div_two_pi : Irrational (wAngle / (2 * π)) := by
  rintro ⟨q, hq⟩
  have hpi : (2 : ℝ) * π ≠ 0 := by positivity
  have hθ : wAngle = 2 * π * q := by
    field_simp at hq
    linarith [hq]
  exact not_isIntegral_two_mul_cos_wAngle (isIntegral_two_mul_cos_of_eq_two_pi_mul hθ)

/-- The ratio `wAngle / (4 * π)` is irrational, giving the irrationality condition for the
period of the SU(2) rotation parametrization. -/
theorem irrational_wAngle_div_four_pi : Irrational (wAngle / (4 * π)) := by
  rintro ⟨q, hq⟩
  refine irrational_wAngle_div_two_pi ⟨2 * q, ?_⟩
  have hpi : π ≠ 0 := Real.pi_ne_zero
  push_cast at hq ⊢
  field_simp at hq ⊢
  linarith [hq]

/-- Negating all three axis coordinates has the same effect on `axisRot` as negating the
rotation angle. -/
theorem axisRot_neg_axis (a b c θ : ℝ) : axisRot (-a) (-b) (-c) θ = axisRot a b c (-θ) := by
  rw [axisRot, axisRot, show -θ / 2 = -(θ / 2) by ring, Real.cos_neg, Real.sin_neg]
  congr 1 <;> ring

/-- Conjugating a z-axis rotation by `Euler.ryMat (π / 4)` gives a rotation with axis
`(Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2)` and the same angle. -/
theorem ryMat_conj_rzMat (t : ℝ) :
    Euler.ryMat (π / 4) * Euler.rzMat t * Euler.ryMat (-(π / 4))
      = axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) t := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpy : Real.sin (π / 8) ^ 2 + Real.cos (π / 8) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hdiff : Real.cos (π / 8) ^ 2 - Real.sin (π / 8) ^ 2 = Real.sqrt 2 / 2 := by
    have h := Real.cos_two_mul' (π / 8)
    rw [show 2 * (π / 8) = π / 4 by ring, Real.cos_pi_div_four] at h
    linarith [h]
  have hprod : 2 * (Real.sin (π / 8) * Real.cos (π / 8)) = Real.sqrt 2 / 2 := by
    have h := Real.sin_two_mul (π / 8)
    rw [show 2 * (π / 8) = π / 4 by ring, Real.sin_pi_div_four] at h
    linarith [h]
  rw [Euler.ryMat, Euler.rzMat, Euler.ryMat, axisRot, axisRot, axisRot, axisRot,
    show π / 4 / 2 = π / 8 by ring, show -(π / 4) / 2 = -(π / 8) by ring,
    Real.cos_neg, Real.sin_neg, su2_mul, su2_mul]
  congr 1
  · linear_combination Real.cos (t / 2) * hpy
  · linear_combination Real.sin (t / 2) * hprod
  · ring
  · linear_combination Real.sin (t / 2) * hdiff

/-- Conjugating an x-axis rotation by `Euler.ryMat (π / 4)` gives a rotation with axis
`(Real.sqrt 2 / 2, 0, -(Real.sqrt 2 / 2))` and the same angle. -/
theorem ryMat_conj_axisRot_x (t : ℝ) :
    Euler.ryMat (π / 4) * axisRot 1 0 0 t * Euler.ryMat (-(π / 4))
      = axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) t := by
  have hpy : Real.sin (π / 8) ^ 2 + Real.cos (π / 8) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hdiff : Real.cos (π / 8) ^ 2 - Real.sin (π / 8) ^ 2 = Real.sqrt 2 / 2 := by
    have h := Real.cos_two_mul' (π / 8)
    rw [show 2 * (π / 8) = π / 4 by ring, Real.cos_pi_div_four] at h
    linarith [h]
  have hprod : 2 * (Real.sin (π / 8) * Real.cos (π / 8)) = Real.sqrt 2 / 2 := by
    have h := Real.sin_two_mul (π / 8)
    rw [show 2 * (π / 8) = π / 4 by ring, Real.sin_pi_div_four] at h
    linarith [h]
  rw [Euler.ryMat, axisRot, Euler.ryMat, axisRot, axisRot, axisRot,
    show π / 4 / 2 = π / 8 by ring, show -(π / 4) / 2 = -(π / 8) by ring,
    Real.cos_neg, Real.sin_neg, su2_mul, su2_mul]
  congr 1
  · linear_combination Real.cos (t / 2) * hpy
  · linear_combination Real.sin (t / 2) * hdiff
  · ring
  · linear_combination (-(Real.sin (t / 2))) * hprod

/-- Conjugating `Euler.ryMat γ` by `Euler.rzMat (-(π / 2))` gives the x-axis rotation `axisRot 1
0 0 γ`. -/
theorem rzMat_conj_ryMat (γ : ℝ) :
    Euler.rzMat (-(π / 2)) * Euler.ryMat γ * Euler.rzMat (π / 2) = axisRot 1 0 0 γ := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Euler.rzMat, Euler.ryMat, Euler.rzMat, axisRot, axisRot, axisRot, axisRot,
    show -(π / 2) / 2 = -(π / 4) by ring, show π / 2 / 2 = π / 4 by ring,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four, su2_mul, su2_mul]
  congr 1
  · linear_combination (Real.cos (γ / 2) / 2) * h2
  · linear_combination (Real.sin (γ / 2) / 2) * h2
  · ring
  · ring

/-- If `g' * g = 1`, the product of the three factors `g * A * g'`, `g * B * g'`, and `g * C *
g'` equals `g * (A * B * C) * g'`. -/
theorem conj_mul_three {g g' A B C : Matrix (Fin 2) (Fin 2) ℂ} (h : g' * g = 1) :
    g * A * g' * (g * B * g') * (g * C * g') = g * (A * B * C) * g' := by
  calc g * A * g' * (g * B * g') * (g * C * g')
      = g * A * (g' * g) * B * (g' * g) * C * g' := by simp only [mul_assoc]
    _ = g * (A * B * C) * g' := by
        rw [h]
        simp only [mul_one, mul_assoc]

/-- Every two-dimensional unitary matrix with determinant one is a product of a z-axis rotation,
an x-axis rotation, and a z-axis rotation, as in the single-qubit Euler decompositions of
[NielsenChuang2010]. -/
theorem exists_euler_zxz {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ β γ δ : ℝ, U = Euler.rzMat β * axisRot 1 0 0 γ * Euler.rzMat δ := by
  have hgg : Euler.rzMat (π / 2) * Euler.rzMat (-(π / 2)) = 1 := by
    rw [Euler.rzMat_mul, show π / 2 + -(π / 2) = 0 by ring, Euler.rzMat_zero]
  have hgg' : Euler.rzMat (-(π / 2)) * Euler.rzMat (π / 2) = 1 := by
    rw [Euler.rzMat_mul, show -(π / 2) + π / 2 = 0 by ring, Euler.rzMat_zero]
  have hVmem : Euler.rzMat (π / 2) * U * Euler.rzMat (-(π / 2))
      ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mul_mem (mul_mem (Euler.rzMat_mem_unitaryGroup _) hU) (Euler.rzMat_mem_unitaryGroup _)
  have hVdet : (Euler.rzMat (π / 2) * U * Euler.rzMat (-(π / 2))).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdet, Euler.rzMat, Euler.rzMat,
      axisRot_det (by norm_num), axisRot_det (by norm_num)]
    norm_num
  obtain ⟨β, γ, δ, hV⟩ := Euler.exists_euler_of_det_one hVmem hVdet
  refine ⟨β, γ, δ, ?_⟩
  have hU' : U = Euler.rzMat (-(π / 2)) * (Euler.rzMat (π / 2) * U * Euler.rzMat (-(π / 2)))
      * Euler.rzMat (π / 2) := by
    rw [show Euler.rzMat (-(π / 2)) * (Euler.rzMat (π / 2) * U * Euler.rzMat (-(π / 2)))
        * Euler.rzMat (π / 2)
        = (Euler.rzMat (-(π / 2)) * Euler.rzMat (π / 2)) * U
          * (Euler.rzMat (-(π / 2)) * Euler.rzMat (π / 2)) by simp only [mul_assoc], hgg']
    simp
  rw [hU', hV, ← conj_mul_three hgg, rzMat_conj_ryMat]
  congr 1
  · congr 1
    rw [Euler.rzMat_mul, Euler.rzMat_mul]
    congr 1
    ring
  · rw [Euler.rzMat_mul, Euler.rzMat_mul]
    congr 1
    ring

/-- Every two-dimensional unitary matrix with determinant one is a product of rotations about
the axes `(Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2)`, `(Real.sqrt 2 / 2, 0, -(Real.sqrt 2 /
2))`, and the first axis again. This is the Euler decomposition after a fixed change of
axes, in the framework of [NielsenChuang2010]. -/
theorem exists_euler_two_axes {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ β γ δ : ℝ, U = axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) β
        * axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) γ
        * axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) δ := by
  have hgg : Euler.ryMat (π / 4) * Euler.ryMat (-(π / 4)) = 1 := by
    rw [Euler.ryMat_mul, show π / 4 + -(π / 4) = 0 by ring, Euler.ryMat_zero]
  have hgg' : Euler.ryMat (-(π / 4)) * Euler.ryMat (π / 4) = 1 := by
    rw [Euler.ryMat_mul, show -(π / 4) + π / 4 = 0 by ring, Euler.ryMat_zero]
  have hVmem : Euler.ryMat (-(π / 4)) * U * Euler.ryMat (π / 4)
      ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mul_mem (mul_mem (Euler.ryMat_mem_unitaryGroup _) hU) (Euler.ryMat_mem_unitaryGroup _)
  have hVdet : (Euler.ryMat (-(π / 4)) * U * Euler.ryMat (π / 4)).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdet, Euler.ryMat, Euler.ryMat,
      axisRot_det (by norm_num), axisRot_det (by norm_num)]
    norm_num
  obtain ⟨β, γ, δ, hV⟩ := exists_euler_zxz hVmem hVdet
  refine ⟨β, γ, δ, ?_⟩
  have hU' : U = Euler.ryMat (π / 4) * (Euler.ryMat (-(π / 4)) * U * Euler.ryMat (π / 4))
      * Euler.ryMat (-(π / 4)) := by
    rw [show Euler.ryMat (π / 4) * (Euler.ryMat (-(π / 4)) * U * Euler.ryMat (π / 4))
        * Euler.ryMat (-(π / 4))
        = (Euler.ryMat (π / 4) * Euler.ryMat (-(π / 4))) * U
          * (Euler.ryMat (π / 4) * Euler.ryMat (-(π / 4))) by simp only [mul_assoc], hgg]
    simp
  rw [hU', hV, ← conj_mul_three hgg', ryMat_conj_rzMat, ryMat_conj_axisRot_x, ryMat_conj_rzMat]

/-- The Hadamard matrix `hGateM` multiplied by itself is the identity matrix. -/
theorem hGateM_mul_self : hGateM * hGateM = 1 := by
  have h := sqrt_two_inv_sq_two
  rw [hGateM, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;> linear_combination h

/-- The natural power `tGateM ^ n` is the diagonal matrix with diagonal entries one and `tPhase
^ n`. -/
theorem tGateM_pow (n : ℕ) : tGateM ^ n = !![1, 0; 0, tPhase ^ n] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih, tGateM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- The eighth power of the T gate matrix is the identity matrix. -/
theorem tGateM_pow_eight : tGateM ^ 8 = 1 := by
  rw [tGateM_pow, tPhase_pow_eight]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- If `A * B = 1`, then `A ^ n * B ^ n = 1` for every natural number `n`. -/
theorem pow_mul_pow_eq_one {A B : Matrix (Fin 2) (Fin 2) ℂ} (h : A * B = 1) (n : ℕ) :
    A ^ n * B ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc A ^ (n + 1) * B ^ (n + 1) = A ^ n * (A * B) * B ^ n := by
          rw [pow_succ, pow_succ']
          simp only [mul_assoc]
      _ = A ^ n * B ^ n := by rw [h, mul_one]
      _ = 1 := ih

/-- This is the multiplicative submonoid of two-dimensional complex matrices generated by
`hGateM` and `tGateM`; its elements are finite products of these generators. -/
noncomputable def cliffordT : Submonoid (Matrix (Fin 2) (Fin 2) ℂ) :=
  Submonoid.closure {hGateM, tGateM}

/-- This is the topological closure of the Clifford-T submonoid, regarded again as a
multiplicative submonoid. -/
noncomputable def cliffordTLim : Submonoid (Matrix (Fin 2) (Fin 2) ℂ) :=
  cliffordT.topologicalClosure

/-- The Hadamard matrix belongs to the Clifford-T submonoid. -/
theorem hGateM_mem : hGateM ∈ cliffordT := Submonoid.subset_closure (by simp)

/-- The T gate matrix belongs to the Clifford-T submonoid. -/
theorem tGateM_mem : tGateM ∈ cliffordT := Submonoid.subset_closure (by simp)

/-- Every element of the Clifford-T submonoid belongs to its topological closure `cliffordTLim`. -/
theorem cliffordT_le_lim : cliffordT ≤ cliffordTLim := Submonoid.le_topologicalClosure _

/-- The underlying set of `cliffordTLim` is topologically closed in the space of two-dimensional
complex matrices. -/
theorem isClosed_cliffordTLim : IsClosed (cliffordTLim : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Submonoid.isClosed_topologicalClosure _

/-- If `θ / (4 * π)` is irrational, every matrix `axisRot a b c α` lies in the closure of the
matrices `axisRot a b c ((k : ℝ) * θ)` for integers `k`. This statement uses continuity and
periodicity and requires no unit-length condition on the coordinates. -/
theorem mem_closure_range_axisRot_of_irrational {a b c θ : ℝ}
    (hirr : Irrational (θ / (4 * π))) (α : ℝ) :
    axisRot a b c α ∈ closure (Set.range fun k : ℤ => axisRot a b c ((k : ℝ) * θ)) := by
  set f : ℝ → Matrix (Fin 2) (Fin 2) ℂ := axisRot a b c with hf
  have hdense : Dense (AddSubgroup.closure {θ, 4 * π} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  have hsub : f '' (AddSubgroup.closure {θ, 4 * π} : Set ℝ)
      ⊆ Set.range fun k : ℤ => f ((k : ℝ) * θ) := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨k, m, hkm⟩ := AddSubgroup.mem_closure_pair.mp ht
    refine ⟨k, ?_⟩
    rw [← hkm, zsmul_eq_mul, zsmul_eq_mul, hf]
    exact (axisRot_add_int_mul_four_pi a b c ((k : ℝ) * θ) m).symm
  have hcl : f '' closure (AddSubgroup.closure {θ, 4 * π} : Set ℝ)
      ⊆ closure (f '' (AddSubgroup.closure {θ, 4 * π} : Set ℝ)) :=
    image_closure_subset_closure_image (continuous_axisRot a b c)
  have hmem : f α ∈ f '' closure (AddSubgroup.closure {θ, 4 * π} : Set ℝ) := by
    refine ⟨α, ?_, rfl⟩
    rw [hdense.closure_eq]
    trivial
  exact closure_mono hsub (hcl hmem)

/-- For a unit axis, if a submonoid contains the rotations through `θ` and `-θ`, then it
contains the rotation through `k * θ` for every integer `k`. -/
theorem axisRot_int_mul_mem {K : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)} {a b c θ : ℝ}
    (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (hg : axisRot a b c θ ∈ K)
    (hg' : axisRot a b c (-θ) ∈ K) (k : ℤ) : axisRot a b c ((k : ℝ) * θ) ∈ K := by
  induction k using Int.induction_on with
  | zero =>
    simp only [Int.cast_zero, zero_mul, axisRot_zero]
    exact K.one_mem
  | succ n ih =>
    push_cast
    rw [show ((n : ℝ) + 1) * θ = (n : ℝ) * θ + θ by ring, axisRot_add hu]
    exact mul_mem (by push_cast at ih; exact ih) hg
  | pred n ih =>
    push_cast
    rw [show (-(n : ℝ) - 1) * θ = -(n : ℝ) * θ + -θ by ring, axisRot_add hu]
    exact mul_mem (by push_cast at ih; exact ih) hg'

/-- A closed submonoid containing rotations through `θ` and `-θ` about a unit axis contains
rotations through every real angle about that axis, provided `θ / (4 * π)` is irrational. -/
theorem axisRot_mem_of_irrational {K : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)}
    (hK : IsClosed (K : Set (Matrix (Fin 2) (Fin 2) ℂ))) {a b c θ : ℝ}
    (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (hirr : Irrational (θ / (4 * π)))
    (hg : axisRot a b c θ ∈ K) (hg' : axisRot a b c (-θ) ∈ K) (α : ℝ) :
    axisRot a b c α ∈ K := by
  refine hK.closure_subset_iff.mpr ?_ (mem_closure_range_axisRot_of_irrational hirr α)
  rintro y ⟨k, rfl⟩
  exact axisRot_int_mul_mem hu hg hg' k

/-- The vector `(Real.sqrt 2 / 2, 0, -(Real.sqrt 2 / 2))` has squared Euclidean length one. -/
theorem wAxis_unit : (Real.sqrt 2 / 2) ^ 2 + (0 : ℝ) ^ 2 + (-(Real.sqrt 2 / 2)) ^ 2 = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h2]

/-- The vector `(Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2)` has squared Euclidean length one. -/
theorem uAxis_unit : (Real.sqrt 2 / 2) ^ 2 + (0 : ℝ) ^ 2 + (Real.sqrt 2 / 2) ^ 2 = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h2]

/-- The multiplicative inverse of the real square root of two is `Real.sqrt 2 / 2`. -/
theorem sqrt_two_inv_eq : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  linarith [h2]

/-- Expresses the Hadamard matrix as `Complex.I` times the matrix `su2 0 ((Real.sqrt 2)⁻¹) 0
((Real.sqrt 2)⁻¹)`. -/
theorem hGateM_eq_smul_su2 :
    hGateM = Complex.I • su2 0 ((Real.sqrt 2)⁻¹) 0 ((Real.sqrt 2)⁻¹) := by
  rw [hGateM, su2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff]

/-- The product of a rotation through `π` about `(htA, htB, htA)` with `hGateM` equals
`Complex.I` times the rotation through `wAngle` about `(Real.sqrt 2 / 2, 0, -(Real.sqrt 2 /
2))`. -/
theorem axisRot_htAxis_pi_mul_hGateM :
    axisRot htA htB htA π * hGateM
      = Complex.I • axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) wAngle := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [hGateM_eq_smul_su2, sqrt_two_inv_eq, axisRot, axisRot, Real.cos_pi_div_two,
    Real.sin_pi_div_two, cos_wAngle_half, sin_wAngle_half, wHalfCos, Matrix.mul_smul, su2_mul]
  congr 1
  congr 1 <;> nlinarith [h2]

/-- The matrix `htht`, defined by the product T H T H, belongs to the Clifford-T submonoid. -/
theorem htht_mem : htht ∈ cliffordT := by
  rw [htht]
  exact mul_mem (mul_mem (mul_mem tGateM_mem hGateM_mem) tGateM_mem) hGateM_mem

/-- The product `hGateM * tGateM ^ 7 * hGateM * tGateM ^ 7` belongs to the Clifford-T submonoid. -/
theorem hthtInv_mem : hGateM * tGateM ^ 7 * hGateM * tGateM ^ 7 ∈ cliffordT :=
  mul_mem (mul_mem (mul_mem hGateM_mem (pow_mem tGateM_mem 7)) hGateM_mem)
    (pow_mem tGateM_mem 7)

/-- Multiplying `htht` on the right by `hGateM * tGateM ^ 7 * hGateM * tGateM ^ 7` gives the
identity matrix. -/
theorem htht_mul_inv : htht * (hGateM * tGateM ^ 7 * hGateM * tGateM ^ 7) = 1 := by
  have hh : hGateM * hGateM = 1 := hGateM_mul_self
  have ht8 : tGateM * tGateM ^ 7 = 1 := by
    rw [← pow_succ' tGateM 7, show 7 + 1 = 8 from rfl]
    exact tGateM_pow_eight
  rw [htht]
  simp only [mul_assoc]
  rw [← mul_assoc hGateM hGateM, hh, one_mul, ← mul_assoc tGateM (tGateM ^ 7), ht8, one_mul,
    ← mul_assoc hGateM hGateM, hh, one_mul]
  exact ht8

/-- The rotation through `8 * htAngle` about `(htA, htB, htA)` is `htht ^ 8`, where the eighth
power removes the scalar phase. -/
theorem axisRot_htAxis_eight : axisRot htA htB htA (8 * htAngle) = htht ^ 8 := by
  rw [htht_pow, tPhase_pow_eight, one_smul]
  norm_num

/-- The rotation through `8 * htAngle` about `(htA, htB, htA)` belongs to `cliffordTLim`. -/
theorem axisRot_htAxis_eight_mem : axisRot htA htB htA (8 * htAngle) ∈ cliffordTLim := by
  rw [axisRot_htAxis_eight]
  exact cliffordT_le_lim (pow_mem htht_mem 8)

/-- The rotation through `-(8 * htAngle)` about `(htA, htB, htA)` belongs to `cliffordTLim`. -/
theorem axisRot_htAxis_neg_eight_mem :
    axisRot htA htB htA (-(8 * htAngle)) ∈ cliffordTLim := by
  have h1 : axisRot htA htB htA (8 * htAngle)
      * (hGateM * tGateM ^ 7 * hGateM * tGateM ^ 7) ^ 8 = 1 := by
    rw [axisRot_htAxis_eight]
    exact pow_mul_pow_eq_one htht_mul_inv 8
  have h2 : axisRot htA htB htA (8 * htAngle) * axisRot htA htB htA (-(8 * htAngle)) = 1 := by
    rw [← axisRot_add htAxis_unit]
    simp
  rw [(Matrix.inv_eq_right_inv h2).symm.trans (Matrix.inv_eq_right_inv h1)]
  exact cliffordT_le_lim (pow_mem hthtInv_mem 8)

/-- The ratio `(8 * htAngle) / (4 * π)` is irrational. -/
theorem irrational_eight_htAngle : Irrational ((8 * htAngle) / (4 * π)) := by
  rintro ⟨q, hq⟩
  refine irrational_htAngle_div_four_pi ⟨q / 8, ?_⟩
  have hpi : π ≠ 0 := Real.pi_ne_zero
  push_cast at hq ⊢
  field_simp at hq ⊢
  linarith [hq]

/-- Every rotation through a real angle about `(htA, htB, htA)` belongs to the topological
closure `cliffordTLim`. -/
theorem axisRot_htAxis_mem (α : ℝ) : axisRot htA htB htA α ∈ cliffordTLim :=
  axisRot_mem_of_irrational isClosed_cliffordTLim htAxis_unit irrational_eight_htAngle
    axisRot_htAxis_eight_mem axisRot_htAxis_neg_eight_mem α

/-- The product `axisRot htA htB htA π * hGateM` belongs to `cliffordTLim`. -/
theorem piRot_mul_hGateM_mem : axisRot htA htB htA π * hGateM ∈ cliffordTLim :=
  mul_mem (axisRot_htAxis_mem π) (cliffordT_le_lim hGateM_mem)

/-- The product `hGateM * axisRot htA htB htA (-π)` belongs to `cliffordTLim`. -/
theorem hGateM_mul_piRot_mem : hGateM * axisRot htA htB htA (-π) ∈ cliffordTLim :=
  mul_mem (cliffordT_le_lim hGateM_mem) (axisRot_htAxis_mem (-π))

/-- The product `hGateM * axisRot htA htB htA (-π)` is a right inverse of `axisRot htA htB htA π
* hGateM`. -/
theorem piRot_mul_hGateM_mul_inv :
    (axisRot htA htB htA π * hGateM) * (hGateM * axisRot htA htB htA (-π)) = 1 := by
  calc (axisRot htA htB htA π * hGateM) * (hGateM * axisRot htA htB htA (-π))
      = axisRot htA htB htA π * (hGateM * hGateM) * axisRot htA htB htA (-π) := by
        simp only [mul_assoc]
    _ = 1 := by
        rw [hGateM_mul_self, mul_one, ← axisRot_add htAxis_unit]
        simp

/-- The fourth power of `axisRot htA htB htA π * hGateM` is the rotation through `4 * wAngle`
about `(Real.sqrt 2 / 2, 0, -(Real.sqrt 2 / 2))`. -/
theorem axisRot_wAxis_four :
    (axisRot htA htB htA π * hGateM) ^ 4
      = axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (4 * wAngle) := by
  rw [axisRot_htAxis_pi_mul_hGateM, smul_pow,
    show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num,
    one_smul, show (4 : ℝ) * wAngle = ((4 : ℕ) : ℝ) * wAngle by norm_num,
    axisRot_nat_mul wAxis_unit]

/-- The ratio `(4 * wAngle) / (4 * π)` is irrational. -/
theorem irrational_four_wAngle : Irrational ((4 * wAngle) / (4 * π)) := by
  rintro ⟨q, hq⟩
  refine irrational_wAngle_div_four_pi ⟨q / 4, ?_⟩
  have hpi : π ≠ 0 := Real.pi_ne_zero
  push_cast at hq ⊢
  field_simp at hq ⊢
  linarith [hq]

/-- Every rotation through a real angle about `(Real.sqrt 2 / 2, 0, -(Real.sqrt 2 / 2))` belongs
to `cliffordTLim`. -/
theorem axisRot_wAxis_mem (α : ℝ) :
    axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) α ∈ cliffordTLim := by
  refine axisRot_mem_of_irrational isClosed_cliffordTLim wAxis_unit irrational_four_wAngle ?_ ?_ α
  · rw [← axisRot_wAxis_four]
    exact pow_mem piRot_mul_hGateM_mem 4
  · have h1 : axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (4 * wAngle)
        * (hGateM * axisRot htA htB htA (-π)) ^ 4 = 1 := by
      rw [← axisRot_wAxis_four]
      exact pow_mul_pow_eq_one piRot_mul_hGateM_mul_inv 4
    have h2 : axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (4 * wAngle)
        * axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (-(4 * wAngle)) = 1 := by
      rw [← axisRot_add wAxis_unit]
      simp
    rw [(Matrix.inv_eq_right_inv h2).symm.trans (Matrix.inv_eq_right_inv h1)]
    exact pow_mem hGateM_mul_piRot_mem 4

/-- This is the matrix `tGateM ^ 4`, which is the Pauli Z matrix. -/
noncomputable def zGateM : Matrix (Fin 2) (Fin 2) ℂ := tGateM ^ 4

/-- The fourth power of `tPhase` is negative one. -/
theorem tPhase_pow_four : tPhase ^ 4 = -1 := by
  have h : tPhase ^ 2 = Complex.I := by
    rw [pow_two]
    exact tPhase_sq
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, Complex.I_sq]

/-- The matrix `zGateM` is the diagonal matrix with entries one and negative one. -/
theorem zGateM_eq : zGateM = !![1, 0; 0, -1] := by
  rw [zGateM, tGateM_pow, tPhase_pow_four]

/-- Conjugating `su2 w x y z` by `zGateM` negates the coordinates `x` and `y` while preserving
`w` and `z`. -/
theorem zGateM_conj_su2 (w x y z : ℝ) :
    zGateM * su2 w x y z * zGateM = su2 w (-x) (-y) z := by
  rw [zGateM_eq, su2, su2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

/-- Conjugating the rotation through `-α` about `(Real.sqrt 2 / 2, 0, -(Real.sqrt 2 / 2))` by
`zGateM` gives the rotation through `α` about `(Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2)`. -/
theorem zGateM_conj_axisRot (α : ℝ) :
    zGateM * axisRot (Real.sqrt 2 / 2) 0 (-(Real.sqrt 2 / 2)) (-α) * zGateM
      = axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) α := by
  rw [axisRot, zGateM_conj_su2, axisRot, show -α / 2 = -(α / 2) by ring, Real.cos_neg,
    Real.sin_neg]
  congr 1 <;> ring

/-- Every rotation through a real angle about `(Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2)` belongs to
`cliffordTLim`. -/
theorem axisRot_uAxis_mem (α : ℝ) :
    axisRot (Real.sqrt 2 / 2) 0 (Real.sqrt 2 / 2) α ∈ cliffordTLim := by
  have hz : zGateM ∈ cliffordTLim := cliffordT_le_lim (pow_mem tGateM_mem 4)
  rw [← zGateM_conj_axisRot α]
  exact mul_mem (mul_mem hz (axisRot_wAxis_mem (-α))) hz

/-- Every two-dimensional complex unitary matrix with determinant one lies in the topological
closure of the Clifford-T submonoid. This gives the SU(2) density statement underlying
single-qubit universality [NielsenChuang2010]. -/
theorem det_one_mem_cliffordTLim {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) : U ∈ cliffordTLim := by
  obtain ⟨β, γ, δ, hU'⟩ := exists_euler_two_axes hU hdet
  rw [hU']
  exact mul_mem (mul_mem (axisRot_uAxis_mem β) (axisRot_wAxis_mem γ)) (axisRot_uAxis_mem δ)

/-- For every two-dimensional complex unitary matrix `U`, there is a real phase `φ` such that
`Euler.expI φ • U` lies in the closure of the Clifford-T submonoid. This is universality up
to global phase, as discussed in [NielsenChuang2010]. -/
theorem exists_phase_mem_cliffordTLim {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ φ : ℝ, Euler.expI φ • U ∈ cliffordTLim := by
  obtain ⟨α, β, γ, δ, hU'⟩ := Euler.exists_euler hU
  refine ⟨-α, ?_⟩
  have hW : Euler.rzMat β * Euler.ryMat γ * Euler.rzMat δ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mul_mem (mul_mem (Euler.rzMat_mem_unitaryGroup β) (Euler.ryMat_mem_unitaryGroup γ))
      (Euler.rzMat_mem_unitaryGroup δ)
  rw [hU', smul_smul, ← Euler.expI_add, show -α + α = 0 by ring, Euler.expI_zero, one_smul]
  exact det_one_mem_cliffordTLim hW (Euler.rz_ry_rz_det β γ δ)

end SU2

end QuantumInfo

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
