/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.SU2Rotation
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Balanced Commutators in SU(2)

This module constructs exact balanced commutators for determinant-one unitary matrices of size
two, as used in the Solovay-Kitaev construction [DawsonNielsen2006]. The matrices `skV` and
`skW` are rotations through the same angle about the x and y axes, and `skComm` is their group
commutator. Explicit quaternion coordinates give its distance from the identity in the L2
operator norm.

Quaternion parametrization and unitary conjugation extend this construction to every SU(2)
matrix. The theorem `exists_commutator_of_det_one` produces determinant-one unitary factors V
and W with U = V W V* W* and with each factor's distance from the identity bounded by √2 times
the square root of the distance of U from the identity.

## Main statements

* `norm_su2_sub_one` expresses the distance from the identity using the scalar quaternion
  coordinate.
* `exists_skComm_norm_eq` realizes every distance in [0, 2] by the explicit commutator family,
  with bounds on both factors.
* `norm_conj_sub_one` and `conj_groupCommutator` transport distances and commutators through
  unitary conjugation.
* `exists_commutator_of_det_one` gives an exact commutator decomposition with quantitative
  bounds on the factors.

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006] C. M. Dawson and M. A. Nielsen, The
  Solovay-Kitaev algorithm.
-/

set_option warningAsError false

section

open Matrix

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2

/-- The adjoint of `su2 w x y z` keeps the scalar coordinate w and negates the three vector
coordinates. -/
theorem su2_star (w x y z : ℝ) : star (su2 w x y z) = su2 w (-x) (-y) (-z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Matrix.star_apply, Complex.ext_iff]

/-- If the four real quaternion coordinates have squared sum one, multiplying `su2 w x y z` on
the left by its adjoint gives the identity. -/
theorem su2_star_mul_self {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    star (su2 w x y z) * su2 w x y z = 1 := by
  rw [su2_star, su2_mul, ← su2_one]
  congr 1 <;> (first | linear_combination hu | linear_combination -hu | ring)

/-- The sum of `su2 w x y z` and its adjoint is 2w times the identity matrix. -/
theorem su2_add_star (w x y z : ℝ) :
    su2 w x y z + star (su2 w x y z) = ((2 * w : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [su2_star]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Complex.ext_iff] <;> ring

/-- For unit quaternion coordinates, the adjoint square of `su2 w x y z - 1` is (2 - 2w) times
the identity matrix. -/
theorem star_su2_sub_one_mul_self {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    star (su2 w x y z - 1) * (su2 w x y z - 1)
      = ((2 - 2 * w : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have key : star (su2 w x y z - 1) * (su2 w x y z - 1)
      = star (su2 w x y z) * su2 w x y z + 1 - (su2 w x y z + star (su2 w x y z)) := by
    rw [star_sub, star_one]
    noncomm_ring
  rw [key, su2_star_mul_self hu, su2_add_star]
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℂ) + 1 = ((2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    push_cast
    rw [two_smul]
  rw [h2, ← sub_smul]
  congr 1
  push_cast
  ring

/-- For unit quaternion coordinates, the L2 operator norm of `su2 w x y z - 1` equals √(2 - 2w). -/
theorem norm_su2_sub_one {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    ‖su2 w x y z - 1‖ = Real.sqrt (2 - 2 * w) := by
  have hw : w ^ 2 ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hw' : w ≤ 1 := by nlinarith
  have hnn : (0 : ℝ) ≤ 2 - 2 * w := by linarith
  have hsq : ‖su2 w x y z - 1‖ * ‖su2 w x y z - 1‖ = 2 - 2 * w := by
    rw [← CStarRing.norm_star_mul_self, star_su2_sub_one_mul_self hu, norm_smul, norm_one,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [← Real.sqrt_mul_self (norm_nonneg (su2 w x y z - 1)), hsq]

/-- A rotation through angle θ about a unit axis has L2 operator distance √(2 - 2 cos(θ/2)) from
the identity. -/
theorem norm_axisRot_sub_one {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    ‖axisRot a b c θ - 1‖ = Real.sqrt (2 - 2 * Real.cos (θ / 2)) := by
  rw [axisRot]
  refine norm_su2_sub_one ?_
  have h := Real.sin_sq_add_cos_sq (θ / 2)
  nlinarith [hu, h]

/-- The matrix `skV φ` is the rotation `axisRot 1 0 0 φ` about the x axis, used as the first
factor of the explicit balanced commutator. -/
noncomputable def skV (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 1 0 0 φ

/-- The matrix `skW φ` is the rotation `axisRot 0 1 0 φ` about the y axis, used as the second
factor of the explicit balanced commutator. -/
noncomputable def skW (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 0 1 0 φ

/-- The matrix `skComm φ` is the group commutator `skV φ * skW φ * star (skV φ) * star (skW φ)`
of equal-angle x-axis and y-axis rotations. -/
noncomputable def skComm (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  skV φ * skW φ * star (skV φ) * star (skW φ)

/-- The quaternion coordinates of `skComm φ` are (1 - 2s⁴, 2cs³, -2cs³, 2c²s²), where c =
cos(φ/2) and s = sin(φ/2). -/
theorem skComm_eq (φ : ℝ) :
    skComm φ = su2 (1 - 2 * Real.sin (φ / 2) ^ 4)
      (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)
      (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3))
      (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) := by
  rw [skComm, skV, skW, axisRot, axisRot, su2_star, su2_star, su2_mul, su2_mul, su2_mul]
  have h := Real.sin_sq_add_cos_sq (φ / 2)
  set c := Real.cos (φ / 2) with hc
  set s := Real.sin (φ / 2) with hs
  congr 1
  · linear_combination (s ^ 2 + c ^ 2 + 1) * h
  · ring
  · ring
  · ring

/-- The four explicit quaternion coordinates of `skComm φ` have squared sum one for every real
φ. -/
theorem skComm_unit (φ : ℝ) :
    (1 - 2 * Real.sin (φ / 2) ^ 4) ^ 2 + (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) ^ 2
        + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)) ^ 2
        + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq (φ / 2)
  set c := Real.cos (φ / 2) with hc
  set s := Real.sin (φ / 2) with hs
  linear_combination (4 * s ^ 4 * (s ^ 2 + c ^ 2 + 1)) * h

/-- The L2 operator distance of the explicit commutator `skComm φ` from the identity is exactly
2 sin²(φ/2). -/
theorem norm_skComm_sub_one (φ : ℝ) : ‖skComm φ - 1‖ = 2 * Real.sin (φ / 2) ^ 2 := by
  rw [skComm_eq, norm_su2_sub_one (skComm_unit φ),
    show (2 : ℝ) - 2 * (1 - 2 * Real.sin (φ / 2) ^ 4)
      = (2 * Real.sin (φ / 2) ^ 2) ^ 2 from by ring]
  exact Real.sqrt_sq (by positivity)

/-- The L2 operator distance of the x-axis rotation `skV φ` from the identity is √(2 - 2
cos(φ/2)). -/
theorem norm_skV_sub_one (φ : ℝ) :
    ‖skV φ - 1‖ = Real.sqrt (2 - 2 * Real.cos (φ / 2)) := by
  rw [skV]
  exact norm_axisRot_sub_one (by norm_num) φ

/-- The L2 operator distance of the y-axis rotation `skW φ` from the identity is √(2 - 2
cos(φ/2)). -/
theorem norm_skW_sub_one (φ : ℝ) :
    ‖skW φ - 1‖ = Real.sqrt (2 - 2 * Real.cos (φ / 2)) := by
  rw [skW]
  exact norm_axisRot_sub_one (by norm_num) φ

/-- For 0 ≤ φ ≤ π, the distance of `skV φ` from the identity is at most √2 times the square root
of the distance of `skComm φ` from the identity. -/
theorem norm_skV_sub_one_le {φ : ℝ} (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) :
    ‖skV φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖skComm φ - 1‖ := by
  have hpi' := Real.pi_pos
  have hs : 0 ≤ Real.sin (φ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hc : 0 ≤ Real.cos (φ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hc1 : Real.cos (φ / 2) ≤ 1 := Real.cos_le_one _
  have hsc : Real.sin (φ / 2) ^ 2 = 1 - Real.cos (φ / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (φ / 2)]
  rw [norm_skV_sub_one, norm_skComm_sub_one, ← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  rw [show (2 : ℝ) * (2 * Real.sin (φ / 2) ^ 2) = 4 * Real.sin (φ / 2) ^ 2 from by ring, hsc]
  nlinarith [hc, hc1]

/-- For 0 ≤ φ ≤ π, the distance of `skW φ` from the identity is at most √2 times the square root
of the distance of `skComm φ` from the identity. -/
theorem norm_skW_sub_one_le {φ : ℝ} (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) :
    ‖skW φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖skComm φ - 1‖ := by
  rw [norm_skW_sub_one, ← norm_skV_sub_one]
  exact norm_skV_sub_one_le h0 hpi

/-- Every ε in [0, 2] is the distance from the identity of `skComm φ` for some φ in [0, π]. Both
`skV φ` and `skW φ` are within √2 √ε of the identity. -/
theorem exists_skComm_norm_eq {ε : ℝ} (h0 : 0 ≤ ε) (h2 : ε ≤ 2) :
    ∃ φ : ℝ, 0 ≤ φ ∧ φ ≤ Real.pi ∧ ‖skComm φ - 1‖ = ε ∧
      ‖skV φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε ∧ ‖skW φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε := by
  have hhalf : Real.sqrt (ε / 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hnn : 0 ≤ Real.sqrt (ε / 2) := Real.sqrt_nonneg _
  have harc0 : 0 ≤ Real.arcsin (Real.sqrt (ε / 2)) := Real.arcsin_nonneg.2 hnn
  have harc1 : Real.arcsin (Real.sqrt (ε / 2)) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have h0φ : (0 : ℝ) ≤ 2 * Real.arcsin (Real.sqrt (ε / 2)) := by linarith
  have hpiφ : 2 * Real.arcsin (Real.sqrt (ε / 2)) ≤ Real.pi := by linarith
  have hsin : Real.sin (2 * Real.arcsin (Real.sqrt (ε / 2)) / 2) = Real.sqrt (ε / 2) := by
    rw [show 2 * Real.arcsin (Real.sqrt (ε / 2)) / 2 = Real.arcsin (Real.sqrt (ε / 2)) from by
      ring]
    exact Real.sin_arcsin (by linarith) hhalf
  have hnorm : ‖skComm (2 * Real.arcsin (Real.sqrt (ε / 2))) - 1‖ = ε := by
    rw [norm_skComm_sub_one, hsin, Real.sq_sqrt (by linarith)]
    ring
  refine ⟨2 * Real.arcsin (Real.sqrt (ε / 2)), h0φ, hpiφ, hnorm, ?_, ?_⟩
  · have hV := norm_skV_sub_one_le h0φ hpiφ
    rwa [hnorm] at hV
  · have hW := norm_skW_sub_one_le h0φ hpiφ
    rwa [hnorm] at hW

/-- Every unitary matrix of size two with determinant one has the form `su2 w x y z`, with real
coordinates whose squared sum is one. -/
theorem exists_su2_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ w x y z : ℝ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1 ∧ U = su2 w x y z := by
  have hstar : U⁻¹ = star U :=
    Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hU)
  have hadj : U⁻¹ = U.adjugate := by
    rw [Matrix.inv_def, hdet]
    simp
  have hkey : star U = !![U 1 1, -U 0 1; -U 1 0, U 0 0] := by
    rw [← hstar, hadj, Matrix.adjugate_fin_two]
  have h11 : U 1 1 = starRingEnd ℂ (U 0 0) := by
    have h : (star U) 0 0
        = (!![U 1 1, -U 0 1; -U 1 0, U 0 0] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [hkey]
    simp [Matrix.star_apply] at h
    linear_combination -h
  have h10 : U 1 0 = -starRingEnd ℂ (U 0 1) := by
    have h : (star U) 1 0
        = (!![U 1 1, -U 0 1; -U 1 0, U 0 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by rw [hkey]
    simp [Matrix.star_apply] at h
    linear_combination h
  have hrow : U 0 0 * starRingEnd ℂ (U 0 0) + U 0 1 * starRingEnd ℂ (U 0 1) = 1 := by
    have h : (U * star U) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
      rw [Unitary.mul_star_self_of_mem hU]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h
    linear_combination h
  have hrow' : Complex.normSq (U 0 0) + Complex.normSq (U 0 1) = 1 := by
    rw [Complex.mul_conj, Complex.mul_conj] at hrow
    exact_mod_cast hrow
  refine ⟨(U 0 0).re, -(U 0 1).im, -(U 0 1).re, -(U 0 0).im, ?_, ?_⟩
  · simp only [Complex.normSq_apply] at hrow'
    nlinarith [hrow']
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [su2, h11, h10, Complex.ext_iff]

/-- Conjugation by `su2 0 m₁ m₂ m₃`, for a unit vector m, preserves the scalar coordinate and
maps the vector coordinate v to 2(m · v)m - v. -/
theorem su2_conj_pure {m₁ m₂ m₃ : ℝ} (hm : m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2 = 1) (w x y z : ℝ) :
    su2 0 m₁ m₂ m₃ * su2 w x y z * star (su2 0 m₁ m₂ m₃)
      = su2 w (2 * (m₁ * x + m₂ * y + m₃ * z) * m₁ - x)
          (2 * (m₁ * x + m₂ * y + m₃ * z) * m₂ - y)
          (2 * (m₁ * x + m₂ * y + m₃ * z) * m₃ - z) := by
  rw [su2_star, su2_mul, su2_mul]
  congr 1
  · linear_combination w * hm
  · linear_combination (-x) * hm
  · linear_combination (-y) * hm
  · linear_combination (-z) * hm

/-- Real quaternion coordinates with squared sum one define an element of the unitary submonoid
of complex matrices of size two. -/
theorem su2_mem_unitary {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    su2 w x y z ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  refine Unitary.mem_iff.2 ⟨su2_star_mul_self hu, ?_⟩
  rw [su2_star, su2_mul, ← su2_one]
  congr 1
  · linear_combination hu
  · ring
  · ring
  · ring

/-- For a unit real axis, `axisRot a b c θ` belongs to the unitary submonoid for every real
angle θ. -/
theorem axisRot_mem_unitary {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    axisRot a b c θ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [axisRot]
  refine su2_mem_unitary ?_
  have h := Real.sin_sq_add_cos_sq (θ / 2)
  nlinarith [hu, h]

/-- Two real vectors in three dimensions with equal squared length and nonzero sum are related
by v ↦ 2(m · v)m - v for some unit vector m. The unit vector can be taken along their
bisector. -/
theorem bisector_reflect {p₁ p₂ p₃ n₁ n₂ n₃ ρ : ℝ} (hp : p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 = ρ)
    (hn : n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = ρ)
    (hsum : 0 < (p₁ + n₁) ^ 2 + (p₂ + n₂) ^ 2 + (p₃ + n₃) ^ 2) :
    ∃ m₁ m₂ m₃ : ℝ, m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2 = 1 ∧
      2 * (m₁ * p₁ + m₂ * p₂ + m₃ * p₃) * m₁ - p₁ = n₁ ∧
      2 * (m₁ * p₁ + m₂ * p₂ + m₃ * p₃) * m₂ - p₂ = n₂ ∧
      2 * (m₁ * p₁ + m₂ * p₂ + m₃ * p₃) * m₃ - p₃ = n₃ := by
  obtain ⟨r, hrpos, hr⟩ : ∃ r : ℝ, 0 < r ∧
      r ^ 2 = (p₁ + n₁) ^ 2 + (p₂ + n₂) ^ 2 + (p₃ + n₃) ^ 2 :=
    ⟨Real.sqrt ((p₁ + n₁) ^ 2 + (p₂ + n₂) ^ 2 + (p₃ + n₃) ^ 2), Real.sqrt_pos.2 hsum,
      Real.sq_sqrt (le_of_lt hsum)⟩
  have hrne : r ≠ 0 := ne_of_gt hrpos
  refine ⟨(p₁ + n₁) / r, (p₂ + n₂) / r, (p₃ + n₃) / r, ?_, ?_, ?_, ?_⟩
  · field_simp
    rw [hr]
  · field_simp
    rw [hr]
    linear_combination (p₁ + n₁) * hp - (p₁ + n₁) * hn
  · field_simp
    rw [hr]
    linear_combination (p₂ + n₂) * hp - (p₂ + n₂) * hn
  · field_simp
    rw [hr]
    linear_combination (p₃ + n₃) * hp - (p₃ + n₃) * hn

/-- In a C-star ring, conjugation by a unitary element preserves the norm of the difference from
the identity. -/
theorem norm_conj_sub_one {E : Type*} [NormedRing E] [StarRing E] [CStarRing E] {S : E}
    (hS : S ∈ unitary E) (K : E) : ‖S * K * star S - 1‖ = ‖K - 1‖ := by
  have hexp : S * (K - 1) * star S = S * K * star S - S * star S := by noncomm_ring
  have h1 : S * K * star S - 1 = S * (K - 1) * star S := by
    rw [hexp, Unitary.mul_star_self_of_mem hS]
  rw [h1, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hS),
    CStarRing.norm_mem_unitary_mul _ hS]

/-- Simultaneous conjugation of V and W by a unitary S carries `V * W * star V * star W` to its
conjugate by S. -/
theorem conj_groupCommutator {E : Type*} [Monoid E] [StarMul E] {S : E} (hS : S ∈ unitary E)
    (V W : E) :
    (S * V * star S) * (S * W * star S) * star (S * V * star S) * star (S * W * star S)
      = S * (V * W * star V * star W) * star S := by
  have hss : star S * S = 1 := Unitary.star_mul_self_of_mem hS
  have hsv : star (S * V * star S) = S * star V * star S := by
    simp only [star_mul, star_star]
    noncomm_ring
  have hsw : star (S * W * star S) = S * star W * star S := by
    simp only [star_mul, star_star]
    noncomm_ring
  rw [hsv, hsw]
  calc S * V * star S * (S * W * star S) * (S * star V * star S) * (S * star W * star S)
      = S * V * (star S * S) * W * (star S * S) * star V * (star S * S) * star W * star S := by
        noncomm_ring
    _ = S * (V * W * star V * star W) * star S := by
        rw [hss]
        noncomm_ring

/-- Taking the adjoint of `V * W * star V * star W` gives `W * V * star W * star V`. -/
theorem star_groupCommutator {E : Type*} [Monoid E] [StarMul E] (V W : E) :
    star (V * W * star V * star W) = W * V * star W * star V := by
  simp only [star_mul, star_star]
  noncomm_ring

/-- Conjugation by a unitary complex matrix of size two preserves the determinant of every
complex matrix of size two. -/
theorem det_conj_of_mem_unitary {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (S * X * star S).det = X.det := by
  have hone : S.det * (star S).det = 1 := by
    rw [← Matrix.det_mul, Unitary.mul_star_self_of_mem hS, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  calc S.det * X.det * (star S).det = S.det * (star S).det * X.det := by ring
    _ = X.det := by rw [hone, one_mul]

/-- Every determinant-one unitary matrix of size two is exactly `V * W * star V * star W` for
determinant-one unitary V and W, each within √2 times the square root of the target's
distance from the identity. This gives the SU(2) balanced commutator construction used in
[DawsonNielsen2006]. -/
theorem exists_commutator_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) (hdet : U.det = 1) :
    ∃ V W : Matrix (Fin 2) (Fin 2) ℂ,
      V ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧ W ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧
      V.det = 1 ∧ W.det = 1 ∧
      U = V * W * star V * star W ∧
      ‖V - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖U - 1‖ ∧
      ‖W - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖U - 1‖ := by
  obtain ⟨w, x, y, z, hunit, hUeq⟩ := exists_su2_of_det_one hU hdet
  have hw1 : w ≤ 1 := by nlinarith [hunit, sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hwm1 : -1 ≤ w := by nlinarith [hunit, sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hnn : (0 : ℝ) ≤ 2 - 2 * w := by linarith
  have hnormU : ‖U - 1‖ = Real.sqrt (2 - 2 * w) := by
    rw [hUeq]
    exact norm_su2_sub_one hunit
  have hε0 : (0 : ℝ) ≤ ‖U - 1‖ := norm_nonneg _
  have hε2 : ‖U - 1‖ ≤ 2 := by
    rw [hnormU]
    calc Real.sqrt (2 - 2 * w) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]
          exact Real.sqrt_sq (by norm_num)
  obtain ⟨φ, hφ0, hφpi, hφnorm, hVb, hWb⟩ := exists_skComm_norm_eq hε0 hε2

  have h2s : 2 * Real.sin (φ / 2) ^ 2 = ‖U - 1‖ := by
    rw [← hφnorm, norm_skComm_sub_one]
  have hsq : (2 * Real.sin (φ / 2) ^ 2) ^ 2 = 2 - 2 * w := by
    rw [h2s, hnormU, Real.sq_sqrt hnn]
  have hw' : w = 1 - 2 * Real.sin (φ / 2) ^ 4 := by nlinarith [hsq]

  have hKeq : skComm φ = su2 w (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)
      (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3))
      (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) := by
    rw [skComm_eq, hw']
  have hKunit := skComm_unit φ
  rw [← hw'] at hKunit

  have hlenU : x ^ 2 + y ^ 2 + z ^ 2 = 1 - w ^ 2 := by linarith [hunit]
  have hlenK : (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) ^ 2
      + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)) ^ 2
      + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) ^ 2 = 1 - w ^ 2 := by
    nlinarith [hKunit]
  have hVu : skV φ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [skV]; exact axisRot_mem_unitary (by norm_num) φ
  have hWu : skW φ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [skW]; exact axisRot_mem_unitary (by norm_num) φ
  by_cases hopp : (0 : ℝ) < (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2
      + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2
      + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2
  · obtain ⟨m₁, m₂, m₃, hm, hr₁, hr₂, hr₃⟩ := bisector_reflect hlenK hlenU hopp
    have hSu : su2 0 m₁ m₂ m₃ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
      su2_mem_unitary (by linarith)
    have hconj : su2 0 m₁ m₂ m₃ * skComm φ * star (su2 0 m₁ m₂ m₃) = U := by
      rw [hKeq, su2_conj_pure hm, hUeq, hr₁, hr₂, hr₃]
    refine ⟨su2 0 m₁ m₂ m₃ * skV φ * star (su2 0 m₁ m₂ m₃),
      su2 0 m₁ m₂ m₃ * skW φ * star (su2 0 m₁ m₂ m₃), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_mem (mul_mem hSu hVu) (Unitary.star_mem hSu)
    · exact mul_mem (mul_mem hSu hWu) (Unitary.star_mem hSu)
    · rw [det_conj_of_mem_unitary hSu, skV, axisRot_det (by norm_num)]
    · rw [det_conj_of_mem_unitary hSu, skW, axisRot_det (by norm_num)]
    · rw [conj_groupCommutator hSu, ← skComm, hconj]
    · rw [norm_conj_sub_one hSu]
      exact hVb
    · rw [norm_conj_sub_one hSu]
      exact hWb
  · have hzero : (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2
        + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2
        + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2 = 0 := by
      have hge : (0 : ℝ) ≤ (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2
          + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2
          + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2 := by positivity
      linarith [not_lt.1 hopp]
    have hsq1 : (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2 = 0 := by
      linarith [sq_nonneg (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y),
        sq_nonneg (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z),
        sq_nonneg (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x), hzero]
    have hsq2 : (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2 = 0 := by
      linarith [sq_nonneg (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y),
        sq_nonneg (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z),
        sq_nonneg (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x), hzero]
    have hsq3 : (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2 = 0 := by
      linarith [sq_nonneg (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y),
        sq_nonneg (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z),
        sq_nonneg (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x), hzero]
    have hx : x = -(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) := by
      have h := sq_eq_zero_iff.1 hsq1
      linarith
    have hy : y = 2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 := by
      have h := sq_eq_zero_iff.1 hsq2
      linarith
    have hz : z = -(2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) := by
      have h := sq_eq_zero_iff.1 hsq3
      linarith
    have hUstar : U = star (skComm φ) := by
      rw [hKeq, su2_star, hUeq, hx, hy, hz]
      congr 1
      ring
    refine ⟨skW φ, skV φ, hWu, hVu, ?_, ?_, ?_, ?_, ?_⟩
    · rw [skW, axisRot_det (by norm_num)]
    · rw [skV, axisRot_det (by norm_num)]
    · rw [hUstar, skComm, star_groupCommutator]
    · exact hWb
    · exact hVb

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2

end
