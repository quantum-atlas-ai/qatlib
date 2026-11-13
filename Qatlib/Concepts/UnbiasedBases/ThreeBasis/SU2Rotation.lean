/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.CliffordTAngle
import Mathlib.Topology.Instances.Matrix

/-!
# Axis rotations and the Clifford–T rotation angle

This module gives the real four-parameter matrix `su2` and the half-angle parametrization
`axisRot`, with multiplication, determinant, continuity, and periodicity formulas. It expresses
`htht` as a phase times a rotation about a fixed unit axis and proves density of its integer
angle multiples along that axis, supporting the gate approximation framework of
[NielsenChuang2010].

## Main statements

* `su2_mul`: gives the quaternion multiplication formula for the parametrized matrices.
* `htht_eq_axisRot`: identifies the phase and axis of the Clifford–T word.
* `mem_closure_range_axisRot`: every rotation about this axis lies in the closure of the
  integer-angle orbit.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

section

open Matrix
open scoped Real

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

namespace SU2

/-- The complex two-by-two matrix with diagonal entries `w - i z` and `w + i z` and off-diagonal
entries `-i (x - i y)` and `-i (x + i y)`. -/
noncomputable def su2 (w x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(w : ℂ) - Complex.I * z, -Complex.I * ((x : ℂ) - Complex.I * y);
     -Complex.I * ((x : ℂ) + Complex.I * y), (w : ℂ) + Complex.I * z]

/-- Multiplying two matrices `su2` combines their four real parameters by the quaternion
multiplication formula. -/
theorem su2_mul (w x y z w' x' y' z' : ℝ) :
    su2 w x y z * su2 w' x' y' z' =
      su2 (w * w' - x * x' - y * y' - z * z') (w * x' + x * w' + y * z' - z * y')
        (w * y' - x * z' + y * w' + z * x') (w * z' + x * y' - y * x' + z * w') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> constructor <;> ring

/-- The parameters `(1, 0, 0, 0)` give the identity matrix. -/
theorem su2_one : su2 1 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2]

/-- The determinant of `su2 w x y z` is the complex embedding of `w ^ 2 + x ^ 2 + y ^ 2 + z ^
2`. -/
theorem su2_det (w x y z : ℝ) : (su2 w x y z).det = ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ) := by
  rw [su2, Matrix.det_fin_two_of]
  push_cast
  simp [Complex.ext_iff, ← Complex.ofReal_pow]
  constructor <;> ring

/-- The trace of `su2 w x y z` equals twice `w`. -/
theorem su2_trace (w x y z : ℝ) : (su2 w x y z).trace = 2 * (w : ℂ) := by
  rw [su2, Matrix.trace_fin_two_of]
  ring

/-- The matrix `su2` with scalar component `cos (θ / 2)` and vector component `sin (θ / 2)`
times `(a, b, c)`. -/
noncomputable def axisRot (a b c θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  su2 (Real.cos (θ / 2)) (a * Real.sin (θ / 2)) (b * Real.sin (θ / 2)) (c * Real.sin (θ / 2))

/-- The axis parametrization at angle zero is the identity matrix for any axis parameters. -/
@[simp] theorem axisRot_zero (a b c : ℝ) : axisRot a b c 0 = 1 := by
  rw [axisRot]
  norm_num [su2_one]

/-- For a unit axis `(a, b, c)`, the matrix `axisRot a b c θ` has determinant one. -/
theorem axisRot_det {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    (axisRot a b c θ).det = 1 := by
  rw [axisRot, su2_det,
    show Real.cos (θ / 2) ^ 2 + (a * Real.sin (θ / 2)) ^ 2 + (b * Real.sin (θ / 2)) ^ 2
        + (c * Real.sin (θ / 2)) ^ 2 = 1 by
      linear_combination (Real.sin (θ / 2)) ^ 2 * hu + Real.sin_sq_add_cos_sq (θ / 2)]
  norm_num

/-- For a unit axis, adding rotation angles corresponds to multiplying their matrices. -/
theorem axisRot_add {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (α β : ℝ) :
    axisRot a b c (α + β) = axisRot a b c α * axisRot a b c β := by
  rw [axisRot, axisRot, axisRot, su2_mul]
  have hc : Real.cos ((α + β) / 2)
      = Real.cos (α / 2) * Real.cos (β / 2) - Real.sin (α / 2) * Real.sin (β / 2) := by
    rw [show (α + β) / 2 = α / 2 + β / 2 by ring, Real.cos_add]
  have hs : Real.sin ((α + β) / 2)
      = Real.sin (α / 2) * Real.cos (β / 2) + Real.cos (α / 2) * Real.sin (β / 2) := by
    rw [show (α + β) / 2 = α / 2 + β / 2 by ring, Real.sin_add]
  rw [hc, hs]
  congr 1
  · linear_combination (Real.sin (α / 2) * Real.sin (β / 2)) * hu
  · ring
  · ring
  · ring

/-- For a unit axis, multiplying the angle by a natural number corresponds to raising the
rotation matrix to that power. -/
theorem axisRot_nat_mul {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) (k : ℕ) :
    axisRot a b c ((k : ℝ) * θ) = axisRot a b c θ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← ih, ← axisRot_add hu]
    congr 1
    push_cast
    ring

/-- Adding any integer multiple of `4π` to the angle leaves `axisRot` unchanged. -/
theorem axisRot_add_int_mul_four_pi (a b c θ : ℝ) (k : ℤ) :
    axisRot a b c (θ + (k : ℝ) * (4 * π)) = axisRot a b c θ := by
  have h : (θ + (k : ℝ) * (4 * π)) / 2 = θ / 2 + (k : ℝ) * (2 * π) := by ring
  rw [axisRot, axisRot, h, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- For fixed axis parameters, `axisRot` is continuous in its angle. -/
theorem continuous_axisRot (a b c : ℝ) : Continuous (axisRot a b c) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [axisRot, su2] <;> fun_prop

open CliffordT

/-- The real square root of two is nonzero. -/
theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity

/-- The sine of `htHalfAngle`, used to normalize the rotation axis of `htht`. -/
noncomputable def htSin : ℝ := Real.sin htHalfAngle

/-- The real square root of two is strictly less than two. -/
theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2]

/-- The square of `htSin` equals `(10 - 4 * √2) / 16`. -/
theorem htSin_sq : htSin ^ 2 = (10 - 4 * Real.sqrt 2) / 16 := by
  have hu : Real.cos (π / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := cos_sq_pi_div_eight
  have hle : (0 : ℝ) ≤ 1 - (Real.cos (π / 8) ^ 2) ^ 2 := by
    rw [hu]
    nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2]
  rw [htSin, htHalfAngle, Real.sin_arccos, Real.sq_sqrt hle, hu]
  nlinarith [sq_sqrt_two]

/-- The number `htSin` is nonnegative. -/
theorem htSin_nonneg : 0 ≤ htSin := by
  rw [htSin, htHalfAngle, Real.sin_arccos]
  positivity

/-- The number `htSin` is strictly positive. -/
theorem htSin_pos : 0 < htSin := by
  have h2 : 0 < htSin ^ 2 := by
    rw [htSin_sq]
    nlinarith [sqrt_two_lt_two]
  rcases htSin_nonneg.lt_or_eq with h | h
  · exact h
  · rw [← h] at h2
    norm_num at h2

/-- The number `htSin` is nonzero. -/
theorem htSin_ne_zero : htSin ≠ 0 := ne_of_gt htSin_pos

/-- The axis coordinate `(√2 / 4) / htSin` of the rotation associated with `htht`. -/
noncomputable def htA : ℝ := Real.sqrt 2 / 4 / htSin

/-- The axis coordinate `((2 - √2) / 4) / htSin` of the rotation associated with `htht`. -/
noncomputable def htB : ℝ := (2 - Real.sqrt 2) / 4 / htSin

/-- Multiplying `htA` by `htSin` gives `√2 / 4`. -/
theorem htSin_mul_htA : htSin * htA = Real.sqrt 2 / 4 := by
  rw [htA, mul_comm, div_mul_cancel₀ _ htSin_ne_zero]

/-- Multiplying `htB` by `htSin` gives `(2 - √2) / 4`. -/
theorem htSin_mul_htB : htSin * htB = (2 - Real.sqrt 2) / 4 := by
  rw [htB, mul_comm, div_mul_cancel₀ _ htSin_ne_zero]

/-- The vector with coordinates `(htA, htB, htA)` has squared Euclidean length one. -/
theorem htAxis_unit : htA ^ 2 + htB ^ 2 + htA ^ 2 = 1 := by
  have hs := htSin_sq
  have hne := htSin_ne_zero
  rw [htA, htB]
  field_simp
  nlinarith [sq_sqrt_two, hs]

/-- The matrix `htht` equals `tPhase` times `su2` with parameters `((2 + √2) / 4, √2 / 4, (2 -
√2) / 4, √2 / 4)`. -/
theorem htht_eq_su2 :
    htht = tPhase • su2 ((2 + Real.sqrt 2) / 4) (Real.sqrt 2 / 4) ((2 - Real.sqrt 2) / 4)
      (Real.sqrt 2 / 4) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp
  have hhalf : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, h2]
  have hT : tPhase = ((Real.sqrt 2 : ℝ) : ℂ) / 2 * (1 + Complex.I) := by
    rw [tPhase_eq]
    congr 1
    field_simp
    first
      | linear_combination h2
      | linear_combination -h2
  rw [htht_eq, hhalf, hT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Complex.ext_iff] <;>
    constructor <;> nlinarith [sq_sqrt_two]

/-- The matrix `htht` is `tPhase` times the rotation of angle `htAngle` about axis `(htA, htB,
htA)`. -/
theorem htht_eq_axisRot : htht = tPhase • axisRot htA htB htA htAngle := by
  rw [htht_eq_su2, axisRot]
  congr 2
  · rw [show htAngle / 2 = htHalfAngle by rw [htAngle]; ring, cos_htHalfAngle,
      cos_sq_pi_div_eight]
  · rw [show htAngle / 2 = htHalfAngle by rw [htAngle]; ring, ← htSin, mul_comm, htSin_mul_htA]
  · rw [show htAngle / 2 = htHalfAngle by rw [htAngle]; ring, ← htSin, mul_comm, htSin_mul_htB]
  · rw [show htAngle / 2 = htHalfAngle by rw [htAngle]; ring, ← htSin, mul_comm, htSin_mul_htA]

/-- The `k`th power of `htht` is `tPhase ^ k` times the rotation about its fixed axis through
angle `k * htAngle`. -/
theorem htht_pow (k : ℕ) :
    htht ^ k = tPhase ^ k • axisRot htA htB htA ((k : ℝ) * htAngle) := by
  rw [axisRot_nat_mul htAxis_unit, htht_eq_axisRot, smul_pow]

/-- The ratio `htAngle / (4 * π)` is irrational. -/
theorem irrational_htAngle_div_four_pi : Irrational (htAngle / (4 * π)) := by
  rintro ⟨q, hq⟩
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  refine irrational_htAngle_div_two_pi ⟨2 * q, ?_⟩
  push_cast
  rw [hq]
  field_simp
  ring

/-- The additive subgroup generated by `htAngle` and `4π` is dense in the real line. -/
theorem dense_closure_htAngle_four_pi :
    Dense (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ) :=
  dense_addSubgroupClosure_pair_iff.mpr irrational_htAngle_div_four_pi

/-- Every rotation about axis `(htA, htB, htA)` lies in the closure of rotations through integer
multiples of `htAngle`. -/
theorem mem_closure_range_axisRot (α : ℝ) :
    axisRot htA htB htA α
      ∈ closure (Set.range fun k : ℤ => axisRot htA htB htA ((k : ℝ) * htAngle)) := by
  set f : ℝ → Matrix (Fin 2) (Fin 2) ℂ := axisRot htA htB htA with hf

  have hsub : f '' (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ)
      ⊆ Set.range fun k : ℤ => f ((k : ℝ) * htAngle) := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨k, m, hkm⟩ := AddSubgroup.mem_closure_pair.mp ht
    refine ⟨k, ?_⟩
    rw [← hkm, zsmul_eq_mul, zsmul_eq_mul, hf]
    exact (axisRot_add_int_mul_four_pi htA htB htA ((k : ℝ) * htAngle) m).symm
  have hcl : f '' closure (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ)
      ⊆ closure (f '' (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ)) :=
    image_closure_subset_closure_image (continuous_axisRot htA htB htA)
  have hmem : f α ∈ f '' closure (AddSubgroup.closure {htAngle, 4 * π} : Set ℝ) := by
    refine ⟨α, ?_, rfl⟩
    rw [dense_closure_htAngle_four_pi.closure_eq]
    trivial
  exact closure_mono hsub (hcl hmem)

end SU2

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

end
