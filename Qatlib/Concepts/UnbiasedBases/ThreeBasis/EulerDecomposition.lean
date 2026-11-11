/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.SU2Rotation

/-!
# Euler Decompositions of Qubit Unitaries

This module expresses determinant-one qubit unitaries as products of z, y, and z rotations
through `exists_euler_of_det_one`. This is the SU(2) Euler factorization discussed in
[KauffmanLomonaco2006]. The definitions `rzMat`, `ryMat`, and `expI` fix the half-angle rotation
and scalar-phase conventions, and `exists_euler` includes an additional global phase for an
arbitrary unitary matrix of size two.

The rotation identities also give the A-X-B-X-C factorization used in single-qubit gate
constructions [NielsenChuang2010]: `exists_abc` provides unitary matrices A, B, and C satisfying
A B C = 1 and reconstructing the target up to phase. Quaternion and axis-angle representations
then yield unitary square roots, with determinant one preserved when it is required.

## Main statements

- `rz_ry_rz_eq` computes the entries of a z-y-z rotation product.
* `exists_euler_of_det_one` and `exists_euler` give Euler decompositions without and with a
  global phase.
- `exists_abc` gives unitary factors with A B C = 1 and U = expI α • (A X B X C).
* `exists_axisRot_of_det_one` expresses every determinant-one qubit unitary as a rotation about
  a unit axis.
- `exists_sqrt_of_det_one` and `exists_sqrt` construct unitary square roots.

## References

* [Kauffman and Lomonaco, 2006][KauffmanLomonaco2006] Louis H. Kauffman and Samuel J. Lomonaco
  Jr., q-Deformed Spin Networks, Knot Polynomials and Anyonic Topological Quantum Computation.
* [Nielsen and Chuang, 2010][NielsenChuang2010] Michael A. Nielsen and Isaac L. Chuang, Quantum
  Computation and Quantum Information.
-/

set_option warningAsError false
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2

section

open Matrix

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

namespace SU2

/-- The conjugate transpose of `su2 w x y z` keeps w and negates x, y, and z. -/
theorem su2_conjTranspose (w x y z : ℝ) : (su2 w x y z)ᴴ = su2 w (-x) (-y) (-z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Complex.ext_iff]

/-- If the real coordinates w, x, y, and z have squared sum one, `su2 w x y z` belongs to the
unitary group of complex matrices of size two. -/
theorem su2_mem_unitaryGroup {w x y z : ℝ} (h : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    su2 w x y z ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, su2_conjTranspose, su2_mul]
  rw [show w * w - x * -x - y * -y - z * -z = 1 by linear_combination h,
    show w * -x + x * w + y * -z - z * -y = 0 by ring,
    show w * -y - x * -z + y * w + z * -x = 0 by ring,
    show w * -z + x * -y - y * -x + z * w = 0 by ring]
  exact su2_one

/-- Rotation about a real unit axis gives a unitary matrix of size two for every real angle θ. -/
theorem axisRot_mem_unitaryGroup {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    axisRot a b c θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [axisRot]
  refine su2_mem_unitaryGroup ?_
  linear_combination (Real.sin (θ / 2)) ^ 2 * hu + Real.sin_sq_add_cos_sq (θ / 2)

end SU2

namespace Euler

open SU2

/-- The value `expI t` is the complex phase exp(i t) for a real argument t. -/
noncomputable def expI (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

/-- The complex phase `expI` at angle zero equals one. -/
@[simp] theorem expI_zero : expI 0 = 1 := by simp [expI]

/-- The complex phase of a sum is the product of the phases: `expI (s + t) = expI s * expI t`. -/
theorem expI_add (s t : ℝ) : expI (s + t) = expI s * expI t := by
  simp [expI, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Euler's formula expresses `expI t` as cos t + i sin t. -/
theorem expI_eq (t : ℝ) : expI t = (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ) := by
  rw [expI, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- Complex conjugation of `expI t` negates the angle t. -/
@[simp] theorem star_expI (t : ℝ) : star (expI t) = expI (-t) := by
  simp [expI_eq, Complex.ext_iff, Real.cos_neg, Real.sin_neg]

/-- The phases at t and -t multiply to one. -/
@[simp] theorem expI_mul_neg (t : ℝ) : expI t * expI (-t) = 1 := by
  rw [← expI_add]
  simp

/-- A complex number z equals its norm multiplied by `expI z.arg`, including when z is zero. -/
theorem polar (z : ℂ) : (‖z‖ : ℂ) * expI z.arg = z :=
  Complex.norm_mul_exp_arg_mul_I z

/-- The complex conjugate of z equals its norm multiplied by the phase with angle `-z.arg`. -/
theorem polar_star (z : ℂ) : (‖z‖ : ℂ) * expI (-z.arg) = star z := by
  have h : star ((‖z‖ : ℂ) * expI z.arg) = star z := by rw [polar]
  rw [star_mul, star_expI, Complex.star_def, Complex.conj_ofReal] at h
  rw [Complex.star_def, ← h, mul_comm]

/-- The matrix `rzMat β` is the qubit rotation through angle β about the z axis, defined as
`axisRot 0 0 1 β`. -/
noncomputable def rzMat (β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 0 0 1 β

/-- The matrix `ryMat γ` is the qubit rotation through angle γ about the y axis, defined as
`axisRot 0 1 0 γ`. -/
noncomputable def ryMat (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 0 1 0 γ

/-- The matrix `xMat` is the Pauli X matrix, with zero diagonal entries and both off-diagonal
entries equal to one. -/
def xMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The z rotation `rzMat β` is diagonal with entries `expI (-(β/2))` and `expI (β/2)`. -/
theorem rzMat_eq (β : ℝ) : rzMat β = !![expI (-(β / 2)), 0; 0, expI (β / 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzMat, axisRot, su2, expI_eq, Real.cos_neg, Real.sin_neg, sub_eq_add_neg]

/-- The matrix `ryMat γ` has diagonal entries cos(γ/2), upper-right entry -sin(γ/2), and
lower-left entry sin(γ/2). -/
theorem ryMat_eq (γ : ℝ) :
    ryMat γ = !![(Real.cos (γ / 2) : ℂ), -(Real.sin (γ / 2) : ℂ);
                 (Real.sin (γ / 2) : ℂ), (Real.cos (γ / 2) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ryMat, axisRot, su2, Complex.ext_iff]

/-- Multiplying two z rotations adds their angles. -/
theorem rzMat_mul (s t : ℝ) : rzMat s * rzMat t = rzMat (s + t) :=
  (axisRot_add (by norm_num) s t).symm

/-- Multiplying two y rotations adds their angles. -/
theorem ryMat_mul (s t : ℝ) : ryMat s * ryMat t = ryMat (s + t) :=
  (axisRot_add (by norm_num) s t).symm

/-- The z rotation through angle zero is the identity matrix. -/
@[simp] theorem rzMat_zero : rzMat 0 = 1 := axisRot_zero 0 0 1

/-- The y rotation through angle zero is the identity matrix. -/
@[simp] theorem ryMat_zero : ryMat 0 = 1 := axisRot_zero 0 1 0

/-- Every z rotation `rzMat β` belongs to the unitary group of complex matrices of size two. -/
theorem rzMat_mem_unitaryGroup (β : ℝ) : rzMat β ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  axisRot_mem_unitaryGroup (by norm_num) β

/-- Every y rotation `ryMat γ` belongs to the unitary group of complex matrices of size two. -/
theorem ryMat_mem_unitaryGroup (γ : ℝ) : ryMat γ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  axisRot_mem_unitaryGroup (by norm_num) γ

/-- The Pauli X matrix `xMat` belongs to the unitary group of complex matrices of size two. -/
theorem xMat_mem_unitaryGroup : xMat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- The square of the Pauli X matrix `xMat` is the identity matrix. -/
@[simp] theorem xMat_mul_self : xMat * xMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugating a z rotation by the Pauli X matrix negates its angle. -/
theorem xMat_conj_rzMat (β : ℝ) : xMat * rzMat β * xMat = rzMat (-β) := by
  rw [rzMat_eq, rzMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMat, Matrix.mul_apply, Fin.sum_univ_two, neg_div, neg_neg]

/-- Conjugating a y rotation by the Pauli X matrix negates its angle. -/
theorem xMat_conj_ryMat (γ : ℝ) : xMat * ryMat γ * xMat = ryMat (-γ) := by
  rw [ryMat_eq, ryMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMat, Matrix.mul_apply, Fin.sum_univ_two, neg_div, Real.cos_neg, Real.sin_neg]

/-- Conjugation by `xMat` preserves products of matrices of size two. -/
theorem xMat_conj_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    xMat * M * xMat * (xMat * N * xMat) = xMat * (M * N) * xMat := by
  calc xMat * M * xMat * (xMat * N * xMat)
      = xMat * M * (xMat * xMat) * (N * xMat) := by simp only [mul_assoc]
    _ = xMat * (M * N) * xMat := by
        rw [xMat_mul_self, mul_one]
        simp only [mul_assoc]

/-- The entries of the z-y-z product are expressed using cos(γ/2), sin(γ/2), and phases at the
half-sum and half-difference of β and δ. -/
theorem rz_ry_rz_eq (β γ δ : ℝ) :
    rzMat β * ryMat γ * rzMat δ =
      !![expI (-((β + δ) / 2)) * (Real.cos (γ / 2) : ℂ),
          -(expI (-((β - δ) / 2)) * (Real.sin (γ / 2) : ℂ));
         expI ((β - δ) / 2) * (Real.sin (γ / 2) : ℂ),
          expI ((β + δ) / 2) * (Real.cos (γ / 2) : ℂ)] := by
  have e1 : expI (-(β / 2)) * expI (-(δ / 2)) = expI (-((β + δ) / 2)) := by
    rw [← expI_add]
    congr 1
    ring
  have e2 : expI (-(β / 2)) * expI (δ / 2) = expI (-((β - δ) / 2)) := by
    rw [← expI_add]
    congr 1
    ring
  have e3 : expI (β / 2) * expI (-(δ / 2)) = expI ((β - δ) / 2) := by
    rw [← expI_add]
    congr 1
    ring
  have e4 : expI (β / 2) * expI (δ / 2) = expI ((β + δ) / 2) := by
    rw [← expI_add]
    congr 1
    ring
  rw [rzMat_eq, ryMat_eq, rzMat_eq]
  set c : ℂ := (Real.cos (γ / 2) : ℂ)
  set s : ℂ := (Real.sin (γ / 2) : ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination c * e1
  · linear_combination s * e2
  · linear_combination s * e3
  · linear_combination c * e4

/-- For a unitary matrix of size two, the squared norms of the two entries in its first column
sum to one. -/
theorem normSq_col_zero {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ‖U 0 0‖ ^ 2 + ‖U 1 0‖ ^ 2 = 1 := by
  have e : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, ← starRingEnd_apply, Complex.mul_conj']
    push_cast
    ring
  have h0 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.one_apply_eq, e] at h0
  exact_mod_cast h0

/-- In a determinant-one unitary matrix of size two, the bottom-right entry is the conjugate of
the top-left entry, and the top-right entry is the negative conjugate of the bottom-left
entry. -/
theorem adjugate_entries {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    U 1 1 = star (U 0 0) ∧ U 0 1 = -star (U 1 0) := by
  have hinv : U⁻¹ = Uᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have h1 : Uᴴ = U.adjugate := by
    rw [← hinv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [Matrix.adjugate_fin_two] at h1
  refine ⟨?_, ?_⟩
  · simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun h1 0) 0).symm
  · have h2 : star (U 1 0) = -U 0 1 := by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun h1 0) 1
    rw [h2, neg_neg]

/-- Every determinant-one unitary matrix of size two factors as `rzMat β * ryMat γ * rzMat δ`
for real Euler angles β, γ, and δ. This is the SU(2) Euler factorization discussed in
[KauffmanLomonaco2006]. -/
theorem exists_euler_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ β γ δ : ℝ, U = rzMat β * ryMat γ * rzMat δ := by
  obtain ⟨h11, h01⟩ := adjugate_entries hU hdet
  have hcol := normSq_col_zero hU
  have hle : ‖U 0 0‖ ≤ 1 := by nlinarith [norm_nonneg (U 0 0), norm_nonneg (U 1 0)]
  have hge : (-1 : ℝ) ≤ ‖U 0 0‖ := by nlinarith [norm_nonneg (U 0 0)]
  refine ⟨(U 1 0).arg - (U 0 0).arg, 2 * Real.arccos ‖U 0 0‖,
    -(U 0 0).arg - (U 1 0).arg, ?_⟩
  have hhalf : 2 * Real.arccos ‖U 0 0‖ / 2 = Real.arccos ‖U 0 0‖ := by ring
  have hcos : Real.cos (2 * Real.arccos ‖U 0 0‖ / 2) = ‖U 0 0‖ := by
    rw [hhalf, Real.cos_arccos hge hle]
  have hsin : Real.sin (2 * Real.arccos ‖U 0 0‖ / 2) = ‖U 1 0‖ := by
    rw [hhalf, Real.sin_arccos, show 1 - ‖U 0 0‖ ^ 2 = ‖U 1 0‖ ^ 2 by linarith,
      Real.sqrt_sq (norm_nonneg _)]
  have hp : -(((U 1 0).arg - (U 0 0).arg + (-(U 0 0).arg - (U 1 0).arg)) / 2) = (U 0 0).arg := by
    ring
  have hp' : ((U 1 0).arg - (U 0 0).arg + (-(U 0 0).arg - (U 1 0).arg)) / 2 = -(U 0 0).arg := by
    ring
  have hq : ((U 1 0).arg - (U 0 0).arg - (-(U 0 0).arg - (U 1 0).arg)) / 2 = (U 1 0).arg := by
    ring
  rw [rz_ry_rz_eq, hcos, hsin, hp, hp', hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination -polar (U 0 0)
  · linear_combination h01 + polar_star (U 1 0)
  · linear_combination -polar (U 1 0)
  · linear_combination h11 - polar_star (U 0 0)

/-- Every unitary matrix of size two is a scalar phase `expI α` times a z-y-z rotation product
with real angles. -/
theorem exists_euler {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, U = expI α • (rzMat β * ryMat γ * rzMat δ) := by
  have hstar : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hdet : star U.det * U.det = 1 := by
    have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.mp hU)
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose,
      Matrix.det_one] at h
  have hnorm : ‖U.det‖ = 1 := by
    have h : ((‖U.det‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hdet, mul_comm, ← starRingEnd_apply, Complex.mul_conj']
      push_cast
      ring
    have h2 : ‖U.det‖ ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg U.det]
  have hdetU : U.det = expI U.det.arg := by
    conv_lhs => rw [← polar U.det]
    rw [hnorm]
    simp
  obtain ⟨t, ht⟩ : ∃ t : ℝ, U.det = expI t := ⟨U.det.arg, hdetU⟩
  have hW : expI (-(t / 2)) • U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hstar, star_expI, neg_neg, ← expI_add]
    simp
  have hWdet : (expI (-(t / 2)) • U).det = 1 := by
    rw [Matrix.det_smul, ht, show Fintype.card (Fin 2) = 2 from rfl, pow_two, ← expI_add,
      ← expI_add, show -(t / 2) + -(t / 2) + t = 0 by ring, expI_zero]
  obtain ⟨β, γ, δ, hbgd⟩ := exists_euler_of_det_one hW hWdet
  refine ⟨t / 2, β, γ, δ, ?_⟩
  rw [← hbgd, smul_smul, ← expI_add]
  simp

/-- The rotation factors A = Rz(β) Ry(γ/2), B = Ry(-γ/2) Rz(-(δ+β)/2), and C = Rz((δ-β)/2)
satisfy A B C = 1. -/
theorem abc_prod_eq_one (β γ δ : ℝ) :
    rzMat β * ryMat (γ / 2) * (ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2)))
        * rzMat ((δ - β) / 2) = 1 := by
  have key : rzMat β * ryMat (γ / 2) * (ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2)))
        * rzMat ((δ - β) / 2)
      = rzMat β * (ryMat (γ / 2) * ryMat (-(γ / 2)))
          * (rzMat (-((δ + β) / 2)) * rzMat ((δ - β) / 2)) := by
    simp only [mul_assoc]
  rw [key, ryMat_mul, rzMat_mul, show γ / 2 + -(γ / 2) = 0 by ring, ryMat_zero, mul_one,
    show -((δ + β) / 2) + (δ - β) / 2 = -β by ring, rzMat_mul, show β + -β = 0 by ring, rzMat_zero]

/-- For A = Rz(β) Ry(γ/2), B = Ry(-γ/2) Rz(-(δ+β)/2), and C = Rz((δ-β)/2), the product A X B X C
equals Rz(β) Ry(γ) Rz(δ). -/
theorem abc_identity (β γ δ : ℝ) :
    rzMat β * ryMat (γ / 2) * xMat * (ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2))) * xMat
        * rzMat ((δ - β) / 2) = rzMat β * ryMat γ * rzMat δ := by
  have hconj : xMat * (ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2))) * xMat
      = ryMat (γ / 2) * rzMat ((δ + β) / 2) := by
    rw [← xMat_conj_mul, xMat_conj_ryMat, xMat_conj_rzMat, neg_neg, neg_neg]
  have hassoc : ∀ M N P : Matrix (Fin 2) (Fin 2) ℂ,
      M * xMat * N * xMat * P = M * (xMat * N * xMat) * P := by
    intro M N P
    simp only [mul_assoc]
  rw [hassoc, hconj]
  have key : rzMat β * ryMat (γ / 2) * (ryMat (γ / 2) * rzMat ((δ + β) / 2))
        * rzMat ((δ - β) / 2)
      = rzMat β * (ryMat (γ / 2) * ryMat (γ / 2))
          * (rzMat ((δ + β) / 2) * rzMat ((δ - β) / 2)) := by
    simp only [mul_assoc]
  rw [key, ryMat_mul, rzMat_mul, show γ / 2 + γ / 2 = γ by ring,
    show (δ + β) / 2 + (δ - β) / 2 = δ by ring]

/-- Every unitary matrix of size two can be written as `expI α • (A * xMat * B * xMat * C)` with
unitary A, B, and C satisfying A B C = 1. -/
theorem exists_abc {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (α : ℝ) (A B C : Matrix (Fin 2) (Fin 2) ℂ),
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        C ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ A * B * C = 1 ∧
          U = expI α • (A * xMat * B * xMat * C) := by
  obtain ⟨α, β, γ, δ, hU'⟩ := exists_euler hU
  refine ⟨α, rzMat β * ryMat (γ / 2), ryMat (-(γ / 2)) * rzMat (-((δ + β) / 2)),
    rzMat ((δ - β) / 2), mul_mem (rzMat_mem_unitaryGroup β) (ryMat_mem_unitaryGroup (γ / 2)),
    mul_mem (ryMat_mem_unitaryGroup (-(γ / 2))) (rzMat_mem_unitaryGroup (-((δ + β) / 2))),
    rzMat_mem_unitaryGroup ((δ - β) / 2), abc_prod_eq_one β γ δ, ?_⟩
  rw [hU', abc_identity]

/-- Multiplying a unitary matrix of size two by the scalar phase `expI t` preserves membership
in the unitary group. -/
theorem expI_smul_mem_unitaryGroup (t : ℝ) {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    expI t • U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mem_unitaryGroup_iff.mp hU, star_expI, ← expI_add]
  simp

/-- Every determinant-one unitary matrix of size two has the quaternion form `su2 w x y z`, with
real coordinates whose squared sum is one. -/
theorem exists_su2_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ w x y z : ℝ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1 ∧ U = su2 w x y z := by
  obtain ⟨h11, h01⟩ := adjugate_entries hU hdet
  have hcol := normSq_col_zero hU
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  refine ⟨(U 0 0).re, -(U 1 0).im, (U 1 0).re, -(U 0 0).im, ?_, ?_⟩
  · rw [hsq, hsq] at hcol
    linarith
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [su2, h11, h01, Complex.ext_iff]

/-- Every determinant-one unitary matrix of size two is `axisRot a b c θ` for a real unit axis
(a, b, c) and a real angle θ. -/
theorem exists_axisRot_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ a b c θ : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 ∧ U = axisRot a b c θ := by
  obtain ⟨w, x, y, z, hunit, hU'⟩ := exists_su2_of_det_one hU hdet
  have hw1 : w ≤ 1 := by nlinarith
  have hw2 : (-1 : ℝ) ≤ w := by nlinarith
  have hcos : Real.cos (2 * Real.arccos w / 2) = w := by
    rw [show 2 * Real.arccos w / 2 = Real.arccos w by ring, Real.cos_arccos hw2 hw1]
  have hsin : Real.sin (2 * Real.arccos w / 2) = Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
    rw [show 2 * Real.arccos w / 2 = Real.arccos w by ring, Real.sin_arccos,
      show 1 - w ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 by linarith]
  by_cases hr : x ^ 2 + y ^ 2 + z ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hz : z = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    refine ⟨0, 0, 1, 2 * Real.arccos w, by norm_num, ?_⟩
    rw [hU', axisRot, hcos, hsin, hr, hx, hy, hz]
    norm_num
  · have hrpos : 0 < x ^ 2 + y ^ 2 + z ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hr)
    set r := Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) with hrdef
    have hrpos' : 0 < r := Real.sqrt_pos.mpr hrpos
    have hr2 : r ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := Real.sq_sqrt (le_of_lt hrpos)
    refine ⟨x / r, y / r, z / r, 2 * Real.arccos w, ?_, ?_⟩
    · field_simp
      linarith [hr2]
    · rw [hU', axisRot, hcos, hsin]
      congr 1 <;> field_simp

/-- Every determinant-one unitary matrix of size two has a unitary square root whose determinant
is also one. -/
theorem exists_sqrt_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℂ,
      V ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ V.det = 1 ∧ V * V = U := by
  obtain ⟨a, b, c, θ, hu, hU'⟩ := exists_axisRot_of_det_one hU hdet
  refine ⟨axisRot a b c (θ / 2), axisRot_mem_unitaryGroup hu _, axisRot_det hu _, ?_⟩
  rw [← axisRot_add hu, show θ / 2 + θ / 2 = θ by ring, hU']

/-- Every z-y-z rotation product `rzMat β * ryMat γ * rzMat δ` has determinant one. -/
theorem rz_ry_rz_det (β γ δ : ℝ) : (rzMat β * ryMat γ * rzMat δ).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, rzMat, ryMat, rzMat,
    axisRot_det (by norm_num), axisRot_det (by norm_num), axisRot_det (by norm_num)]
  norm_num

/-- Every unitary matrix of size two has a unitary square root. -/
theorem exists_sqrt {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℂ, V ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ V * V = U := by
  obtain ⟨α, β, γ, δ, hU'⟩ := exists_euler hU
  have hW : rzMat β * ryMat γ * rzMat δ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mul_mem (mul_mem (rzMat_mem_unitaryGroup β) (ryMat_mem_unitaryGroup γ))
      (rzMat_mem_unitaryGroup δ)
  obtain ⟨V, hV, -, hVV⟩ := exists_sqrt_of_det_one hW (rz_ry_rz_det β γ δ)
  refine ⟨expI (α / 2) • V, expI_smul_mem_unitaryGroup _ hV, ?_⟩
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hVV, ← expI_add,
    show α / 2 + α / 2 = α by ring, hU']

end Euler

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo
