/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.Magic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# An Irrational Clifford-T Rotation Angle

This module establishes the irrational rotation angle used in a single-qubit Clifford-T density
argument, following the universality framework discussed in [NielsenChuang2010]. The definitions
`htHalfAngle` and `htAngle` satisfy `cos_htAngle`; the relation
`sq_add_self_two_mul_cos_htAngle` obstructs integral dependence over the integers and yields
`irrational_htAngle_div_two_pi`. Integer multiples of this angle are therefore dense modulo `2 *
π`.

The matrices `hGateM`, `tGateM`, and `htht` connect the angle with an explicit gate product:
`htht` is defined as `tGateM * hGateM * tGateM * hGateM`. The trace and determinant calculations
culminate in `trace_htht_eq_cos_htAngle`, retaining the global phase `tPhase`.

## Main statements

* `isIntegral_two_mul_cos_of_eq_two_pi_mul` proves integrality of twice the cosine of a rational
  multiple of a full turn.
- `irrational_htAngle_div_two_pi` proves that `htAngle / (2 * π)` is irrational.
* `denseRange_zsmul_htAngle` and `exists_zsmul_htAngle_approx` give density modulo a full turn
  and approximation by integer combinations.
- `trace_htht_eq_cos_htAngle` relates the explicit gate product to its half-angle cosine.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010], *Quantum Computation and Quantum Information*.
-/

open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

open QuantumInfo

section

open Polynomial
open scoped Real

/-- If `θ` is a rational multiple of `2 * π`, then `2 * Real.cos θ` is integral over the
integers. The proof expresses this number as the sum of a root of unity and its inverse. -/
theorem isIntegral_two_mul_cos_of_eq_two_pi_mul {θ : ℝ} {q : ℚ} (hθ : θ = 2 * π * q) :
    IsIntegral ℤ (2 * Real.cos θ) := by
  have hd0 : q.den ≠ 0 := q.den_nz
  set ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hζdef

  have hdθ : (q.den : ℝ) * θ = 2 * π * (q.num : ℝ) := by
    rw [hθ, Rat.cast_def]
    have hne : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    field_simp
  have hζd : ζ ^ q.den = 1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    have hcast : ((q.den : ℂ)) * ((θ : ℂ) * Complex.I)
        = (q.num : ℂ) * (2 * (π : ℂ) * Complex.I) := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) hdθ
      push_cast at h
      calc ((q.den : ℂ)) * ((θ : ℂ) * Complex.I) = ((q.den : ℂ) * (θ : ℂ)) * Complex.I := by ring
        _ = (2 * (π : ℂ) * (q.num : ℂ)) * Complex.I := by rw [h]
        _ = (q.num : ℂ) * (2 * (π : ℂ) * Complex.I) := by ring
    rw [hcast, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

  have hζint : IsIntegral ℤ ζ := by
    refine ⟨X ^ q.den - 1, ?_, ?_⟩
    · simpa using monic_X_pow_sub_C (1 : ℤ) hd0
    · simp [hζd]

  have hpow : ζ ^ (q.den - 1) * ζ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd0)]
    exact hζd
  have hinv : ζ ^ (q.den - 1) = ζ⁻¹ := eq_inv_of_mul_eq_one_left hpow
  have hsum : IsIntegral ℤ (ζ + ζ⁻¹) := by
    rw [← hinv]
    exact hζint.add (hζint.pow _)
  have hcos : ζ + ζ⁻¹ = ((2 * Real.cos θ : ℝ) : ℂ) := by
    have h2 := Complex.two_cos (θ : ℂ)
    rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_ofNat, h2, hζdef,
      show -(θ : ℂ) * Complex.I = -((θ : ℂ) * Complex.I) by ring, Complex.exp_neg]
  rw [hcos] at hsum
  rwa [← isIntegral_algebraMap_iff (R := ℤ) (A := ℝ) (B := ℂ),
    Complex.coe_algebraMap]

/-- A real number satisfying `x ^ 2 + x = 7 / 4` is not integral over the integers, since that
would make the nonintegral rational number `7 / 4` integral as well. -/
theorem not_isIntegral_of_sq_add_self_eq {x : ℝ} (hx : x ^ 2 + x = 7 / 4) : ¬ IsIntegral ℤ x := by
  intro h
  have h74 : IsIntegral ℤ ((7 / 4 : ℝ)) := by
    rw [← hx]
    exact (h.pow 2).add h
  have hq : IsIntegral ℤ ((7 / 4 : ℚ)) := by
    rw [← isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℝ)]
    have hmap : (algebraMap ℚ ℝ) (7 / 4 : ℚ) = (7 / 4 : ℝ) := by norm_num
    rw [hmap]
    exact h74
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  have hy' : (y : ℚ) = 7 / 4 := by simpa using hy
  have h4' : y * 4 = 7 := by
    field_simp at hy'
    exact_mod_cast hy'
  omega

namespace QuantumInfo

namespace CliffordT

/-- This half-angle is `Real.arccos (Real.cos (π / 8) ^ 2)` and is associated with the
Clifford-T gate product. -/
noncomputable def htHalfAngle : ℝ := Real.arccos (Real.cos (π / 8) ^ 2)

/-- This rotation angle is defined as twice `htHalfAngle`. -/
noncomputable def htAngle : ℝ := 2 * htHalfAngle

/-- The squared cosine of `π / 8` is `(2 + Real.sqrt 2) / 4`. -/
theorem cos_sq_pi_div_eight : Real.cos (π / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  rw [Real.cos_sq, show 2 * (π / 8) = π / 4 by ring, Real.cos_pi_div_four]
  ring

/-- The cosine of `htHalfAngle` equals `Real.cos (π / 8) ^ 2`, as prescribed by its
inverse-cosine definition. -/
theorem cos_htHalfAngle : Real.cos htHalfAngle = Real.cos (π / 8) ^ 2 := by
  refine Real.cos_arccos ?_ ?_
  · nlinarith [sq_nonneg (Real.cos (π / 8))]
  · nlinarith [Real.cos_le_one (π / 8), Real.neg_one_le_cos (π / 8)]

/-- The square of the nonnegative real square root of two is two. -/
theorem sq_sqrt_two : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- The cosine of `htAngle` is `(2 * Real.sqrt 2 - 1) / 4`. -/
theorem cos_htAngle : Real.cos htAngle = (2 * Real.sqrt 2 - 1) / 4 := by
  rw [htAngle, Real.cos_two_mul, cos_htHalfAngle, cos_sq_pi_div_eight]
  nlinarith [sq_sqrt_two]

/-- Twice the cosine of `htAngle` satisfies the relation `x ^ 2 + x = 7 / 4`, providing the
obstruction to integrality used in the irrationality argument. -/
theorem sq_add_self_two_mul_cos_htAngle :
    (2 * Real.cos htAngle) ^ 2 + 2 * Real.cos htAngle = 7 / 4 := by
  rw [cos_htAngle]
  nlinarith [sq_sqrt_two]

/-- The ratio `htAngle / (2 * π)` is irrational. This supplies the irrational rotation
ingredient in the Clifford-T universality argument described in [NielsenChuang2010]. -/
theorem irrational_htAngle_div_two_pi : Irrational (htAngle / (2 * π)) := by
  rintro ⟨q, hq⟩
  have hpi : (2 : ℝ) * π ≠ 0 := by positivity
  have hθ : htAngle = 2 * π * q := by
    field_simp at hq
    linarith [hq]
  exact not_isIntegral_of_sq_add_self_eq sq_add_self_two_mul_cos_htAngle
    (isIntegral_two_mul_cos_of_eq_two_pi_mul hθ)

/-- Integer multiples of `htAngle` have dense range in the additive circle of period `2 * π`. -/
theorem denseRange_zsmul_htAngle :
    DenseRange fun k : ℤ => k • (htAngle : AddCircle (2 * π)) :=
  AddCircle.denseRange_zsmul_coe_iff.mpr irrational_htAngle_div_two_pi

/-- The additive subgroup of the real numbers generated by `htAngle` and `2 * π` is dense in the
real line. -/
theorem dense_closure_htAngle :
    Dense (AddSubgroup.closure {htAngle, 2 * π} : Set ℝ) :=
  dense_addSubgroupClosure_pair_iff.mpr irrational_htAngle_div_two_pi

/-- Every real `α` can be approximated within any positive `ε` by an integer linear combination
of `htAngle` and `2 * π`. -/
theorem exists_zsmul_htAngle_approx (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k m : ℤ, |(k : ℝ) * htAngle + (m : ℝ) * (2 * π) - α| < ε := by
  obtain ⟨y, hy, hdist⟩ := dense_closure_htAngle.exists_dist_lt α hε
  obtain ⟨k, m, hkm⟩ := AddSubgroup.mem_closure_pair.mp hy
  refine ⟨k, m, ?_⟩
  rw [Real.dist_eq] at hdist
  rw [zsmul_eq_mul, zsmul_eq_mul] at hkm
  rw [hkm, abs_sub_comm]
  exact hdist

/-- The Hadamard matrix is defined as the matrix with rows `(1, 1)` and `(1, -1)` scaled by the
complex inverse of `Real.sqrt 2`. -/
noncomputable def hGateM : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]

/-- The T gate matrix is `diag(1, tPhase)`, where `tPhase` is the phase for angle `π / 4`. -/
noncomputable def tGateM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, tPhase]

/-- This is the explicit matrix product `tGateM * hGateM * tGateM * hGateM` used to obtain the
angle `htAngle`. -/
noncomputable def htht : Matrix (Fin 2) (Fin 2) ℂ := tGateM * hGateM * tGateM * hGateM

/-- Two complex factors of the inverse of `Real.sqrt 2`, multiplied by two, give one. -/
theorem sqrt_two_inv_sq_two : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2 = 1 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Expands `htht` as a scalar multiple of the matrix with rows `(1 + tPhase, 1 - tPhase)` and
`(tPhase * (1 - tPhase), tPhase * (1 + tPhase))`. -/
theorem htht_eq : htht = (((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) •
    !![1 + tPhase, 1 - tPhase; tPhase * (1 - tPhase), tPhase * (1 + tPhase)]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [htht, hGateM, tGateM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The trace of `htht` is `(1 + tPhase) ^ 2 / 2`. -/
theorem trace_htht : htht.trace = (1 + tPhase) ^ 2 / 2 := by
  rw [htht_eq, Matrix.trace_smul, Matrix.trace_fin_two_of, smul_eq_mul]
  have h := sqrt_two_inv_sq_two
  linear_combination ((1 + tPhase) ^ 2 / 2) * h

/-- The determinant of `htht` is `tPhase ^ 2`. -/
theorem det_htht : htht.det = tPhase ^ 2 := by
  rw [htht_eq, Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin]
  have h := sqrt_two_inv_sq_two
  have hsq : ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) ^ 2 * 4 = 1 := by
    have h4 : ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2) ^ 2 = 1 := by rw [h]; norm_num
    linear_combination h4
  linear_combination (tPhase ^ 2) * hsq

/-- This complex phase is `exp(i * π / 8)`, whose square is `tPhase`. -/
noncomputable def tPhase8 : ℂ := Complex.exp (((π / 8 : ℝ) : ℂ) * Complex.I)

/-- Squaring the phase `tPhase8` gives `tPhase`. -/
theorem tPhase8_sq : tPhase8 ^ 2 = tPhase := by
  rw [tPhase8, tPhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The phase `tPhase8` is nonzero, since it is a complex exponential. -/
theorem tPhase8_ne_zero : tPhase8 ≠ 0 := Complex.exp_ne_zero _

/-- The sum of `tPhase8` and its multiplicative inverse is twice the complex coercion of
`Real.cos (π / 8)`. -/
theorem tPhase8_add_inv : tPhase8 + tPhase8⁻¹ = 2 * (Real.cos (π / 8) : ℂ) := by
  have h2 := Complex.two_cos (((π / 8 : ℝ)) : ℂ)
  have hneg : Complex.exp (-(((π / 8 : ℝ)) : ℂ) * Complex.I) = tPhase8⁻¹ := by
    rw [tPhase8,
      show -(((π / 8 : ℝ)) : ℂ) * Complex.I = -((((π / 8 : ℝ)) : ℂ) * Complex.I) by ring,
      Complex.exp_neg]
  rw [Complex.ofReal_cos, h2, hneg, tPhase8]

/-- Factors `1 + tPhase` as `2 * (Real.cos (π / 8) : ℂ) * tPhase8`. -/
theorem one_add_tPhase : 1 + tPhase = 2 * (Real.cos (π / 8) : ℂ) * tPhase8 := by
  have h := tPhase8_add_inv
  have hne := tPhase8_ne_zero
  rw [← tPhase8_sq, ← h]
  field_simp
  ring

/-- The trace of `htht` is `2 * (Real.cos (htAngle / 2) : ℂ) * tPhase`, relating the gate
product to the half-angle cosine with its global phase retained. -/
theorem trace_htht_eq_cos_htAngle :
    htht.trace = 2 * (Real.cos (htAngle / 2) : ℂ) * tPhase := by
  have hhalf : htAngle / 2 = htHalfAngle := by rw [htAngle]; ring
  rw [trace_htht, hhalf, cos_htHalfAngle, one_add_tPhase]
  push_cast
  rw [mul_pow, mul_pow, tPhase8_sq]
  ring

end CliffordT

end QuantumInfo

end

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
