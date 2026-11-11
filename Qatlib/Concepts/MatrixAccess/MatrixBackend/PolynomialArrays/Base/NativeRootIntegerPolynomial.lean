/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootSharedHorner
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerCoordinate
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorization

set_option backward.isDefEq.respectTransparency false

/-! Bind the same original integer array, its actual derivative array, degree,
LCM point and compact Horner states to the mathematical root consumer. This
reuses the existing literal coefficient polynomial; no new polynomial model. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian
open Qatlib.Concepts.OrderedOracle.TiSdpBridge
open scoped BigOperators

/-- Existing finite literal polynomial, applied to the original integer array. -/
def rootIntegerPolynomial {d : ℕ} (a : Fin (d+1) → ℤ) : ℂ[X] :=
  laurentCoefficientPolynomial (fun i => (a i : ℂ))

/-- Exactly j*a[j] for the nonconstant source array, shifted to start at zero. -/
def rootIntegerDerivative (n : ℕ) (a : Fin (n+2) → ℤ) : Fin (n+1) → ℤ :=
  fun i => ((i.val+1 : ℕ) : ℤ)*a i.succ

/-- The finite construction in `NativeRootIntegerPolynomial` satisfies `rootIntegerScalar_decode` under the displayed hypotheses. -/
theorem rootIntegerScalar_decode (a : ℤ) : gaussianScalarDecode 0 (a,0)=(a : ℂ) := by
  apply Complex.ext <;> simp [gaussianScalarDecode]

/-- The finite construction in `NativeRootIntegerPolynomial` satisfies `rootIntegerPolynomial_coeff` under the displayed hypotheses. -/
theorem rootIntegerPolynomial_coeff {d : ℕ} (a : Fin (d+1) → ℤ) (k : ℕ) :
    (rootIntegerPolynomial a).coeff k=if h : k<d+1 then (a ⟨k,h⟩ : ℂ) else 0 :=
  laurentCoefficientPolynomial_coeff _ k

/-- The finite construction in `NativeRootIntegerPolynomial` satisfies `rootIntegerPolynomial_degree` under the displayed hypotheses. -/
theorem rootIntegerPolynomial_degree {d : ℕ} (a : Fin (d+1) → ℤ) :
    (rootIntegerPolynomial a).natDegree≤d := by
  simpa only [rootIntegerPolynomial,Nat.add_sub_cancel] using
    laurentCoefficientPolynomial_degree (fun i => (a i : ℂ))

/-- The finite construction in `NativeRootIntegerPolynomial` satisfies `rootIntegerPolynomial_natDegree` under the displayed hypotheses. -/
theorem rootIntegerPolynomial_natDegree {d : ℕ} (a : Fin (d+1) → ℤ)
    (ha : a (Fin.last d)≠0) : (rootIntegerPolynomial a).natDegree=d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (rootIntegerPolynomial_degree a)
  rw [rootIntegerPolynomial_coeff,dite_eq_left (Nat.lt_succ_self d)]
  change (a (Fin.last d) : ℂ)≠0
  exact_mod_cast ha

/-- The finite construction in `NativeRootIntegerPolynomial` satisfies `rootIntegerPolynomial_derivative` under the displayed hypotheses. -/
theorem rootIntegerPolynomial_derivative (n : ℕ) (a : Fin (n+2) → ℤ) :
    (rootIntegerPolynomial a).derivative=rootIntegerPolynomial (rootIntegerDerivative n a) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_derivative,rootIntegerPolynomial_coeff,rootIntegerPolynomial_coeff]
  by_cases hk : k<n+1
  · have hk' : k+1<n+2 := by omega
    rw [dite_eq_left hk,dite_eq_left hk']
    simp only [rootIntegerDerivative,Int.cast_mul,Int.cast_natCast]
    have hi : (⟨k,hk⟩ : Fin (n+1)).succ=(⟨k+1,hk'⟩ : Fin (n+2)) := rfl
    rw [hi]
    simp only [Nat.cast_add,Nat.cast_one]
    exact mul_comm _ _
  · have hk' : ¬k+1<n+2 := by omega
    simp only [dite_eq_right hk,dite_eq_right hk',zero_mul]

/-- The finite construction in `NativeRootIntegerPolynomial` satisfies `rootIntegerPolynomial_horner` under the displayed hypotheses. -/
theorem rootIntegerPolynomial_horner {d : ℕ} (a : Fin (d+1) → ℤ) (c : ℚ×ℚ) :
    gaussianPointValue (rootCompactHorner (rootSharedNumerator c)
      (rootSharedDenominator c) (List.ofFn a))=
      (rootIntegerPolynomial a).eval (rootRationalCoordinate c) := by
  rw [rootSharedCompactHorner_correct,rootIntegerPolynomial,laurentCoefficientPolynomial_eval]
  simp only [rootIntegerScalar_decode]

/-- The finite construction in `NativeRootIntegerPolynomial` satisfies `rootIntegerDerivative_denominator` under the displayed hypotheses. -/
theorem rootIntegerDerivative_denominator (n : ℕ) (a : Fin (n+2) → ℤ) (c : ℚ×ℚ) :
    (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a)).denominator=
      rootSharedDenominator c*(rootCompactHorner (rootSharedNumerator c)
        (rootSharedDenominator c) (List.ofFn (rootIntegerDerivative n a))).denominator := by
  simp only [rootCompactHorner_denominator,List.length_ofFn]
  simp [pow_succ,Nat.mul_comm]

/-- The coordinate premise is now the actual integer comparison of SAME-array
value/derivative Horner outputs. No external polynomial/evaluation identities. -/
theorem rootIntegerArray_disk (n : ℕ) (a : Fin (n+2) → ℤ)
    (ha : a (Fin.last (n+1))≠0) (c : ℚ×ℚ) (r : ℚ) (hr : 0<r)
    (htest : rootIntegerCoordinateBound (n+1)
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a))
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))) r) :
    ∃ z : ℂ, (rootIntegerPolynomial a).eval z=0 ∧ ‖z-rootRationalCoordinate c‖≤(r : ℝ) := by
  have hd := rootIntegerPolynomial_natDegree a ha
  apply polynomial_root_disk_of_integer_coordinate_test (rootIntegerPolynomial a)
    (by omega) (rootRationalCoordinate c) r hr
    (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a))
    (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
      (List.ofFn (rootIntegerDerivative n a)))
  · exact rootCompactHorner_denominator_pos _ _ _ (rootSharedDenominator_pos c)
  · exact rootCompactHorner_denominator_pos _ _ _ (rootSharedDenominator_pos c)
  · exact rootIntegerPolynomial_horner a c
  · rw [rootIntegerPolynomial_derivative]
    exact rootIntegerPolynomial_horner (rootIntegerDerivative n a) c
  · simpa only [hd] using htest

/-- The actual exact-zero shortcut needs no derivative array or leading term. -/
theorem rootIntegerArray_zero_disk {d : ℕ} (a : Fin (d+1) → ℤ) (c : ℚ×ℚ)
    (r : ℚ) (hr : 0≤r)
    (hz : (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
      (List.ofFn a)).numerator=(0,0)) :
    ∃ z : ℂ, (rootIntegerPolynomial a).eval z=0 ∧ ‖z-rootRationalCoordinate c‖≤(r : ℝ) :=
  polynomial_root_disk_of_integer_zero (rootIntegerPolynomial a) (rootRationalCoordinate c)
    r (by exact_mod_cast hr) _ hz (rootIntegerPolynomial_horner a c)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
