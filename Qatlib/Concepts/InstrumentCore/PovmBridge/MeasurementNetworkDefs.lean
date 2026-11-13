/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

/-!
# Binary projective POVMs

This module proves that a Hermitian projection is nonnegative, equals its positive square root,
and has an idempotent complement. These facts define `binaryProjectivePOVM`, whose effects are
the projection and its complement.

The construction supplies the POVM form of binary projective measurement in the standard
finite-dimensional measurement formalism [Watrous2018].

## Main definitions and statements

* `hermitian_projection_half`: a Hermitian projection equals its square root.
* `binaryProjectivePOVM`: the Boolean-outcome POVM associated with a projection.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option autoImplicit false

namespace Qatlib.Concepts.InstrumentCore.PovmBridge

open Matrix
open scoped ComplexOrder

/-- A Hermitian idempotent equals its square root defined by real functional calculus. -/
theorem hermitian_projection_half {D : ℕ} (P : HermitianMat (Fin D) ℂ)
    (hP : P.mat * P.mat = P.mat) : P ^ (1 / 2 : ℝ) = P := by
  have heq : P.cfc (fun x => x * x) = P.cfc id := by
    apply HermitianMat.ext
    simpa only [HermitianMat.mat_cfc_mul_apply, HermitianMat.cfc_id, HermitianMat.cfc_id'] using hP
  have hspec := (HermitianMat.cfc_eq_cfc_iff_eqOn (A := P) (fun x => x*x) id).mp heq
  rw [HermitianMat.rpow_eq_cfc]
  nth_rw 2 [← HermitianMat.cfc_id P]
  apply HermitianMat.cfc_congr
  intro x hx
  have hxx : x * x = x := hspec hx
  have hz : x = 0 ∨ x = 1 := by
    have hprod : x * (x - 1) = 0 := by nlinarith only [hxx]
    exact (mul_eq_zero.mp hprod).imp id (fun h => sub_eq_zero.mp h)
  rcases hz with rfl | rfl <;> norm_num

/-- A Hermitian idempotent is nonnegative. -/
theorem hermitian_projection_nonneg {D : ℕ} (P : HermitianMat (Fin D) ℂ)
    (hP : P.mat * P.mat = P.mat) : 0 ≤ P := by
  apply HermitianMat.zero_le_iff.mpr
  have h := Matrix.posSemidef_conjTranspose_mul_self P.mat
  simpa only [HermitianMat.conjTranspose_mat, hP] using h

/-- The complement of a Hermitian idempotent is idempotent. -/
theorem complement_projection {D : ℕ} (P : HermitianMat (Fin D) ℂ)
    (hP : P.mat * P.mat = P.mat) :
    (1 - P).mat * (1 - P).mat = (1 - P).mat := by
  simp only [HermitianMat.mat_sub, HermitianMat.mat_one]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hP]
  abel

/-- The Boolean-outcome POVM with effect `P` for `true` and effect `1 - P` for `false`. -/
noncomputable def binaryProjectivePOVM {D : ℕ} (P : HermitianMat (Fin D) ℂ)
    (hP : P.mat * P.mat = P.mat) : POVM Bool (Fin D) where
  mats o := if o then P else 1 - P
  nonneg o := by
    cases o
    · exact hermitian_projection_nonneg _ (complement_projection P hP)
    · exact hermitian_projection_nonneg P hP
  normalized := by simp

end Qatlib.Concepts.InstrumentCore.PovmBridge
