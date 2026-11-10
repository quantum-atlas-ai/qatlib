/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.DressedUpdate.GradientStep
import Mathlib.LinearAlgebra.Matrix.Hermitian
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QGradient20.DressedUpdate
open Qatlib.Papers.QGradient20.Polynomial
open Qatlib.Papers.QGradient20.FilterBranch
variable {I : Type} [Fintype I] [DecidableEq I]

theorem complexDerivative_hermitian {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (hA : A.IsSymm) (x : I → ℝ) :
    (complexDerivative A x).IsHermitian := by
  change (complexDerivative A x)ᴴ=complexDerivative A x
  ext i j
  simp only [Matrix.conjTranspose_apply, complexDerivative]
  change (starRingEnd ℂ) ((derivativeMatrix A (dressed x) j i : ℝ) : ℂ) = _
  rw [Complex.conj_ofReal]
  have h := congrArg (fun B : Matrix (Option I) (Option I) ℝ => B i j)
    (derivativeMatrix_symmetric A hA (dressed x)).eq
  exact congrArg Complex.ofReal h

theorem decodedRate_pos {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) {ξ : ℝ} (hξ : 0 < ξ) : 0 < decodedRate A x ξ := by
  exact div_pos (mul_pos hξ (pow_pos (normalizer_pos x) _)) (spectralScale_pos _)

theorem decoded_stationary_iff {p : ℕ} (hp : 0 < p)
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) {ξ : ℝ} (hξ : 0 < ξ) (ascent : Bool) :
    (∀ i, outputVector A x ξ ascent (some i) / outputVector A x ξ ascent none = (x i : ℂ)) ↔
      ∀ i, gradient A (homogeneousInput x) (some i) = 0 := by
  have hs : branchSign ascent ≠ 0 := by cases ascent <;> norm_num [branchSign]
  have hr := (decodedRate_pos A x hξ).ne'
  constructor
  · intro h i
    have hi := h i
    rw [outputVector_decode hp A x ξ hξ.le ascent i] at hi
    have hi' := Complex.ofReal_injective hi
    have he :
        branchSign ascent * decodedRate A x ξ * gradient A (homogeneousInput x) (some i) = 0 := by
          linarith
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hs hr)
  · intro h i
    rw [outputVector_decode hp A x ξ hξ.le ascent i, h i]
    simp

theorem stationary_actual_partials {p : ℕ} (hp : 0 < p)
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (hA : A.IsSymm)
    (x : I → ℝ) {ξ : ℝ} (hξ : 0 < ξ) (ascent : Bool)
    (hfix : ∀ i, outputVector A x ξ ascent (some i) / outputVector A x ξ ascent none = (x i : ℂ))
    (i : I) :
    HasDerivAt (fun t : ℝ => objective A (fun j => homogeneousInput x j +
      t * ((Pi.single (some i) (1 : ℝ) : Option I → ℝ) j))) 0 0 := by
  have hg := (decoded_stationary_iff hp A x hξ ascent).mp hfix i
  simpa only [hg] using objective_partial A hA (homogeneousInput x) (some i)

end Qatlib.Papers.QGradient20.DressedUpdate
