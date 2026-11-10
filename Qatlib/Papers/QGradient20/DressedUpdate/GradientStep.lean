/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.DressedUpdate.Encoding
import Qatlib.Papers.QGradient20.Polynomial.Scaling
import Qatlib.Papers.QGradient20.FilterBranch.ActualVector
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QGradient20.DressedUpdate
open Qatlib.Papers.QGradient20.Polynomial
open Qatlib.Papers.QGradient20.FilterBranch
variable {I : Type} [Fintype I] [DecidableEq I]

def complexDerivative {p : ℕ} (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) : Matrix (Option I) (Option I) ℂ :=
  fun i j => (derivativeMatrix A (dressed x) i j : ℂ)

def updateScale {p : ℕ} (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) : ℝ := spectralScale (complexDerivative A x)

theorem derivativeAction_encoded {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (x : I → ℝ) (i : Option I) :
    derivativeAction (complexDerivative A x) (encoded x) i =
      ((updateScale A x)⁻¹ * gradient A (dressed x) i : ℝ) := by
  change (normalizedMatrix (complexDerivative A x) *ᵥ (encoded x).ofLp) i = _
  rw [← derivativeMatrix_mulVec A (dressed x)]
  simp only [normalizedMatrix, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Complex.real_smul, complexDerivative, encoded, WithLp.ofLp_toLp, updateScale,
    Complex.ofReal_mul, Complex.ofReal_sum]
  rw [Finset.mul_sum]
  simp only [mul_assoc]

def outputVector {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (ascent : Bool) : EuclideanSpace ℂ (Option I) :=
  successfulVector none (complexDerivative A x) ξ ascent (encoded x)

theorem outputVector_none {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (ascent : Bool) :
    outputVector A x ξ ascent none = (((1 + ξ)⁻¹ * normalizer x : ℝ) : ℂ) := by
  simp [outputVector, successfulVector, update, project_apply, encoded_none, Complex.real_smul]

theorem outputVector_some {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (ascent : Bool) (i : I) :
    outputVector A x ξ ascent (some i) =
      (((1 + ξ)⁻¹ * (normalizer x * x i + branchSign ascent * ξ *
        ((updateScale A x)⁻¹ * gradient A (dressed x) (some i))) : ℝ) : ℂ) := by
  change (((1 + ξ)⁻¹ : ℝ) •
    (encoded x + (branchSign ascent * ξ) • project none (derivativeAction (complexDerivative A x) (encoded x)))) (some i) = _
  simp only [PiLp.smul_apply, PiLp.add_apply, project_apply, Option.some_ne_none, ite_false,
    derivativeAction_encoded, encoded_some, Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]

def decodedRate {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) : ℝ := ξ * normalizer x ^ (2 * (p - 1)) / updateScale A x

theorem outputVector_decode {p : ℕ} (hp : 0 < p)
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (hξ : 0 ≤ ξ) (ascent : Bool) (i : I) :
    outputVector A x ξ ascent (some i) / outputVector A x ξ ascent none =
      ((x i + branchSign ascent * decodedRate A x ξ * gradient A (homogeneousInput x) (some i) : ℝ) : ℂ) := by
  rw [outputVector_none, outputVector_some]
  have hc := (normalizer_pos x).ne'
  have hα := (spectralScale_pos (complexDerivative A x)).ne'
  have hη : 1 + ξ ≠ 0 := by linarith
  have hg : gradient A (dressed x) (some i) =
      normalizer x ^ (2 * p - 1) * gradient A (homogeneousInput x) (some i) :=
    gradient_scale hp A (homogeneousInput x) (normalizer x) (some i)
  rw [hg, show 2 * p - 1 = 2 * (p - 1) + 1 by omega, pow_succ]
  rw [← Complex.ofReal_div]
  congr 1
  unfold decodedRate
  change (1+ξ)⁻¹*(normalizer x*x i+branchSign ascent*ξ*((updateScale A x)⁻¹*
    (normalizer x^(2*(p-1))*normalizer x*gradient A (homogeneousInput x) (some i)))) /
      ((1+ξ)⁻¹*normalizer x)=_
  field_simp [hc, hη, updateScale, hα]

theorem outputVector_mass_third {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) :
    (1 / 4 : ℝ) ≤ ‖outputVector A x (1 / 3) ascent‖ ^ 2 :=
  successMass_third none (complexDerivative A x) ascent (encoded x) (encoded_norm x)

end Qatlib.Papers.QGradient20.DressedUpdate
