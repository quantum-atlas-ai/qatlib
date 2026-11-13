/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.DressedUpdate.Encoding
import Qatlib.Papers.QGradient20.Polynomial.Scaling
import Qatlib.Papers.QGradient20.FilterBranch.ActualVector

/-!
# Decoding the dressed gradient update

`complexDerivative` and `updateScale` define the normalized derivative action used by
`outputVector`. Explicit coordinate formulas show that decoding the successful vector yields a
classical gradient step with rate `decodedRate`, and the one-third branch parameter has squared
norm at least one quarter. The mathematical context is [GaoEtAl2021].

## Main statements

* `outputVector_decode`: For positive tensor order and nonnegative `ξ`, decoding the successful
  vector gives `x` plus the signed gradient at the homogeneous input multiplied by
  `decodedRate`.
* `outputVector_mass_third`: At branch parameter `ξ = 1/3`, the successful dressed vector has
  squared norm at least `1/4`.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QGradient20.DressedUpdate
open Qatlib.Papers.QGradient20.Polynomial
open Qatlib.Papers.QGradient20.FilterBranch
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The complex matrix obtained from the real polynomial derivative matrix evaluated on the
dressed input. -/
def complexDerivative {p : ℕ} (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) : Matrix (Option I) (Option I) ℂ :=
  fun i j => (derivativeMatrix A (dressed x) i j : ℂ)

/-- The spectral normalization scale of `complexDerivative A x`. -/
def updateScale {p : ℕ} (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) : ℝ := spectralScale (complexDerivative A x)

/-- The normalized derivative action on the encoded input equals the dressed polynomial gradient
divided by `updateScale`, coordinatewise. -/
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

/-- The successful filter vector for the dressed input, with the homogeneous constant coordinate
removed from the derivative contribution. -/
def outputVector {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (ascent : Bool) : EuclideanSpace ℂ (Option I) :=
  successfulVector none (complexDerivative A x) ξ ascent (encoded x)

/-- The constant coordinate of the successful vector is `normalizer x / (1+ξ)`, coerced to the
complex numbers. -/
theorem outputVector_none {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (ascent : Bool) :
    outputVector A x ξ ascent none = (((1 + ξ)⁻¹ * normalizer x : ℝ) : ℂ) := by
  simp [outputVector, successfulVector, update, project_apply, encoded_none, Complex.real_smul]

/-- Each nonconstant successful coordinate is the scaled sum of the encoded input coordinate and
the signed normalized-gradient contribution. -/
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

/-- The decoded gradient-step rate `ξ * normalizer x^(2*(p-1)) / updateScale A x`. -/
def decodedRate {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) : ℝ := ξ * normalizer x ^ (2 * (p - 1)) / updateScale A x

/-- For positive tensor order and nonnegative `ξ`, decoding the successful vector gives `x` plus
the signed gradient at the homogeneous input multiplied by `decodedRate`. See [GaoEtAl2021]. -/
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

/-- At branch parameter `ξ = 1/3`, the successful dressed vector has squared norm at least
`1/4`. -/
theorem outputVector_mass_third {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) :
    (1 / 4 : ℝ) ≤ ‖outputVector A x (1 / 3) ascent‖ ^ 2 :=
  successMass_third none (complexDerivative A x) ascent (encoded x) (encoded_norm x)

end Qatlib.Papers.QGradient20.DressedUpdate
