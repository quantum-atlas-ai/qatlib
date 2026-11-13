/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.DressedUpdate.Stationary
import Qatlib.Papers.QGradient20.FilterBranch.Operator
import Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn

/-!
# Physical readout of a polynomial gradient step

The pure state `inputState` and binary measurement `gradientReadout` realize the dressed
polynomial update. The module identifies the successful Born weight and density matrix, bounds
the success probability at parameter 1/3, and relates decoded coordinates to the polynomial
gradient. See [GaoEtAl2021] for the paper context.

## Main statements

* `actual_gradient_Born`: The successful outcome of `gradientReadout` on `inputState` has
  probability equal to the squared norm of `outputVector`.
* `actual_success_probability`: At parameter `ξ = 1/3`, the successful gradient readout has
  probability at least 1/4.
* `actual_polynomial_step`: For positive tensor degree and symmetric coefficients, the gradient
  is the coordinate derivative of the homogeneous objective and the decoded output coordinate
  equals the signed gradient update with rate `decodedRate`.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open Qatlib.Concepts.ChannelTheory.Naimark
open scoped BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.QGradient20.MainResults.PhysicalStep
open Qatlib.Papers.QGradient20.Polynomial
open Qatlib.Papers.QGradient20.DressedUpdate
open Qatlib.Papers.QGradient20.FilterBranch
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The pure density state associated with the normalized dressed encoding of `x`. -/
def inputState (x : I → ℝ) : MState (Option I) :=
    MState.pure (ContractionBorn.ketOfUnit (encoded x) (encoded_norm x))

/-- The binary POVM associated with the polynomial update success operator, for nonnegative
parameter `ξ` and the selected ascent or descent branch. -/
def gradientReadout {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (hξ : 0 ≤ ξ) (ascent : Bool) : POVM Bool (Option I) :=
  ContractionInstrument.readout (successOperator none (complexDerivative A x) ξ ascent)
    (successOperator_norm none (complexDerivative A x) hξ ascent)

/-- The successful outcome of `gradientReadout` on `inputState` has probability equal to the
squared norm of `outputVector`. See [GaoEtAl2021]. -/
theorem actual_gradient_Born {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (hξ : 0 ≤ ξ) (ascent : Bool) :
    (((gradientReadout A x ξ hξ ascent).measure (inputState x)) true : ℝ) =
      ‖outputVector A x ξ ascent‖ ^ 2 := by
  unfold gradientReadout inputState
  rw [ContractionBorn.native_success_Born_unit]
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Option I))
    (successOperator none (complexDerivative A x) ξ ascent) (encoded x)‖ ^ 2 = _
  rw [successOperator_action]
  rfl

/-- At parameter `ξ = 1/3`, the successful gradient readout has probability at least 1/4. See
[GaoEtAl2021]. -/
theorem actual_success_probability {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) :
    (1/4 : ℝ) ≤ (((gradientReadout A x (1/3) (by norm_num) ascent).measure (inputState x)) true : ℝ) := by
  rw [actual_gradient_Born]
  exact outputVector_mass_third A x ascent

/-- At parameter `ξ = 1/3`, the successful gradient readout has probability strictly greater
than 3/16. See [GaoEtAl2021]. -/
theorem actual_success_gt_source {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) :
    (3/16 : ℝ) < (((gradientReadout A x (1/3) (by norm_num) ascent).measure (inputState x)) true : ℝ) := by
  linarith [actual_success_probability A x ascent]

/-- Applying the successful completely positive map to `inputState` gives the outer product of
`outputVector` with its conjugate. -/
theorem actual_success_density {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (ascent : Bool) :
    (ContractionInstrument.successCP (successOperator none (complexDerivative A x) ξ ascent)).map (inputState x).m =
      Matrix.vecMulVec (outputVector A x ξ ascent).ofLp (fun j => star (outputVector A x ξ ascent j)) := by
  rw [inputState, ContractionBorn.success_pure_matrix]
  have he : (successOperator none (complexDerivative A x) ξ ascent *ᵥ (encoded x).ofLp) =
      (outputVector A x ξ ascent).ofLp := by
    exact congrArg WithLp.ofLp
        (successOperator_action none (complexDerivative A x) ξ ascent (encoded x))
  change Matrix.vecMulVec (successOperator none (complexDerivative A x) ξ ascent *ᵥ (encoded x).ofLp)
    (fun j => star ((successOperator none (complexDerivative A x) ξ ascent *ᵥ (encoded x).ofLp) j)) = _
  rw [he]

/-- For positive tensor degree and symmetric coefficients, the gradient is the coordinate
derivative of the homogeneous objective and the decoded output coordinate equals the signed
gradient update with rate `decodedRate`. See [GaoEtAl2021]. -/
theorem actual_polynomial_step {p : ℕ} (hp : 0 < p)
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (hA : A.IsSymm)
    (x : I → ℝ) (ξ : ℝ) (hξ : 0 ≤ ξ) (ascent : Bool) (i : I) :
    HasDerivAt (fun t : ℝ => objective A (fun j => homogeneousInput x j +
      t * ((Pi.single (some i) (1 : ℝ) : Option I → ℝ) j)))
      (gradient A (homogeneousInput x) (some i)) 0 ∧
    outputVector A x ξ ascent (some i) / outputVector A x ξ ascent none =
      ((x i + branchSign ascent * decodedRate A x ξ * gradient A (homogeneousInput x) (some i) : ℝ) : ℂ) :=
  ⟨objective_partial A hA _ _, outputVector_decode hp A x ξ hξ ascent i⟩

end Qatlib.Papers.QGradient20.MainResults.PhysicalStep
