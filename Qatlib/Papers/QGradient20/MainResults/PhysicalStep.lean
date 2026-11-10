/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.DressedUpdate.Stationary
import Qatlib.Papers.QGradient20.FilterBranch.Operator
import Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn
set_option warningAsError false

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

def inputState (x : I → ℝ) : MState (Option I) :=
    MState.pure (ContractionBorn.ketOfUnit (encoded x) (encoded_norm x))

def gradientReadout {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ξ : ℝ) (hξ : 0 ≤ ξ) (ascent : Bool) : POVM Bool (Option I) :=
  ContractionInstrument.readout (successOperator none (complexDerivative A x) ξ ascent)
    (successOperator_norm none (complexDerivative A x) hξ ascent)

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

theorem actual_success_probability {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) :
    (1/4 : ℝ) ≤ (((gradientReadout A x (1/3) (by norm_num) ascent).measure (inputState x)) true : ℝ) := by
  rw [actual_gradient_Born]
  exact outputVector_mass_third A x ascent

theorem actual_success_gt_source {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) :
    (3/16 : ℝ) < (((gradientReadout A x (1/3) (by norm_num) ascent).measure (inputState x)) true : ℝ) := by
  linarith [actual_success_probability A x ascent]

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
