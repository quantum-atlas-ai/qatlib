/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument

/-!
# Born probabilities for contraction dilations

The success branch of a contraction readout sends a pure state to the outer product of its image
under the contraction. Its Born probability is therefore the squared output norm. The stacked
success and failure Kraus matrices form an isometry and induce a channel with an explicit
Boolean outcome register.

The mathematical background is described in [Watrous2018].

## Main statements

* `native_success_Born`: success probability is the squared contracted norm.
* `stack_gram`: the stacked Kraus matrix is isometric.
* `stack_success`: the successful flag contains the contracted vector.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator
open Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument

namespace Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The success completely positive map sends a pure-state density matrix to the outer product
of the vector `Bψ`. -/
theorem success_pure_matrix (B : Matrix I I ℂ) (ψ : _root_.Ket I) :
    (successCP B).map (MState.pure ψ).m=
      Matrix.vecMulVec (B*ᵥ(ψ : I→ℂ)) (fun j => star ((B*ᵥ(ψ : I→ℂ)) j)) := by
  rw [successCP_matrix]
  have hp : (MState.pure ψ).m=Matrix.vecMulVec (ψ : I→ℂ) (fun j => star (ψ j)) := by
    ext i j
    exact MState.pure_apply (ψ:=ψ)
  rw [hp,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul]
  congr 1
  funext j
  simp [Matrix.vecMul,Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,mul_comm]

/-- The real trace of the success branch on a pure state is the squared Euclidean norm of `Bψ`. -/
theorem success_pure_trace (B : Matrix I I ℂ) (ψ : _root_.Ket I) :
    ((successCP B).map (MState.pure ψ).m).trace.re=
      ‖(WithLp.toLp 2 (B*ᵥ(ψ : I→ℂ)) : EuclideanSpace ℂ I)‖^2 := by
  rw [success_pure_matrix,EuclideanSpace.norm_sq_eq]
  simp only [Matrix.trace,Matrix.vecMulVec_apply,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,
    Matrix.diag,Complex.re_sum,Complex.ofReal_re]

/-- For a contraction `B`, the native Boolean readout succeeds on a pure state with probability
equal to `‖Bψ‖²`. -/
theorem native_success_Born (B : Matrix I I ℂ) (hB : ‖B‖≤1) (ψ : _root_.Ket I) :
    (((readout B hB).measure (MState.pure ψ)) true : ℝ)=
      ‖(WithLp.toLp 2 (B*ᵥ(ψ : I→ℂ)) : EuclideanSpace ℂ I)‖^2 := by
  rw [success_probability_trace,success_pure_trace]

/-- A normalized ket constructed from a Euclidean vector of norm one. -/
def ketOfUnit (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) : _root_.Ket I where
  vec := WithLp.ofLp x
  normalized' := by simpa only [hx,one_pow] using (EuclideanSpace.norm_sq_eq x).symm

/-- For a unit Euclidean input vector, the success probability of a contraction readout is the
squared norm of its image under `B`. See [GaoEtAl2021]. -/
theorem native_success_Born_unit (B : Matrix I I ℂ) (hB : ‖B‖≤1)
    (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) :
    (((readout B hB).measure (MState.pure (ketOfUnit x hx))) true : ℝ)=
      ‖(WithLp.toLp 2 (B*ᵥWithLp.ofLp x) : EuclideanSpace ℂ I)‖^2 :=
  native_success_Born B hB (ketOfUnit x hx)

/-- The matrix stacking the failure and success Kraus matrices along a Boolean outcome register. -/
def stack (B : Matrix I I ℂ) (hB : ‖B‖≤1) : Matrix (I×Bool) I ℂ :=
  fun x j => kraus B hB x.2 x.1 j

/-- The stacked Kraus matrix of a contraction has adjoint product equal to the identity. -/
theorem stack_gram (B : Matrix I I ℂ) (hB : ‖B‖≤1) : (stack B hB)ᴴ*stack B hB=1 := by
  ext i j
  have h := congrFun (congrFun (kraus_complete B hB) i) j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,stack,Fintype.sum_prod_type,
    Matrix.sum_apply] at h ⊢
  rw [Finset.sum_comm]
  exact h

/-- The Boolean component of the stacked matrix output equals the corresponding Kraus matrix
applied to the input. -/
theorem stack_action (B : Matrix I I ℂ) (hB : ‖B‖≤1) (x : I→ℂ) (i : I) (b : Bool) :
    (stack B hB*ᵥx) (i,b)=(kraus B hB b*ᵥx) i := rfl

/-- The quantum channel induced by the single isometric Kraus matrix `stack B hB`. -/
def isometryChannel (B : Matrix I I ℂ) (hB : ‖B‖≤1) : CPTPMap I (I×Bool) ℂ :=
  CPTPMap.of_kraus_CPTPMap (fun _ : Unit => stack B hB) (by simpa using stack_gram B hB)

/-- The `true` component of the stacked contraction dilation is exactly `B` applied to the
input. -/
theorem stack_success (B : Matrix I I ℂ) (hB : ‖B‖≤1) (x : I→ℂ) (i : I) :
    (stack B hB*ᵥx) (i,true)=(B*ᵥx) i := rfl

end Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn
