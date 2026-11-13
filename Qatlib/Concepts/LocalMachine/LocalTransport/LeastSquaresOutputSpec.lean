/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.PseudoinverseState

/-!
# Least squares solution states and postselection

`leastSquaresVector` applies the Moore-Penrose pseudoinverse to the input, while
`IsEuclideanLeastSquares` specifies a residual minimizer of minimum norm. The module proves the
normal equations, orthogonal residual decomposition, and uniqueness properties underlying the
quantum linear systems setting of [HarrowHassidimLloyd2009].

`IsLeastSquaresSolutionState` specifies approximation to the normalized solution direction.
Block-encoding and counted QSVT results connect this specification to postselection probability
and output error, and an augmented matrix formulation gives a unique ridge-regularized
minimizer.

## Main statements

* `leastSquares_minimum_residual_and_norm`: the pseudoinverse solution minimizes residual and
  norm.
* `leastSquares_actual_postselection`: bound success probability and normalized solution error.
* `ridge_regularized_unique_minimizer`: positive regularization yields a unique minimizer.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Matrix
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

/-- The vector obtained by applying the Moore-Penrose pseudoinverse of `A` to `b`. -/
noncomputable def leastSquaresVector {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) : QState I :=
  matrixPseudoinverse A *ᵥ b

/-- The Euclidean norm of the projection of `b` given by `A * matrixPseudoinverse A`. -/
noncomputable def leastSquaresOverlap {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) : ℝ :=
  ‖stateVector ((A * matrixPseudoinverse A) *ᵥ b)‖

/-- The property that `x` minimizes the Euclidean residual and has minimum norm among all
residual minimizers. -/
def IsEuclideanLeastSquares {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (x : QState I) : Prop :=
  (∀ y : QState I, ‖stateVector (A *ᵥ x - b)‖ ≤ ‖stateVector (A *ᵥ y - b)‖) ∧
    ∀ y : QState I,
      (∀ z : QState I, ‖stateVector (A *ᵥ y - b)‖ ≤ ‖stateVector (A *ᵥ z - b)‖) →
        ‖stateVector x‖ ≤ ‖stateVector y‖

/-- The normalized pseudoinverse solution, or `none` when the pseudoinverse solution is zero. -/
noncomputable def leastSquaresDirection {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) : Option (QState I) :=
  if leastSquaresVector A b = 0 then none
  else some (PostMeasure (leastSquaresVector A b) Finset.univ)

/-- The property that `φ` is normalized and lies within `η` of the normalized direction of a
nonzero minimum-norm least squares solution. -/
def IsLeastSquaresSolutionState {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (φ : QState I)
    (η : ℝ) : Prop :=
  ∃ x : QState I, IsEuclideanLeastSquares A b x ∧ x ≠ 0 ∧ Normalized φ ∧
    ‖stateVector φ - NormedSpace.normalize (stateVector x)‖ ≤ η

/-- The matrix formed by stacking `A` above `sqrt lam` times the identity. -/
noncomputable def ridgeAugmentedMatrix {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (lam : ℝ) : Matrix (O ⊕ I) I ℂ :=
  Matrix.fromRows A ((Real.sqrt lam : ℂ) • 1)

/-- Extend the input vector by zero on the added coordinates of the ridge-augmented system. -/
def ridgeAugmentedInput {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (b : QState O) : QState (O ⊕ I) :=
  Sum.elim b 0

section InnerProduct

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- The pure-state inner product is additive in its first argument. -/
theorem Inner_add_left (u v w : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (u + v) w = Qatlib.Foundations.PureStateMath.Inner u w + Qatlib.Foundations.PureStateMath.Inner v w := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [star_add, add_dotProduct]

omit [DecidableEq I] in

/-- The pure-state inner product is additive in its second argument. -/
theorem Inner_add_right (u v w : QState I) :
    Qatlib.Foundations.PureStateMath.Inner u (v + w) = Qatlib.Foundations.PureStateMath.Inner u v + Qatlib.Foundations.PureStateMath.Inner u w := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [dotProduct_add]

omit [DecidableEq I] in

/-- The pure-state inner product distributes over subtraction in its second argument. -/
theorem Inner_sub_right (u v w : QState I) :
    Qatlib.Foundations.PureStateMath.Inner u (v - w) = Qatlib.Foundations.PureStateMath.Inner u v - Qatlib.Foundations.PureStateMath.Inner u w := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [dotProduct_sub]

omit [DecidableEq I] in

/-- The pure-state inner product with the zero vector in its second argument vanishes. -/
theorem Inner_zero_right (u : QState I) : Qatlib.Foundations.PureStateMath.Inner u 0 = 0 := by
    simp [Qatlib.Foundations.PureStateMath.Inner]

/-- Exchanging the arguments of the pure-state inner product takes its complex conjugate. -/
theorem Inner_rev (u v : QState I) : Qatlib.Foundations.PureStateMath.Inner v u = (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Inner u v) := by
  rw [inner_apply, inner_apply,
    show (∑ i, (starRingEnd ℂ) (v i) * u i)
      = (starRingEnd ℂ) (∑ i, (starRingEnd ℂ) (u i) * v i) from by
      rw [map_sum (starRingEnd ℂ) (fun i => (starRingEnd ℂ) (u i) * v i) Finset.univ]
      exact Finset.sum_congr rfl fun i _ => by
        have h : (starRingEnd ℂ) ((starRingEnd ℂ) (u i)) = u i := star_star (u i)
        rw [map_mul, h]
        ring]

omit [DecidableEq I] in

/-- Move a matrix from the first argument of the inner product to its conjugate transpose in the
second argument. -/
theorem Inner_mulVec {O : Type} [Fintype O] (A : Matrix O I ℂ) (u : QState I) (v : QState O) :
    Qatlib.Foundations.PureStateMath.Inner (A *ᵥ u) v = Qatlib.Foundations.PureStateMath.Inner u (Aᴴ *ᵥ v) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, star_mulVec, dotProduct_mulVec]

omit [DecidableEq I] in

/-- The squared Euclidean norm of a state vector is the sum of the squared norms of its
coordinates. -/
theorem stateVector_norm_sq_sum (ψ : QState I) :
    ‖stateVector ψ‖ ^ 2 = ∑ i, ‖ψ i‖ ^ 2 := by
  rw [stateVector_norm_sq]
  simp [MeasureProb, BornProb]

/-- The squared Euclidean norm of a state vector equals the real part of its inner product with
itself. -/
theorem stateVector_norm_sq_eq_re_inner (ψ : QState I) :
    ‖stateVector ψ‖ ^ 2 = (Qatlib.Foundations.PureStateMath.Inner ψ ψ).re := by
  rw [inner_self, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact stateVector_norm_sq_sum ψ

omit [DecidableEq I] in

/-- Expand the inner product of `u + v` with itself into its four constituent terms. -/
theorem Inner_add_add (u v : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (u + v) (u + v) = Qatlib.Foundations.PureStateMath.Inner u u + Qatlib.Foundations.PureStateMath.Inner u v + Qatlib.Foundations.PureStateMath.Inner v u + Qatlib.Foundations.PureStateMath.Inner v v := by
  rw [Inner_add_left, Inner_add_right, Inner_add_right]
  ring

/-- Orthogonal state vectors satisfy the Pythagorean identity for their sum. -/
theorem stateVector_norm_sq_add_of_inner_eq_zero {O : Type} [Fintype O] [DecidableEq O]
    {u v : QState O} (h : Qatlib.Foundations.PureStateMath.Inner u v = 0) :
    ‖stateVector (u + v)‖ ^ 2 = ‖stateVector u‖ ^ 2 + ‖stateVector v‖ ^ 2 := by
  have hv : Qatlib.Foundations.PureStateMath.Inner v u = 0 := by
    rw [Inner_rev, h]
    simp
  rw [stateVector_norm_sq_eq_re_inner, stateVector_norm_sq_eq_re_inner,
    stateVector_norm_sq_eq_re_inner, Inner_add_add, h, hv]
  simp [Complex.add_re]

omit [Fintype I] [DecidableEq I] in

/-- Conversion to a Euclidean state vector preserves subtraction. -/
theorem stateVector_sub {O : Type} (u v : QState O) :
    stateVector (u - v) = stateVector u - stateVector v := rfl

omit [Fintype I] [DecidableEq I] in

/-- Conversion to a Euclidean state vector preserves addition. -/
theorem stateVector_add {O : Type} (u v : QState O) :
    stateVector (u + v) = stateVector u + stateVector v := rfl

omit [Fintype I] [DecidableEq I] in

/-- Conversion to a Euclidean state vector preserves multiplication by a real scalar. -/
theorem stateVector_real_smul {O : Type} (r : ℝ) (u : QState O) :
    stateVector (r • u) = r • stateVector u := rfl

end InnerProduct

section Penrose

variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

omit [DecidableEq O] in

/-- The conjugate transpose of `A` is unchanged by right multiplication by `A *
matrixPseudoinverse A`. -/
theorem conjTranspose_mul_mul_matrixPseudoinverse (A : Matrix O I ℂ) :
    Aᴴ * (A * matrixPseudoinverse A) = Aᴴ := by
  calc
    Aᴴ * (A * matrixPseudoinverse A) = (A * matrixPseudoinverse A * A)ᴴ := by
      rw [Matrix.conjTranspose_mul, mul_matrixPseudoinverse_adjoint]
    _ = Aᴴ := congrArg Matrix.conjTranspose (mul_matrixPseudoinverse_mul A)

omit [DecidableEq O] in

/-- The product of the pseudoinverse, its conjugate transpose, and `A`'s conjugate transpose
equals the pseudoinverse. -/
theorem matrixPseudoinverse_mul_conjTranspose_mul_conjTranspose (A : Matrix O I ℂ) :
    matrixPseudoinverse A * (matrixPseudoinverse A)ᴴ * Aᴴ = matrixPseudoinverse A := by
  rw [Matrix.mul_assoc, ← Matrix.conjTranspose_mul, mul_matrixPseudoinverse_adjoint,
    ← Matrix.mul_assoc, matrixPseudoinverse_mul_self]

/-- The projector `matrixPseudoinverse A * A` fixes the least squares solution vector. -/
theorem matrixPseudoinverse_mul_mulVec_pseudoinverse (A : Matrix O I ℂ) (b : QState O) :
    (matrixPseudoinverse A * A) *ᵥ leastSquaresVector A b = leastSquaresVector A b := by
  show (matrixPseudoinverse A * A) *ᵥ (matrixPseudoinverse A *ᵥ b) =
    matrixPseudoinverse A *ᵥ b
  rw [Matrix.mulVec_mulVec, matrixPseudoinverse_mul_self]

omit [DecidableEq O] in

/-- Projecting any solution of the normal equations by `matrixPseudoinverse A * A` gives the
pseudoinverse solution. -/
theorem normalSolution_project_mulVec (A : Matrix O I ℂ) (b : QState O) {y : QState I}
    (hy : Aᴴ *ᵥ (A *ᵥ y - b) = 0) :
    (matrixPseudoinverse A * A) *ᵥ y = matrixPseudoinverse A *ᵥ b := by
  have he := matrixPseudoinverse_mul_conjTranspose_mul_conjTranspose A
  have hz : (matrixPseudoinverse A * (matrixPseudoinverse A)ᴴ) *ᵥ (Aᴴ *ᵥ (A *ᵥ y - b)) = 0 := by
    rw [hy]
    exact Matrix.mulVec_zero _
  rw [Matrix.mulVec_mulVec, he, Matrix.mulVec_sub, Matrix.mulVec_mulVec, sub_eq_zero] at hz
  exact hz

end Penrose

/-- The pseudoinverse solution satisfies the normal equations, maps to the projected input, and
gives orthogonal projected and residual components. -/
theorem leastSquares_projection_and_normal {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) :
    Aᴴ *ᵥ (A *ᵥ leastSquaresVector A b - b) = 0 ∧
    A *ᵥ leastSquaresVector A b = (A * matrixPseudoinverse A) *ᵥ b ∧
    Qatlib.Foundations.PureStateMath.Inner ((A * matrixPseudoinverse A) *ᵥ b) (b - (A * matrixPseudoinverse A) *ᵥ b) = 0 := by
  have he := conjTranspose_mul_mul_matrixPseudoinverse A
  refine ⟨?_, Matrix.mulVec_mulVec _ _ _, ?_⟩
  · show Aᴴ *ᵥ (A *ᵥ (matrixPseudoinverse A *ᵥ b) - b) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec b A (matrixPseudoinverse A),
      Matrix.mulVec_mulVec b Aᴴ (A * matrixPseudoinverse A), he, sub_self]
  · rw [Inner_sub_right, Inner_mulVec, mul_matrixPseudoinverse_adjoint, Inner_mulVec,
      mul_matrixPseudoinverse_adjoint,
      Matrix.mulVec_mulVec b (A * matrixPseudoinverse A) (A * matrixPseudoinverse A),
      (matrixPseudoinverse_projectors A).1.1, sub_self]

/-- The squared residual at any vector splits into the optimal squared residual and the squared
norm of its image displacement from the pseudoinverse solution. -/
theorem leastSquares_residual_pythagoras {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (y : QState I) :
    ‖stateVector (A *ᵥ y - b)‖^2 = ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖^2 +
      ‖stateVector (A *ᵥ (y - leastSquaresVector A b))‖^2 := by
  have hnormal := (leastSquares_projection_and_normal A b).1
  have hdecomp : A *ᵥ y - b =
      (A *ᵥ leastSquaresVector A b - b) + A *ᵥ (y - leastSquaresVector A b) := by
    rw [Matrix.mulVec_sub]
    abel
  have hcross : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ leastSquaresVector A b - b) (A *ᵥ (y - leastSquaresVector A b)) = 0 := by
    have h : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ (y - leastSquaresVector A b)) (A *ᵥ leastSquaresVector A b - b) = 0 := by
      rw [Inner_mulVec, hnormal, Inner_zero_right]
    rw [Inner_rev, h]
    simp
  rw [hdecomp, stateVector_norm_sq_add_of_inner_eq_zero hcross]

/-- The pseudoinverse solution minimizes residual and then norm; any minimum-norm least squares
solution with the same norm equals it. This supplies the minimum-norm solution property used
in [HarrowHassidimLloyd2009]. -/
theorem leastSquares_minimum_residual_and_norm {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) :
    IsEuclideanLeastSquares A b (leastSquaresVector A b) ∧
    (∀ y : QState I, IsEuclideanLeastSquares A b y →
      ‖stateVector y‖ = ‖stateVector (leastSquaresVector A b)‖ → y = leastSquaresVector A b) := by
  have hmin : ∀ y : QState I,
      ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ ≤ ‖stateVector (A *ᵥ y - b)‖ := by
    intro y
    have h := leastSquares_residual_pythagoras A b y
    have hsq : ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖^2 ≤
        ‖stateVector (A *ᵥ y - b)‖^2 := by
      rw [h]
      have hnn := sq_nonneg ‖stateVector (A *ᵥ (y - leastSquaresVector A b))‖
      linarith
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hnormmin : ∀ y : QState I,
      (∀ z : QState I, ‖stateVector (A *ᵥ y - b)‖ ≤ ‖stateVector (A *ᵥ z - b)‖) →
      ‖stateVector (leastSquaresVector A b)‖ ≤ ‖stateVector y‖ := by
    intro y hy
    have hEq : ‖stateVector (A *ᵥ y - b)‖ = ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ :=
      le_antisymm (hy _) (hmin y)
    have hAy : A *ᵥ y = A *ᵥ leastSquaresVector A b := by
      have h := leastSquares_residual_pythagoras A b y
      have h2 : ‖stateVector (A *ᵥ (y - leastSquaresVector A b))‖^2 = 0 := by
        have hEq2 := congrArg (· ^ 2) hEq
        linarith [sq_nonneg ‖stateVector (A *ᵥ (y - leastSquaresVector A b))‖]
      have h3 : A *ᵥ (y - leastSquaresVector A b) = 0 :=
        (stateVector_eq_zero_iff _).mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h2))
      rw [← sub_eq_zero, ← Matrix.mulVec_sub]
      exact h3
    have hnormaly : Aᴴ *ᵥ (A *ᵥ y - b) = 0 := by
      rw [hAy]
      exact (leastSquares_projection_and_normal A b).1
    have hproj := normalSolution_project_mulVec A b hnormaly
    show ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ ≤ ‖stateVector y‖
    rw [← hproj]
    calc ‖stateVector ((matrixPseudoinverse A * A) *ᵥ y)‖
        ≤ ‖matrixPseudoinverse A * A‖ * ‖stateVector y‖ := stateVector_mulVec_norm_le _ _
      _ ≤ 1 * ‖stateVector y‖ := mul_le_mul_of_nonneg_right
        (orthogonalProjector_spectralNorm_le_one (matrixPseudoinverse_projectors A).2)
        (norm_nonneg _)
      _ = ‖stateVector y‖ := one_mul _
  refine ⟨⟨hmin, hnormmin⟩, ?_⟩
  intro y hy hnormEq
  have hEq : ‖stateVector (A *ᵥ y - b)‖ = ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ :=
    le_antisymm (hy.1 _) (hmin y)
  have hAy : A *ᵥ (y - leastSquaresVector A b) = 0 := by
    have h := leastSquares_residual_pythagoras A b y
    have h2 : ‖stateVector (A *ᵥ (y - leastSquaresVector A b))‖^2 = 0 := by
      have hEq2 := congrArg (· ^ 2) hEq
      linarith [sq_nonneg ‖stateVector (A *ᵥ (y - leastSquaresVector A b))‖]
    exact (stateVector_eq_zero_iff _).mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h2))
  have hsupp : (matrixPseudoinverse A * A) *ᵥ leastSquaresVector A b =
      leastSquaresVector A b := matrixPseudoinverse_mul_mulVec_pseudoinverse A b
  have hInner : Qatlib.Foundations.PureStateMath.Inner (leastSquaresVector A b) (y - leastSquaresVector A b) = 0 := by
    nth_rewrite 1 [← hsupp]
    rw [Inner_mulVec, matrixPseudoinverse_mul_adjoint, ← Matrix.mulVec_mulVec, hAy,
      Matrix.mulVec_zero, Inner_zero_right]
  have hdecomp : y = leastSquaresVector A b + (y - leastSquaresVector A b) := by abel
  have hpyth := stateVector_norm_sq_add_of_inner_eq_zero hInner
  have hdsq : ‖stateVector (y - leastSquaresVector A b)‖^2 = 0 := by
    have h1 : ‖stateVector y‖^2 = ‖stateVector (leastSquaresVector A b)‖^2 :=
      congrArg (· ^ 2) hnormEq
    rw [hdecomp] at h1
    linarith [hpyth]
  have hd : y - leastSquaresVector A b = 0 :=
    (stateVector_eq_zero_iff _).mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdsq))
  exact sub_eq_zero.mp hd

/-- A vector minimizes the Euclidean residual if and only if it satisfies the normal equations. -/
theorem leastSquares_minimizer_iff_normal {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (y : QState I) :
    (∀ z : QState I, ‖stateVector (A *ᵥ y - b)‖ ≤ ‖stateVector (A *ᵥ z - b)‖) ↔
      Aᴴ *ᵥ (A *ᵥ y - b) = 0 := by
  constructor
  · intro hy
    have hmin := (leastSquares_minimum_residual_and_norm A b).1.1
    have hEq : ‖stateVector (A *ᵥ y - b)‖ = ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ :=
      le_antisymm (hy _) (hmin y)
    have hAy : A *ᵥ y = A *ᵥ leastSquaresVector A b := by
      have h := leastSquares_residual_pythagoras A b y
      have h2 : ‖stateVector (A *ᵥ (y - leastSquaresVector A b))‖^2 = 0 := by
        have hEq2 := congrArg (· ^ 2) hEq
        linarith [sq_nonneg ‖stateVector (A *ᵥ (y - leastSquaresVector A b))‖]
      have h3 : A *ᵥ (y - leastSquaresVector A b) = 0 :=
        (stateVector_eq_zero_iff _).mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h2))
      rw [← sub_eq_zero, ← Matrix.mulVec_sub]
      exact h3
    rw [hAy]
    exact (leastSquares_projection_and_normal A b).1
  · intro hy z
    have hdecomp : A *ᵥ z - b = (A *ᵥ y - b) + A *ᵥ (z - y) := by
      rw [Matrix.mulVec_sub]
      abel
    have hcross : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ y - b) (A *ᵥ (z - y)) = 0 := by
      have h : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ (z - y)) (A *ᵥ y - b) = 0 := by
        rw [Inner_mulVec, hy, Inner_zero_right]
      rw [Inner_rev, h]
      simp
    have hsq : ‖stateVector (A *ᵥ y - b)‖^2 ≤ ‖stateVector (A *ᵥ z - b)‖^2 := by
      rw [hdecomp, stateVector_norm_sq_add_of_inner_eq_zero hcross]
      have hnn := sq_nonneg ‖stateVector (A *ᵥ (z - y))‖
      linarith
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The least squares overlap vanishes exactly when the solution does, is bounded by the
solution norm for a contraction, and gives the orthogonal decomposition of the input norm. -/
theorem leastSquares_overlap_and_zero {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) :
    leastSquaresOverlap A b = ‖stateVector ((A * matrixPseudoinverse A) *ᵥ b)‖ ∧
    (leastSquaresOverlap A b = 0 ↔ leastSquaresVector A b = 0) ∧
    (‖A‖ ≤ 1 → leastSquaresOverlap A b ≤ ‖stateVector (leastSquaresVector A b)‖) ∧
    ‖stateVector b‖^2 = (leastSquaresOverlap A b)^2 +
      ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖^2 := by
  have hproj := leastSquares_projection_and_normal A b
  refine ⟨rfl, ?_, ?_, ?_⟩
  · constructor
    · intro h
      have hPb : (A * matrixPseudoinverse A) *ᵥ b = 0 :=
        (stateVector_eq_zero_iff _).mp (norm_eq_zero.mp h)
      have hx : leastSquaresVector A b =
          matrixPseudoinverse A *ᵥ ((A * matrixPseudoinverse A) *ᵥ b) := by
        show matrixPseudoinverse A *ᵥ b = _
        rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, matrixPseudoinverse_mul_self]
      rw [hx, hPb, Matrix.mulVec_zero]
    · intro h
      have hPb : (A * matrixPseudoinverse A) *ᵥ b = A *ᵥ leastSquaresVector A b :=
        (Matrix.mulVec_mulVec _ _ _).symm
      show ‖stateVector ((A * matrixPseudoinverse A) *ᵥ b)‖ = 0
      rw [hPb, h, Matrix.mulVec_zero]
      have hz : stateVector (0 : QState O) = 0 := rfl
      rw [hz, norm_zero]
  · intro hA
    show ‖stateVector ((A * matrixPseudoinverse A) *ᵥ b)‖ ≤
      ‖stateVector (leastSquaresVector A b)‖
    rw [← Matrix.mulVec_mulVec]
    calc ‖stateVector (A *ᵥ (matrixPseudoinverse A *ᵥ b))‖
        ≤ ‖A‖ * ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ := stateVector_mulVec_norm_le _ _
      _ ≤ 1 * ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ = ‖stateVector (leastSquaresVector A b)‖ := by
        rw [one_mul]
        rfl
  · have hcross : Qatlib.Foundations.PureStateMath.Inner (b - (A * matrixPseudoinverse A) *ᵥ b)
        ((A * matrixPseudoinverse A) *ᵥ b) = 0 := by
      rw [Inner_rev, hproj.2.2]
      simp
    have hpyth := stateVector_norm_sq_add_of_inner_eq_zero
      (u := b - (A * matrixPseudoinverse A) *ᵥ b) (v := (A * matrixPseudoinverse A) *ᵥ b) hcross
    have hsum : b - (A * matrixPseudoinverse A) *ᵥ b + (A * matrixPseudoinverse A) *ᵥ b = b :=
      sub_add_cancel _ _
    rw [hsum] at hpyth
    have hflip : ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ =
        ‖stateVector (b - (A * matrixPseudoinverse A) *ᵥ b)‖ := by
      rw [show A *ᵥ leastSquaresVector A b - b = -(b - (A * matrixPseudoinverse A) *ᵥ b) from by
        rw [hproj.2.1]
        abel]
      rw [show stateVector (-(b - (A * matrixPseudoinverse A) *ᵥ b)) =
        -stateVector (b - (A * matrixPseudoinverse A) *ᵥ b) from rfl, norm_neg]
    show ‖stateVector b‖^2 = ‖stateVector ((A * matrixPseudoinverse A) *ᵥ b)‖^2 +
      ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖^2
    rw [hflip]
    linarith [hpyth]

/-- The least squares direction is absent exactly for a zero solution, and any returned vector
satisfies the solution-state specification with zero error. -/
theorem leastSquares_direction_spec {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) :
    (leastSquaresDirection A b = none ↔ leastSquaresVector A b = 0) ∧
    (∀ φ, leastSquaresDirection A b = some φ → IsLeastSquaresSolutionState A b φ 0) := by
  by_cases hx : leastSquaresVector A b = 0
  · rw [show leastSquaresDirection A b = none from by simp [leastSquaresDirection, hx]]
    exact ⟨⟨fun _ => hx, fun _ => rfl⟩, fun φ hφ => by simp at hφ⟩
  · rw [show leastSquaresDirection A b =
        some (PostMeasure (leastSquaresVector A b) Finset.univ) from by
      simp [leastSquaresDirection, hx]]
    refine ⟨⟨fun h => by simp at h, fun h => absurd h hx⟩, ?_⟩
    intro φ hφ
    have hφ' : PostMeasure (leastSquaresVector A b) Finset.univ = φ := Option.some.inj hφ
    subst φ
    have hpos : 0 < MeasureProb (leastSquaresVector A b) Finset.univ := by
      rw [← stateVector_norm_sq]
      exact pow_pos (norm_pos_iff.mpr fun h0 => hx ((stateVector_eq_zero_iff _).mp h0)) 2
    refine ⟨leastSquaresVector A b, (leastSquares_minimum_residual_and_norm A b).1, hx,
      normalized_postMeasure hpos, ?_⟩
    rw [stateVector_postMeasure_univ, sub_self]
    simp

/-- Under the stated contraction, normalization, and error-gap assumptions, applying an
approximation to a positive scaled pseudoinverse gives a nonzero vector whose normalized
direction has error at most `2 * ε / (c * leastSquaresOverlap A b)`. -/
theorem leastSquares_approximate_application {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (T : Matrix I O ℂ) (b : QState O)
    (c ε : ℝ) (hc : 0 < c) (hε : 0 ≤ ε) (hb : Normalized b) (hA : ‖A‖ ≤ 1)
    (hT : ‖T - (c : ℂ) • matrixPseudoinverse A‖ ≤ ε)
    (hgap : ε < c * leastSquaresOverlap A b) :
    T *ᵥ b ≠ 0 ∧ IsLeastSquaresSolutionState A b (PostMeasure (T *ᵥ b) Finset.univ)
      (2 * ε / (c * leastSquaresOverlap A b)) := by
  have hγnn : 0 ≤ leastSquaresOverlap A b := norm_nonneg _
  have hγpos : 0 < leastSquaresOverlap A b := by
    rcases eq_or_lt_of_le hγnn with h0 | hpos
    · exfalso
      rw [← h0, mul_zero] at hgap
      exact (not_lt_of_ge hε) hgap
    · exact hpos
  have hγle := (leastSquares_overlap_and_zero A b).2.2.1 hA
  have ht : stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b) =
      c • stateVector (matrixPseudoinverse A *ᵥ b) := by
    rw [Matrix.smul_mulVec]
    ext i
    simp [stateVector, Complex.real_smul]
  have htnorm : ‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ =
      c * ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ := by
    rw [ht, norm_smul, Real.norm_of_nonneg hc.le]
  have htarget : c * leastSquaresOverlap A b ≤
      ‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ := by
    rw [htnorm]
    exact mul_le_mul_of_nonneg_left hγle hc.le
  have hcgap : ε < ‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ := hgap.trans_le htarget
  have hclose : ‖stateVector (T *ᵥ b) - stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖
      ≤ ε := by
    have h := stateVector_mulVec_norm_le (T - (c : ℂ) • matrixPseudoinverse A) b
    rw [(normalized_iff_stateVector_norm b).mp hb, mul_one] at h
    have h2 : stateVector ((T - (c : ℂ) • matrixPseudoinverse A) *ᵥ b) =
        stateVector (T *ᵥ b) - stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b) := by
      rw [Matrix.sub_mulVec]
      rfl
    rw [h2] at h
    exact h.trans hT
  obtain ⟨hne, hnorm⟩ := normalize_error_of_gap hclose hcgap
  have hTb : T *ᵥ b ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
  have hpos : 0 < MeasureProb (T *ᵥ b) Finset.univ := by
    rw [← stateVector_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hne) 2
  refine ⟨hTb, leastSquaresVector A b, (leastSquares_minimum_residual_and_norm A b).1, ?_,
    normalized_postMeasure hpos, ?_⟩
  · intro hx0
    have h0 : leastSquaresOverlap A b = 0 := (leastSquares_overlap_and_zero A b).2.1.mpr hx0
    rw [h0, mul_zero] at hgap
    exact (not_lt_of_ge hε) hgap
  · rw [stateVector_postMeasure_univ,
      show NormedSpace.normalize (stateVector (leastSquaresVector A b)) =
        NormedSpace.normalize (stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)) from by
        rw [ht, NormedSpace.normalize_smul_of_pos hc]
        rfl]
    exact hnorm.trans (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hε)
      (mul_pos hc hγpos) htarget)

/-- Under the block-encoding and error-gap assumptions, postselection succeeds with probability
at least `((c * leastSquaresOverlap A b - ε) / α)^2` and returns a solution state with the
stated error bound. -/
theorem leastSquares_actual_postselection {H O I : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] (A : Matrix O I ℂ)
    (U W : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ) (b : QState O)
    (c α ε : ℝ) (hA : ProjectedUnitaryEncoding A U L R)
    (hW : BlockEncoding ((c : ℂ) • matrixPseudoinverse A) W R L α ε)
    (hc : 0 < c) (hb : Normalized b) (hgap : ε < c * leastSquaresOverlap A b) :
    ((c * leastSquaresOverlap A b - ε) / α)^2 ≤ postselectionProbability W R L b ∧
    0 < postselectionProbability W R L b ∧
    ∃ φ, postselectionOutput W R L b = some φ ∧
      IsLeastSquaresSolutionState A b φ (2 * ε / (c * leastSquaresOverlap A b)) := by
  have hAnorm : ‖A‖ ≤ 1 := by
    rw [← hA.encoded]
    exact (compress_norm_le hA.left_isometry hA.right_isometry U).trans
      (unitary_norm_le_one hA.unitary)
  have hγnn : 0 ≤ leastSquaresOverlap A b := norm_nonneg _
  have hγpos : 0 < leastSquaresOverlap A b := by
    rcases eq_or_lt_of_le hγnn with h0 | hpos
    · exfalso
      rw [← h0, mul_zero] at hgap
      exact (not_lt_of_ge hW.error_nonneg) hgap
    · exact hpos
  have hγle := (leastSquares_overlap_and_zero A b).2.2.1 hAnorm
  have ht : stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b) =
      c • stateVector (matrixPseudoinverse A *ᵥ b) := by
    rw [Matrix.smul_mulVec]
    ext i
    simp [stateVector, Complex.real_smul]
  have htnorm : ‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ =
      c * ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ := by
    rw [ht, norm_smul, Real.norm_of_nonneg hc.le]
  have htarget : c * leastSquaresOverlap A b ≤
      ‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ := by
    rw [htnorm]
    exact mul_le_mul_of_nonneg_left hγle hc.le
  have hgap' : ε < ‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ := hgap.trans_le htarget
  have hlower :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower hW hb hgap'.le
  obtain ⟨hp, φ, hφ, happ⟩ :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_output_of_gap hW hb hgap'
  refine ⟨?_, hp, φ, hφ, leastSquaresVector A b,
    (leastSquares_minimum_residual_and_norm A b).1, ?_, happ.2.1, ?_⟩
  · have hle : (c * leastSquaresOverlap A b - ε) / α ≤
        (‖stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)‖ - ε) / α :=
      div_le_div_of_nonneg_right (sub_le_sub_right htarget ε) hW.normalization_pos.le
    exact (pow_le_pow_left₀
      (div_nonneg (sub_nonneg.mpr hgap.le) hW.normalization_pos.le) hle 2).trans hlower
  · intro hx0
    have h0 : leastSquaresOverlap A b = 0 := (leastSquares_overlap_and_zero A b).2.1.mpr hx0
    rw [h0, mul_zero] at hgap
    exact (not_lt_of_ge hW.error_nonneg) hgap
  · rw [show NormedSpace.normalize (stateVector (leastSquaresVector A b)) =
        NormedSpace.normalize (stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b)) from by
      rw [ht, NormedSpace.normalize_smul_of_pos hc]
      rfl]
    exact happ.2.2.trans (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hW.error_nonneg)
      (mul_pos hc hγpos) htarget)

/-- An odd QSVT phase list approximating the scaled reciprocal on positive singular values
yields a circuit with `zs.length` queries and `zs.length + 1` gates, together with the
stated postselection probability and solution-state error bounds. -/
theorem leastSquares_counted_qsvt_output {H O I : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] (A : Matrix O I ℂ)
    (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ) (b : QState O) (base : ℂ)
    (zs : List ℂ) (c ε : ℝ) (hA : ProjectedUnitaryEncoding A U L R) (hbase : IsPhase base)
    (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1) (hc : 0 < c) (hε : 0 ≤ ε)
    (hb : Normalized b)
    (happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) -
        (c : ℂ) / (matrixSingularValues A i : ℂ)‖ ≤ ε)
    (hgap : ε < c * leastSquaresOverlap A b) :
    ∃ cs : List (AdjointStep H), adjointQueryCount cs = zs.length ∧
      adjointGateCount cs = zs.length + 1 ∧
      (c * leastSquaresOverlap A b - ε)^2 ≤ postselectionProbability (evaluate U cs) R L b ∧
      ∃ φ, postselectionOutput (evaluate U cs) R L b = some φ ∧
        IsLeastSquaresSolutionState A b φ (2 * ε / (c * leastSquaresOverlap A b)) := by
  obtain ⟨cs, hcs, hqueries, hgates⟩ :=
    qsvt_pseudoinverse_counted_approximation hA hbase zs hzs hodd c hε happrox
  obtain ⟨hprob, -, hout⟩ := leastSquares_actual_postselection A U (evaluate U cs) L R b c 1 ε
    hA hcs hc hb hgap
  exact ⟨cs, hqueries, hgates, by simpa only [div_one] using hprob, hout⟩

section Ridge

variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

omit [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] in

/-- The conjugate transpose of a vertically stacked matrix is the horizontal concatenation of
the conjugate transposes. -/
theorem conjTranspose_fromRows (A₁ : Matrix O I ℂ) (A₂ : Matrix I I ℂ) :
    (Matrix.fromRows A₁ A₂)ᴴ = Matrix.fromCols A₁ᴴ A₂ᴴ := by
  ext i j
  cases j <;> simp [Matrix.conjTranspose_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]

omit [Fintype I] in

/-- The identity scaled by the real square root of `lam` is self-adjoint. -/
theorem sqrt_smul_one_conjTranspose (lam : ℝ) :
    ((Real.sqrt lam : ℂ) • (1 : Matrix I I ℂ))ᴴ = (Real.sqrt lam : ℂ) • 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

/-- For nonnegative `lam`, the Gram matrix of the ridge augmentation is `Aᴴ * A + lam • 1`. -/
theorem ridgeAugmented_gram (A : Matrix O I ℂ) (lam : ℝ) (hlam : 0 ≤ lam) :
    (ridgeAugmentedMatrix A lam)ᴴ * ridgeAugmentedMatrix A lam = Aᴴ * A + (lam : ℂ) • 1 := by
  rw [ridgeAugmentedMatrix, conjTranspose_fromRows, sqrt_smul_one_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  congr 1
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hlam]

/-- Applying the adjoint of the augmented matrix to the zero-extended input gives `Aᴴ *ᵥ b`. -/
theorem ridgeAugmented_adjoint_input (A : Matrix O I ℂ) (b : QState O) (lam : ℝ) :
    (ridgeAugmentedMatrix A lam)ᴴ *ᵥ ridgeAugmentedInput b = Aᴴ *ᵥ b := by
  rw [ridgeAugmentedMatrix, conjTranspose_fromRows, sqrt_smul_one_conjTranspose,
    Matrix.fromCols_mulVec]
  have hinl : (ridgeAugmentedInput (I := I) b ∘ Sum.inl : QState O) = b := rfl
  have hinr : (ridgeAugmentedInput (I := I) b ∘ Sum.inr : QState I) = 0 := rfl
  rw [hinl, hinr, Matrix.mulVec_zero, add_zero]

/-- For nonnegative `lam`, the augmented squared residual equals the original squared residual
plus `lam` times the squared solution norm. -/
theorem ridge_augmented_residual {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (lam : ℝ) (x : QState I)
    (hlam : 0 ≤ lam) :
    ‖stateVector (ridgeAugmentedMatrix A lam *ᵥ x - ridgeAugmentedInput b)‖^2 =
      ‖stateVector (A *ᵥ x - b)‖^2 + lam * ‖stateVector x‖^2 := by
  have hsqrt : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg lam
  have hinl : ∀ o : O, (ridgeAugmentedMatrix A lam *ᵥ x - ridgeAugmentedInput (I := I) b)
        (Sum.inl o) = (A *ᵥ x) o - b o := by
    intro o
    show ((Matrix.fromRows A ((Real.sqrt lam : ℂ) • (1 : Matrix I I ℂ))) *ᵥ x -
        ridgeAugmentedInput (I := I) b) (Sum.inl o) = _
    rw [Matrix.fromRows_mulVec]
    rfl
  have hinr : ∀ i : I, (ridgeAugmentedMatrix A lam *ᵥ x - ridgeAugmentedInput (I := I) b)
        (Sum.inr i) = (Real.sqrt lam : ℂ) * x i := by
    intro i
    show ((Matrix.fromRows A ((Real.sqrt lam : ℂ) • (1 : Matrix I I ℂ))) *ᵥ x -
        ridgeAugmentedInput (I := I) b) (Sum.inr i) = _
    rw [Matrix.fromRows_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [ridgeAugmentedInput]
  have hinl' : ∀ o : O, ‖(ridgeAugmentedMatrix A lam *ᵥ x - ridgeAugmentedInput (I := I) b)
      (Sum.inl o)‖^2 = ‖(A *ᵥ x - b) o‖^2 :=
    fun o => congrArg (fun t => ‖t‖^2) (hinl o)
  have hinr' : ∀ i : I, ‖(ridgeAugmentedMatrix A lam *ᵥ x - ridgeAugmentedInput (I := I) b)
      (Sum.inr i)‖^2 = lam * ‖x i‖^2 := by
    intro i
    rw [hinr i, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsqrt, mul_pow,
      Real.sq_sqrt hlam]
  simp only [stateVector_norm_sq_sum]
  rw [Fintype.sum_sum_type]
  simp_rw [hinl', hinr']
  rw [Finset.mul_sum]

end Ridge

/-- For positive `lam`, the augmented pseudoinverse solution satisfies the regularized normal
equations and uniquely minimizes the ridge objective. -/
theorem ridge_regularized_unique_minimizer {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (lam : ℝ) (hlam : 0 < lam) :
    let x := leastSquaresVector (ridgeAugmentedMatrix A lam) (ridgeAugmentedInput b)
    (Aᴴ * A + (lam : ℂ) • 1) *ᵥ x = Aᴴ *ᵥ b ∧
    (∀ y : QState I, ‖stateVector (A *ᵥ x - b)‖^2 + lam * ‖stateVector x‖^2 ≤
      ‖stateVector (A *ᵥ y - b)‖^2 + lam * ‖stateVector y‖^2) ∧
    (∀ y : QState I, ‖stateVector (A *ᵥ y - b)‖^2 + lam * ‖stateVector y‖^2 =
      ‖stateVector (A *ᵥ x - b)‖^2 + lam * ‖stateVector x‖^2 → y = x) := by
  have hridge : (Aᴴ * A + (lam : ℂ) • 1) *ᵥ
      leastSquaresVector (ridgeAugmentedMatrix A lam) (ridgeAugmentedInput b) = Aᴴ *ᵥ b := by
    have h0 := (leastSquares_projection_and_normal (ridgeAugmentedMatrix A lam)
      (ridgeAugmentedInput b)).1
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ridgeAugmented_gram A lam hlam.le,
      ridgeAugmented_adjoint_input, sub_eq_zero] at h0
    exact h0
  have hobj : ∀ y : QState I, ‖stateVector (A *ᵥ
        leastSquaresVector (ridgeAugmentedMatrix A lam) (ridgeAugmentedInput b) - b)‖^2 +
      lam * ‖stateVector (leastSquaresVector (ridgeAugmentedMatrix A lam)
        (ridgeAugmentedInput b))‖^2 ≤
      ‖stateVector (A *ᵥ y - b)‖^2 + lam * ‖stateVector y‖^2 := by
    intro y
    have hmin := (leastSquares_minimum_residual_and_norm (ridgeAugmentedMatrix A lam)
      (ridgeAugmentedInput b)).1.1 y
    have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmin
    rwa [ridge_augmented_residual A b lam _ hlam.le,
      ridge_augmented_residual A b lam y hlam.le] at hsq
  have huniq : ∀ y : QState I, ‖stateVector (A *ᵥ y - b)‖^2 + lam * ‖stateVector y‖^2 =
      ‖stateVector (A *ᵥ leastSquaresVector (ridgeAugmentedMatrix A lam)
          (ridgeAugmentedInput b) - b)‖^2 +
        lam * ‖stateVector (leastSquaresVector (ridgeAugmentedMatrix A lam)
          (ridgeAugmentedInput b))‖^2 →
      y = leastSquaresVector (ridgeAugmentedMatrix A lam) (ridgeAugmentedInput b) := by
    intro y hy
    have hpyth := leastSquares_residual_pythagoras (ridgeAugmentedMatrix A lam)
      (ridgeAugmentedInput b) y
    rw [ridge_augmented_residual A b lam y hlam.le,
      ridge_augmented_residual A b lam (leastSquaresVector (ridgeAugmentedMatrix A lam)
        (ridgeAugmentedInput b)) hlam.le] at hpyth
    have hz : ‖stateVector (ridgeAugmentedMatrix A lam *ᵥ
        (y - leastSquaresVector (ridgeAugmentedMatrix A lam) (ridgeAugmentedInput b)))‖^2 = 0 := by
      linarith [hpyth, hy]
    have hM0 : ridgeAugmentedMatrix A lam *ᵥ
        (y - leastSquaresVector (ridgeAugmentedMatrix A lam) (ridgeAugmentedInput b)) = 0 :=
      (stateVector_eq_zero_iff _).mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
    funext i
    have hi := congrFun hM0 (Sum.inr i)
    rw [Pi.zero_apply] at hi
    have hentry : (ridgeAugmentedMatrix A lam *ᵥ
        (y - leastSquaresVector (ridgeAugmentedMatrix A lam) (ridgeAugmentedInput b)))
        (Sum.inr i) = (Real.sqrt lam : ℂ) *
          (y i - leastSquaresVector (ridgeAugmentedMatrix A lam) (ridgeAugmentedInput b) i) := by
      show ((Matrix.fromRows A ((Real.sqrt lam : ℂ) • (1 : Matrix I I ℂ))) *ᵥ _) (Sum.inr i) = _
      rw [Matrix.fromRows_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rfl
    rw [hentry] at hi
    have hsqrtne : (Real.sqrt lam : ℂ) ≠ 0 := by
      have h := Real.sqrt_pos_of_pos hlam
      exact_mod_cast h.ne'
    have hyi : y i -
        leastSquaresVector (ridgeAugmentedMatrix A lam) (ridgeAugmentedInput b) i = 0 :=
      (mul_eq_zero.mp hi).resolve_left hsqrtne
    exact sub_eq_zero.mp hyi
  exact ⟨hridge, hobj, huniq⟩

/-- Rescaling the postselection vector by `α / c` approximates the least squares vector within
`ε / c`, and its residual lies between the optimum and the optimum plus `‖A‖ * ε / c`. -/
theorem leastSquares_actual_rescaled_residual {H O I : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] (A : Matrix O I ℂ)
    (W : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ) (b : QState O) (c α ε : ℝ)
    (hW : BlockEncoding ((c : ℂ) • matrixPseudoinverse A) W R L α ε)
    (hc : 0 < c) (hb : Normalized b) :
    let y := (α/c : ℝ) • postselectionVector W R L b
    ‖stateVector (y - leastSquaresVector A b)‖ ≤ ε/c ∧
    ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ ≤ ‖stateVector (A *ᵥ y - b)‖ ∧
    ‖stateVector (A *ᵥ y - b)‖ ≤
      ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ + ‖A‖*ε/c := by
  have hps :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_error hW hb
  have ht : stateVector (((c : ℂ) • matrixPseudoinverse A) *ᵥ b) =
      c • stateVector (matrixPseudoinverse A *ᵥ b) := by
    rw [Matrix.smul_mulVec]
    ext i
    simp [stateVector, Complex.real_smul]
  rw [ht] at hps
  have hcy : (c : ℝ) • stateVector (matrixPseudoinverse A *ᵥ b) -
        α • stateVector (postselectionVector W R L b) =
      (c : ℝ) • (stateVector (matrixPseudoinverse A *ᵥ b) -
        (α/c : ℝ) • stateVector (postselectionVector W R L b)) := by
    rw [smul_sub, smul_smul, ← mul_div_assoc, mul_div_cancel_left₀ α hc.ne']
  rw [hcy, norm_smul, Real.norm_of_nonneg hc.le] at hps
  have hclose : ‖stateVector (matrixPseudoinverse A *ᵥ b) -
      (α/c : ℝ) • stateVector (postselectionVector W R L b)‖ ≤ ε / c :=
    (le_div_iff₀ hc).mpr (by linarith [hps])
  refine ⟨?_, ?_, ?_⟩
  · rw [stateVector_sub, stateVector_real_smul, norm_sub_rev]
    exact hclose
  · exact (leastSquares_minimum_residual_and_norm A b).1.1 _
  · have hclose' : ‖stateVector (((α/c : ℝ) • postselectionVector W R L b) -
        leastSquaresVector A b)‖ ≤ ε / c := by
      rw [stateVector_sub, stateVector_real_smul, norm_sub_rev]
      exact hclose
    have hdecomp : A *ᵥ ((α/c : ℝ) • postselectionVector W R L b) - b =
        (A *ᵥ leastSquaresVector A b - b) +
          A *ᵥ (((α/c : ℝ) • postselectionVector W R L b) - leastSquaresVector A b) := by
      rw [Matrix.mulVec_sub]
      abel
    have hs1 : ‖stateVector (A *ᵥ ((α/c : ℝ) • postselectionVector W R L b) - b)‖ =
        ‖stateVector ((A *ᵥ leastSquaresVector A b - b) +
          A *ᵥ (((α/c : ℝ) • postselectionVector W R L b) - leastSquaresVector A b))‖ := by
      rw [hdecomp]
    have hs2 : ‖stateVector ((A *ᵥ leastSquaresVector A b - b) +
          A *ᵥ (((α/c : ℝ) • postselectionVector W R L b) - leastSquaresVector A b))‖ ≤
        ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ +
          ‖stateVector (A *ᵥ (((α/c : ℝ) • postselectionVector W R L b) -
            leastSquaresVector A b))‖ := by
      rw [stateVector_add]
      exact norm_add_le _ _
    have hs3 : ‖stateVector (A *ᵥ (((α/c : ℝ) • postselectionVector W R L b) -
          leastSquaresVector A b))‖ ≤
        ‖A‖ * ‖stateVector (((α/c : ℝ) • postselectionVector W R L b) -
          leastSquaresVector A b)‖ :=
      stateVector_mulVec_norm_le A _
    have hs4 : ‖A‖ * ‖stateVector (((α/c : ℝ) • postselectionVector W R L b) -
          leastSquaresVector A b)‖ ≤ ‖A‖ * ε / c := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hclose' (norm_nonneg A)
    rw [hs1]
    exact (hs2.trans (add_le_add_right hs3 _)).trans (add_le_add_right hs4 _)

end Qatlib.Concepts.LocalMachine.LocalTransport
