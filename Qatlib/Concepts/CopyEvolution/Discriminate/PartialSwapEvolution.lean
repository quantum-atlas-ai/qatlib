/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError

/-!
# Partial-swap density evolution

This module defines the register swap, its partial-swap unitary `partialSwapMatrix`, and the
reduced output `partialSwapOutput`. The exact output formula separates the input, reset, and
commutator terms in the density-matrix exponentiation identity of [LloydMohseniRebentrost2014].

`partialSwapChannel` packages the construction as a quantum channel for a density copy.
`partialSwapReferenceOutput` extends the construction to an untouched reference register, with
explicit positivity and trace preservation, and the final estimates bound its unreferenced
first-order commutator approximation in operator norm.

## Main statements

* `partial_swap_unitary_laws`: the swap and partial-swap algebraic identities.
* `partial_swap_actual_output_formula`: the exact reduced output.
* `partial_swap_actual_reference_bridge`: agreement with channel reference extension.
* `partial_swap_trig_and_quadratic_error`: the quadratic first-order error estimate.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Foundations.PureStateMath.BornBridge
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ReferenceError.RefTraceError

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.Discriminate

open Matrix
open scoped ComplexOrder Kronecker Matrix.Norms.L2Operator

/-- The permutation matrix swapping two `D`-dimensional registers. -/
def swapRegisterMatrix (D : ℕ) : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  permMatrix Prod.swap

/-- A register-swap matrix entry is one precisely when the row index is the swap of the column
index. -/
theorem swapRegisterMatrix_apply (D : ℕ) (x y : Fin D × Fin D) :
    swapRegisterMatrix D x y = if x = Prod.swap y then (1 : ℂ) else 0 := rfl

/-- The register-swap matrix squares to the identity. -/
theorem swapRegisterMatrix_mul_self (D : ℕ) :
    swapRegisterMatrix D * swapRegisterMatrix D = 1 :=
  permMatrix_mul_self (fun _ => Prod.swap_swap _)

/-- The register-swap matrix is equal to its conjugate transpose. -/
theorem swapRegisterMatrix_conjTranspose (D : ℕ) :
    (swapRegisterMatrix D)ᴴ = swapRegisterMatrix D :=
  permMatrix_conjTranspose (fun _ => Prod.swap_swap _)

/-- The partial-swap matrix `cos θ • 1 - (i sin θ) • swapRegisterMatrix D`. -/
noncomputable def partialSwapMatrix (D : ℕ) (θ : ℝ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  (Real.cos θ : ℂ) • 1 - (Complex.I * (Real.sin θ : ℂ)) • swapRegisterMatrix D

/-- The entries of the partial-swap matrix are the cosine-scaled identity entries minus the
imaginary sine-scaled swap entries. -/
theorem partialSwapMatrix_apply (D : ℕ) (θ : ℝ) (x y : Fin D × Fin D) :
    partialSwapMatrix D θ x y =
      (Real.cos θ : ℂ) * (if x = y then (1 : ℂ) else 0) -
        Complex.I * (Real.sin θ : ℂ) * (if x = Prod.swap y then (1 : ℂ) else 0) := by
  simp only [partialSwapMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, swapRegisterMatrix_apply]

/-- Multiplying two linear combinations of the identity and an involutive matrix gives the
stated identity and involution coefficients. -/
private theorem swap_combo_mul {I : Type*} [Fintype I] [DecidableEq I]
    (a b a' b' : ℂ) (S : Matrix I I ℂ) (hS : S * S = 1) :
    ((a • 1) - b • S) * ((a' • 1) - b' • S)
      = (a * a' + b * b') • 1 - (a * b' + b * a') • S := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [hS]
  module

/-- The sum of the cosine square and sine square, cast to the complex numbers, is one. -/
private theorem complex_cos_sq_add_sin_sq (θ : ℝ) :
    ((Real.cos θ : ℂ)) * ((Real.cos θ : ℂ)) + ((Real.sin θ : ℂ)) * ((Real.sin θ : ℂ)) = 1 := by
  rw [← pow_two, ← pow_two]
  exact_mod_cast Real.cos_sq_add_sin_sq θ

/-- The partial swap at angle `-θ` is a right inverse of the partial swap at angle `θ`. -/
theorem partialSwapMatrix_mul_neg (D : ℕ) (θ : ℝ) :
    partialSwapMatrix D θ * partialSwapMatrix D (-θ) = 1 := by
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h := swap_combo_mul (Real.cos θ : ℂ) (Complex.I * (Real.sin θ : ℂ))
      (Real.cos (-θ) : ℂ) (Complex.I * (Real.sin (-θ) : ℂ)) (swapRegisterMatrix D)
      (swapRegisterMatrix_mul_self D)
  show ((Real.cos θ : ℂ) • 1 - (Complex.I * (Real.sin θ : ℂ)) • swapRegisterMatrix D) *
      ((Real.cos (-θ) : ℂ) • 1 - (Complex.I * (Real.sin (-θ) : ℂ)) • swapRegisterMatrix D) = 1
  rw [h]
  have hc : ((Real.cos θ : ℂ)) * ((Real.cos (-θ) : ℂ)) +
      (Complex.I * (Real.sin θ : ℂ)) * (Complex.I * (Real.sin (-θ) : ℂ)) = 1 := by
    rw [Real.cos_neg, Real.sin_neg]
    simp only [Complex.ofReal_neg]
    linear_combination complex_cos_sq_add_sin_sq θ -
      ((Real.sin θ : ℂ)) * ((Real.sin θ : ℂ)) * hI2
  have hb : ((Real.cos θ : ℂ)) * (Complex.I * ((Real.sin (-θ) : ℂ))) +
      (Complex.I * ((Real.sin θ : ℂ))) * ((Real.cos (-θ) : ℂ)) = 0 := by
    rw [Real.cos_neg, Real.sin_neg]
    simp only [Complex.ofReal_neg]
    ring
  rw [hc, hb, one_smul, zero_smul, sub_zero]

/-- The partial swap at angle `-θ` is a left inverse of the partial swap at angle `θ`. -/
theorem partialSwapMatrix_neg_mul (D : ℕ) (θ : ℝ) :
    partialSwapMatrix D (-θ) * partialSwapMatrix D θ = 1 := by
  have h := partialSwapMatrix_mul_neg D (-θ)
  rw [neg_neg] at h
  exact h

/-- The conjugate transpose of a partial swap is the partial swap with negated angle. -/
theorem partialSwapMatrix_conjTranspose (D : ℕ) (θ : ℝ) :
    (partialSwapMatrix D θ)ᴴ = partialSwapMatrix D (-θ) := by
  have hc : (star (Real.cos θ : ℂ)) = (Real.cos θ : ℂ) := by
    rw [RCLike.star_def, Complex.conj_ofReal]
  have hb : (star (Complex.I * (Real.sin θ : ℂ)))
      = -(Complex.I * (Real.sin θ : ℂ)) := by
    rw [RCLike.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hR : partialSwapMatrix D (-θ)
      = (Real.cos θ : ℂ) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
        + (Complex.I * (Real.sin θ : ℂ)) • swapRegisterMatrix D := by
    simp only [partialSwapMatrix, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    module
  rw [hR, partialSwapMatrix]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    swapRegisterMatrix_conjTranspose, hc, hb]
  module

/-- The partial-swap matrix is unitary for every real angle. -/
theorem partialSwapMatrix_unitary (D : ℕ) (θ : ℝ) :
    partialSwapMatrix D θ ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    partialSwapMatrix_conjTranspose, partialSwapMatrix_neg_mul]

/-- Multiplying partial swaps adds their angles. -/
theorem partialSwapMatrix_mul (D : ℕ) (θ t : ℝ) :
    partialSwapMatrix D θ * partialSwapMatrix D t = partialSwapMatrix D (θ + t) := by
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h := swap_combo_mul (Real.cos θ : ℂ) (Complex.I * (Real.sin θ : ℂ))
      (Real.cos t : ℂ) (Complex.I * (Real.sin t : ℂ)) (swapRegisterMatrix D)
      (swapRegisterMatrix_mul_self D)
  have hcos : ((Real.cos (θ + t) : ℝ) : ℂ) = ((Real.cos θ : ℂ)) * ((Real.cos t : ℂ)) -
      ((Real.sin θ : ℂ)) * ((Real.sin t : ℂ)) := by
    exact_mod_cast Real.cos_add θ t
  have hsin : ((Real.sin (θ + t) : ℝ) : ℂ) = ((Real.sin θ : ℂ)) * ((Real.cos t : ℂ)) +
      ((Real.cos θ : ℂ)) * ((Real.sin t : ℂ)) := by
    exact_mod_cast Real.sin_add θ t
  have hc : ((Real.cos θ : ℂ)) * ((Real.cos t : ℂ)) +
      (Complex.I * (Real.sin θ : ℂ)) * (Complex.I * (Real.sin t : ℂ)) =
      ((Real.cos (θ + t) : ℝ) : ℂ) := by
    linear_combination ((Real.sin θ : ℂ)) * ((Real.sin t : ℂ)) * hI2 - hcos
  have hb : ((Real.cos θ : ℂ)) * (Complex.I * ((Real.sin t : ℂ))) +
      (Complex.I * ((Real.sin θ : ℂ))) * ((Real.cos t : ℂ)) =
      Complex.I * ((Real.sin (θ + t) : ℝ) : ℂ) := by
    linear_combination -Complex.I * hsin
  show ((Real.cos θ : ℂ) • 1 - (Complex.I * (Real.sin θ : ℂ)) • swapRegisterMatrix D) *
      ((Real.cos t : ℂ) • 1 - (Complex.I * (Real.sin t : ℂ)) • swapRegisterMatrix D) = _
  rw [h, hc, hb]
  simp only [partialSwapMatrix]

/-- The swap is a Hermitian involution, and partial swaps are unitary with adjoint given by
angle negation and composition given by angle addition. -/
theorem partial_swap_unitary_laws (D : ℕ) (θ : ℝ) :
    swapRegisterMatrix D * swapRegisterMatrix D = 1 ∧ (swapRegisterMatrix D)ᴴ = swapRegisterMatrix D ∧
    partialSwapMatrix D θ ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ ∧
    (partialSwapMatrix D θ)ᴴ = partialSwapMatrix D (-θ) ∧
    (∀ t, partialSwapMatrix D θ * partialSwapMatrix D t = partialSwapMatrix D (θ+t)) :=
  ⟨swapRegisterMatrix_mul_self D, swapRegisterMatrix_conjTranspose D,
    partialSwapMatrix_unitary D θ, partialSwapMatrix_conjTranspose D θ,
    fun t => partialSwapMatrix_mul D θ t⟩

/-- Right multiplication of a tensor product by the swap exchanges the column-register indices
in its entry formula. -/
private theorem tensor_swap_apply {D : ℕ} (σ ρ : Operator D) (x y : Fin D × Fin D) :
    (TensorGate σ ρ * swapRegisterMatrix D) x y = σ x.1 y.2 * ρ x.2 y.1 := by
  classical
  simp only [Matrix.mul_apply, swapRegisterMatrix_apply]
  rw [Fintype.sum_eq_single (Prod.swap y)
    (fun p hp => by rw [if_neg hp, mul_zero])]
  simp only [ite_true, mul_one]
  rfl

/-- Left multiplication of a tensor product by the swap exchanges the row-register indices in
its entry formula. -/
private theorem swap_tensor_apply {D : ℕ} (σ ρ : Operator D) (x y : Fin D × Fin D) :
    (swapRegisterMatrix D * TensorGate σ ρ) x y = σ x.2 y.1 * ρ x.1 y.2 := by
  classical
  simp only [Matrix.mul_apply, swapRegisterMatrix_apply]
  rw [Fintype.sum_eq_single (Prod.swap x)
    (fun p hp => by
      rw [if_neg (fun e => hp (by rw [e, Prod.swap_swap])), zero_mul])]
  rw [Prod.swap_swap, if_pos rfl, one_mul]
  rfl

/-- Conjugating a tensor product by the swap exchanges its two factors, entrywise. -/
private theorem swap_tensor_swap_apply {D : ℕ} (σ ρ : Operator D) (x y : Fin D × Fin D) :
    (swapRegisterMatrix D * TensorGate σ ρ * swapRegisterMatrix D) x y
      = σ x.2 y.2 * ρ x.1 y.1 := by
  classical
  show (∑ p : Fin D × Fin D,
        (swapRegisterMatrix D * TensorGate σ ρ) x p * swapRegisterMatrix D p y)
      = σ x.2 y.2 * ρ x.1 y.1
  have hstep : ∀ p : Fin D × Fin D,
      (swapRegisterMatrix D * TensorGate σ ρ) x p * swapRegisterMatrix D p y
        = σ x.2 p.1 * ρ x.1 p.2 * swapRegisterMatrix D p y :=
    fun p => by rw [swap_tensor_apply σ ρ x p]
  rw [Fintype.sum_eq_single (Prod.swap y)
    (fun p hp => by rw [hstep p, swapRegisterMatrix_apply, if_neg hp, mul_zero])]
  rw [hstep]
  simp only [swapRegisterMatrix_apply, ite_true, mul_one]
  rfl

/-- The partial traces of the two swap cross terms are `σ * ρ` and `ρ * σ`; the swapped tensor
product has partial trace `Matrix.trace σ • ρ`. -/
theorem partial_swap_cross_partial_traces {D : ℕ} (σ ρ : Operator D) :
    PartialTrace (TensorGate σ ρ * swapRegisterMatrix D) = σ * ρ ∧
    PartialTrace (swapRegisterMatrix D * TensorGate σ ρ) = ρ * σ ∧
    PartialTrace (swapRegisterMatrix D * TensorGate σ ρ * swapRegisterMatrix D) = Matrix.trace σ • ρ := by
  constructor
  · ext i j
    simp only [PartialTrace, tensor_swap_apply, ← Matrix.mul_apply]
  constructor
  · ext i j
    simp only [PartialTrace, swap_tensor_apply]
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  · ext i j
    simp only [PartialTrace, swap_tensor_swap_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.trace, Matrix.diag_apply, Finset.sum_mul]

/-- Partial trace preserves matrix subtraction. -/
theorem partialTrace_sub {D E : ℕ}
    (ρ σ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (ρ - σ) = PartialTrace ρ - PartialTrace σ := by
  ext i j
  simp only [PartialTrace, Matrix.sub_apply, Finset.sum_sub_distrib]

/-- The system output after adjoining `ρ`, conjugating by a partial swap of angle `θ`, and
tracing out the copy register. -/
noncomputable def partialSwapOutput {D : ℕ} (ρ : Operator D) (θ : ℝ) (σ : Operator D) :
    Operator D :=
  PartialTrace (partialSwapMatrix D θ * TensorGate σ ρ * (partialSwapMatrix D θ)ᴴ)

/-- Expanding the product of two identity-involution combinations around `X` gives the stated
four matrix terms. -/
private theorem sandwich_expand {I : Type*} [Fintype I] [DecidableEq I] (a b : ℂ)
    (S X : Matrix I I ℂ) :
    ((a • 1) - b • S) * X * ((a • 1) + b • S)
      = (a * a) • X + (a * b) • (X * S) - (b * a) • (S * X) - (b * b) • (S * X * S) := by
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

/-- The partial-swap output is the cosine-square input term plus the sine-square reset term
minus the imaginary sine-cosine commutator term, with the respective trace factors. This is
the density-matrix exponentiation identity of [LloydMohseniRebentrost2014]. -/
theorem partial_swap_actual_output_formula {D : ℕ} (ρ σ : Operator D) (θ : ℝ) :
    partialSwapOutput ρ θ σ =
      ((Real.cos θ)^2 : ℂ) • (Matrix.trace ρ • σ) +
      ((Real.sin θ)^2 : ℂ) • (Matrix.trace σ • ρ) -
      (Complex.I * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) • (ρ * σ - σ * ρ) := by
  have hcast : ((Real.cos θ)^2 : ℂ) = ((Real.cos θ : ℂ))^2 := by push_cast; ring
  have hcast' : ((Real.sin θ)^2 : ℂ) = ((Real.sin θ : ℂ))^2 := by push_cast; ring
  rw [partialSwapOutput, partialSwapMatrix_conjTranspose]
  have hneg : partialSwapMatrix D (-θ) =
      (Real.cos θ : ℂ) • 1 + (Complex.I * (Real.sin θ : ℂ)) • swapRegisterMatrix D := by
    simp only [partialSwapMatrix, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    module
  rw [hneg]
  simp only [partialSwapMatrix, sandwich_expand, partialTrace_add, partialTrace_sub,
    partialTrace_smul, partialTrace_tensorGate,
    (partial_swap_cross_partial_traces σ ρ).1, (partial_swap_cross_partial_traces σ ρ).2.1,
    (partial_swap_cross_partial_traces σ ρ).2.2]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hb2 : (Complex.I * (Real.sin θ : ℂ)) * (Complex.I * (Real.sin θ : ℂ))
      = -(((Real.sin θ : ℂ)) * ((Real.sin θ : ℂ))) := by
    calc Complex.I * (Real.sin θ : ℂ) * (Complex.I * (Real.sin θ : ℂ))
        = (Complex.I * Complex.I) * (((Real.sin θ : ℂ)) * ((Real.sin θ : ℂ))) := by ring
      _ = -(((Real.sin θ : ℂ)) * ((Real.sin θ : ℂ))) := by rw [hI2, neg_one_mul]
  rw [hcast, hcast', hb2]
  module

/-- The matrix map adjoining `ρ` as the right copy register. -/
noncomputable def tensorWithCopy {D : ℕ} (ρ : Operator D) :
    MatrixMap (Fin D) (Fin D × Fin D) ℂ where
  toFun M := TensorGate M ρ
  map_add' := by
    intro M N
    ext
    simp [TensorGate, add_mul]
  map_smul' := by
    intro c M
    ext
    simp [TensorGate, mul_assoc]

/-- The map `tensorWithCopy ρ` sends `M` to `TensorGate M ρ`. -/
theorem tensorWithCopy_apply {D : ℕ} (ρ : Operator D) (M : Operator D) :
    tensorWithCopy ρ M = TensorGate M ρ := rfl

/-- Adjoining a positive semidefinite copy operator is completely positive. -/
theorem completelyPositive_tensorWithCopy {D : ℕ} {ρ : Operator D} (hρ : ρ.PosSemidef) :
    MatrixMap.IsCompletelyPositive (tensorWithCopy ρ) :=
  MatrixMap.kron_kronecker_const (A := Fin D) (d := Fin D) hρ

/-- Adjoining a trace-one copy operator preserves trace. -/
theorem tracePreserving_tensorWithCopy {D : ℕ} {ρ : Operator D}
    (hρ : Matrix.trace ρ = 1) : MatrixMap.IsTracePreserving (tensorWithCopy ρ) := by
  intro M
  rw [tensorWithCopy_apply]
  show Matrix.trace (M ⊗ₖ ρ) = Matrix.trace M
  rw [Matrix.trace_kronecker, hρ, mul_one]

/-- Partial trace over the right copy register, packaged as a matrix map. -/
noncomputable def traceRightLM (D : ℕ) : MatrixMap (Fin D × Fin D) (Fin D) ℂ :=
  (CPTPMap.traceRight (d₁ := Fin D) (d₂ := Fin D)).toLinearMap

/-- The right partial-trace matrix map is completely positive. -/
theorem completelyPositive_traceRightLM (D : ℕ) :
    MatrixMap.IsCompletelyPositive (traceRightLM D) :=
  (CPTPMap.traceRight (d₁ := Fin D) (d₂ := Fin D)).cp

/-- The right partial-trace matrix map preserves trace. -/
theorem tracePreserving_traceRightLM (D : ℕ) :
    MatrixMap.IsTracePreserving (traceRightLM D) :=
  (CPTPMap.traceRight (d₁ := Fin D) (d₂ := Fin D)).TP

/-- Applying `traceRightLM` agrees with `Matrix.traceRight`. -/
theorem traceRightLM_apply (D : ℕ) (M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    traceRightLM D M = Matrix.traceRight M := by
  ext i j
  simp only [traceRightLM, CPTPMap.traceRight, CPTPMap.compose, CPTPMap.traceLeft,
    CPTPMap.SWAP, CPTPMap.ofEquiv, MatrixMap.submatrix, LinearMap.comp_apply,
    Matrix.traceLeft]
  rfl

/-- The finite-register operation `PartialTrace` equals `Matrix.traceRight`. -/
theorem partialTrace_eq_traceRight {D E : ℕ}
    (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace A = Matrix.traceRight A := rfl

/-- The matrix map conjugating by a partial-swap matrix. -/
noncomputable def conjStep {D : ℕ} (θ : ℝ) :
    MatrixMap (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  MatrixMap.conj (partialSwapMatrix D θ)

/-- The map `conjStep θ` sends `M` to its conjugation by `partialSwapMatrix D θ`. -/
theorem conjStep_apply {D : ℕ} (θ : ℝ) (M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    conjStep θ M = partialSwapMatrix D θ * M * (partialSwapMatrix D θ)ᴴ := rfl

/-- Conjugation by the partial-swap matrix is completely positive. -/
theorem completelyPositive_conjStep (D : ℕ) (θ : ℝ) :
    MatrixMap.IsCompletelyPositive (conjStep (D := D) θ) :=
  MatrixMap.congruence_CP (A := Fin D × Fin D) (B := Fin D × Fin D)
    (partialSwapMatrix D θ)

/-- The linear map composing copy extension, partial-swap conjugation, and right partial trace. -/
noncomputable def partialSwapChannelMap {D : ℕ} (ρ : Operator D) (θ : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  (traceRightLM D).comp ((conjStep θ).comp (tensorWithCopy ρ))

set_option maxHeartbeats 400000 in

/-- The matrix-map composition implementing a partial-swap step is completely positive for a
positive semidefinite copy. -/
theorem completelyPositive_partialSwapChannelMap_comp {D : ℕ} (ρ : Operator D)
    (hρ : ρ.PosSemidef) (θ : ℝ) :
    MatrixMap.IsCompletelyPositive
      ((traceRightLM D).comp ((conjStep θ).comp (tensorWithCopy ρ))) :=
  MatrixMap.IsCompletelyPositive.comp
    (MatrixMap.IsCompletelyPositive.comp
      (completelyPositive_tensorWithCopy hρ)
      (completelyPositive_conjStep D θ))
    (completelyPositive_traceRightLM D)

set_option maxHeartbeats 400000 in

/-- The linear map implementing a partial-swap step is completely positive for a positive
semidefinite copy. -/
theorem completelyPositive_partialSwapChannelMap {D : ℕ} (ρ : Operator D)
    (hρ : ρ.PosSemidef) (θ : ℝ) :
    CompletelyPositive
      ((traceRightLM D).comp ((conjStep θ).comp (tensorWithCopy ρ))) :=
  (Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mpr
    (completelyPositive_partialSwapChannelMap_comp ρ hρ θ)

/-- The partial-swap channel map preserves trace when the copy operator has trace one. -/
theorem tracePreserving_partialSwapChannelMap {D : ℕ} (ρ : Operator D)
    (hρ : Matrix.trace ρ = 1) (θ : ℝ) :
    TracePreserving (partialSwapChannelMap ρ θ) := by
  intro σ
  have hunit : (partialSwapMatrix D θ)ᴴ * partialSwapMatrix D θ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp (partialSwapMatrix_unitary D θ)
    rwa [Matrix.star_eq_conjTranspose] at h
  have hmap : partialSwapChannelMap ρ θ σ
      = Matrix.traceRight (partialSwapMatrix D θ * TensorGate σ ρ
          * (partialSwapMatrix D θ)ᴴ) := by
    rw [partialSwapChannelMap, LinearMap.comp_apply, LinearMap.comp_apply,
      conjStep_apply, tensorWithCopy_apply, traceRightLM_apply]
  rw [hmap]
  calc Matrix.trace (Matrix.traceRight
        (partialSwapMatrix D θ * TensorGate σ ρ * (partialSwapMatrix D θ)ᴴ))
      = Matrix.trace (partialSwapMatrix D θ * TensorGate σ ρ
          * (partialSwapMatrix D θ)ᴴ) := Matrix.traceRight_trace _
    _ = Matrix.trace ((partialSwapMatrix D θ)ᴴ * partialSwapMatrix D θ * TensorGate σ ρ) :=
        Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (TensorGate σ ρ) := by rw [hunit, Matrix.one_mul]
    _ = Matrix.trace σ * Matrix.trace ρ := Matrix.trace_kronecker _ _
    _ = Matrix.trace σ := by rw [hρ, mul_one]

/-- The partial-swap step packaged as a quantum channel for a density copy `ρ`. -/
noncomputable def partialSwapChannel {D : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (θ : ℝ) : QuantumChannel D D where
  map := partialSwapChannelMap ρ θ
  completelyPositive := by
    simp only [partialSwapChannelMap]
    exact completelyPositive_partialSwapChannelMap ρ hρ.1 θ
  tracePreserving := tracePreserving_partialSwapChannelMap ρ hρ.2 θ

/-- The underlying partial-swap quantum channel acts by `partialSwapOutput`. -/
theorem partialSwapChannel_map {D : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (θ : ℝ) (σ : Operator D) :
    (partialSwapChannel ρ hρ θ).map σ = partialSwapOutput ρ θ σ := by
  rw [partialSwapChannel, partialSwapOutput, partialTrace_eq_traceRight]
  rfl

/-- The partial-swap channel realizes `partialSwapOutput`, preserves its input trace, and sends
density operators to density operators. -/
theorem partial_swap_cptp_bridge {D : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (θ : ℝ) (σ : Operator D) :
    (partialSwapChannel ρ hρ θ).map σ = partialSwapOutput ρ θ σ ∧
    Matrix.trace (partialSwapOutput ρ θ σ) = Matrix.trace σ ∧
    (IsDensityOperator σ → IsDensityOperator (partialSwapOutput ρ θ σ)) := by
  refine ⟨partialSwapChannel_map ρ hρ θ σ, ?_, ?_⟩
  · rw [← partialSwapChannel_map ρ hρ θ σ]
    exact (partialSwapChannel ρ hρ θ).tracePreserving σ
  · intro hσ
    rw [← partialSwapChannel_map ρ hρ θ σ]
    exact (partialSwapChannel ρ hρ θ).preservesDensity hσ

/-- The register equivalence regrouping system, copy, and reference registers so that the copy
register comes last. -/
def copyRelabel (D r : ℕ) : (Fin D × Fin D) × Fin r ≃ (Fin D × Fin r) × Fin D where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv p := by rcases p with ⟨⟨a, c⟩, b⟩; simp
  right_inv q := by rcases q with ⟨⟨a, b⟩, c⟩; simp

/-- The copy relabeling sends `((system, copy), reference)` to `((system, reference), copy)`. -/
theorem copyRelabel_apply (D r : ℕ) (p : (Fin D × Fin D) × Fin r) :
    copyRelabel D r p = ((p.1.1, p.2), p.1.2) := rfl

/-- The inverse copy relabeling restores the grouping `((system, copy), reference)`. -/
theorem copyRelabel_symm_apply (D r : ℕ) (q : (Fin D × Fin r) × Fin D) :
    (copyRelabel D r).symm q = ((q.1.1, q.2), q.1.2) := rfl

/-- The partial-swap output on a system with an untouched reference register, computed by
adjoining and tracing out a copy. -/
noncomputable def partialSwapReferenceOutput {D : ℕ} (ρ : Operator D) (θ : ℝ) (r : ℕ)
    (σ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ :=
  Matrix.traceRight
    (((TensorGate (partialSwapMatrix D θ) (1 : Operator r)).submatrix
        (copyRelabel D r).symm (copyRelabel D r).symm) * (σ ⊗ₖ ρ) *
      (((TensorGate (partialSwapMatrix D θ) (1 : Operator r)).submatrix
        (copyRelabel D r).symm (copyRelabel D r).symm)).conjTranspose)

/-- The extension of a matrix linear map that applies it to each pair of reference-register
indices. -/
private noncomputable def blockMap {I J R : Type*} [Fintype I] [Fintype J] [Fintype R]
    [DecidableEq I] [DecidableEq J]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (σ : Matrix (I × R) (I × R) ℂ) : Matrix (J × R) (J × R) ℂ :=
  fun x y => T (fun i j => σ (i, x.2) (j, y.2)) x.1 y.1

/-- The reference extension `tensorLeft T` agrees with the blockwise map `blockMap T`. -/
private theorem tensorLeft_eq_blockMap {D R : ℕ} (T : Operator D →ₗ[ℂ] Operator D)
    (σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft T σ = blockMap T σ := rfl

/-- Blockwise reference extension preserves composition of matrix linear maps. -/
private theorem blockMap_comp {I J K R : Type*} [Fintype I] [Fintype J] [Fintype K]
    [Fintype R] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (S : Matrix J J ℂ →ₗ[ℂ] Matrix K K ℂ) (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (σ : Matrix (I × R) (I × R) ℂ) :
    blockMap (S.comp T) σ = blockMap S (blockMap T σ) := rfl

/-- Reference extension preserves addition of matrix linear maps. -/
theorem tensorLeft_map_add {D E R : ℕ} (S T : Operator D →ₗ[ℂ] Operator E)
    (σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (S + T) σ = tensorLeft S σ + tensorLeft T σ := by
  ext x y
  simp only [tensorLeft, LinearMap.add_apply, Matrix.add_apply]

/-- Reference extension preserves subtraction of matrix linear maps. -/
theorem tensorLeft_map_sub {D E R : ℕ} (S T : Operator D →ₗ[ℂ] Operator E)
    (σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (S - T) σ = tensorLeft S σ - tensorLeft T σ := by
  ext x y
  simp only [tensorLeft, LinearMap.sub_apply, Matrix.sub_apply]

/-- Reference extension preserves complex scalar multiplication of matrix linear maps. -/
theorem tensorLeft_map_smul {D E R : ℕ} (c : ℂ) (T : Operator D →ₗ[ℂ] Operator E)
    (σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (c • T) σ = c • tensorLeft T σ := by
  ext x y
  simp only [tensorLeft, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul]

/-- The blockwise copy-extension map is the Kronecker product with `ρ`, expressed using
`copyRelabel`. -/
private theorem blockMap_tensorWithCopy {D R : ℕ} (ρ : Operator D)
    (σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    blockMap (tensorWithCopy ρ) σ
      = (σ ⊗ₖ ρ).submatrix (copyRelabel D R) (copyRelabel D R) := by
  ext ⟨⟨a, c⟩, b⟩ ⟨⟨a', c'⟩, b'⟩
  simp only [blockMap, tensorWithCopy_apply, tensorGate_apply, Matrix.submatrix_apply,
    copyRelabel_apply, Matrix.kronecker_apply]

/-- The blockwise extension of partial-swap conjugation is conjugation by the partial swap
tensored with the reference identity. -/
private theorem blockMap_conjStep {D R : ℕ} (θ : ℝ)
    (M : Matrix ((Fin D × Fin D) × Fin R) ((Fin D × Fin D) × Fin R) ℂ) :
    blockMap (conjStep θ) M
      = TensorGate (partialSwapMatrix D θ) (1 : Operator R) * M
          * (TensorGate (partialSwapMatrix D θ) (1 : Operator R)).conjTranspose := by
  rw [tensorGate_conjTranspose]
  ext ⟨x, b⟩ ⟨y, b'⟩
  classical
  simp only [blockMap, conjStep_apply, Matrix.mul_apply, tensorGate_apply,
    Matrix.conjTranspose_one, Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul,
    mul_zero, mul_one, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- The blockwise extension of the copy partial trace is the right partial trace after
regrouping the registers. -/
private theorem blockMap_traceRightLM {D R : ℕ}
    (M : Matrix ((Fin D × Fin D) × Fin R) ((Fin D × Fin D) × Fin R) ℂ) :
    blockMap (traceRightLM D) M
      = Matrix.traceRight (M.submatrix (copyRelabel D R).symm (copyRelabel D R).symm) := by
  ext ⟨i, b⟩ ⟨j, b'⟩
  simp only [blockMap, traceRightLM_apply, Matrix.traceRight, Matrix.submatrix_apply,
    copyRelabel_symm_apply]
  rfl

/-- For a density copy, the explicit reference-register partial-swap output agrees with
`tensorLeft` of the partial-swap channel map. -/
theorem partial_swap_actual_reference_bridge {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (θ : ℝ) (r : ℕ)
    (σ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    partialSwapReferenceOutput ρ θ r σ = tensorLeft (partialSwapChannel ρ hρ θ).map σ := by
  have hbi : Function.Bijective
      ((copyRelabel D r).symm : ((Fin D × Fin r) × Fin D) → ((Fin D × Fin D) × Fin r)) :=
    (copyRelabel D r).symm.bijective
  have hss : ((σ ⊗ₖ ρ).submatrix (copyRelabel D r) (copyRelabel D r)).submatrix
      (copyRelabel D r).symm (copyRelabel D r).symm = (σ ⊗ₖ ρ) := by
    ext q₁ q₂
    simp only [Matrix.submatrix_apply, copyRelabel_apply, copyRelabel_symm_apply]
  have hmap : (partialSwapChannel ρ hρ θ).map
      = (traceRightLM D).comp ((conjStep θ).comp (tensorWithCopy ρ)) := rfl
  rw [hmap, tensorLeft_eq_blockMap, blockMap_comp, blockMap_comp,
    blockMap_traceRightLM, blockMap_conjStep, blockMap_tensorWithCopy]
  rw [partialSwapReferenceOutput]
  have h1 : ∀ A B : Matrix ((Fin D × Fin D) × Fin r) ((Fin D × Fin D) × Fin r) ℂ,
      (A * B).submatrix (copyRelabel D r).symm (copyRelabel D r).symm
        = A.submatrix (copyRelabel D r).symm (copyRelabel D r).symm
          * B.submatrix (copyRelabel D r).symm (copyRelabel D r).symm :=
    fun A B => Matrix.submatrix_mul A B _ _ _ hbi
  rw [h1, h1, hss]
  rfl

/-- The linear map sending an operator `τ` to `Matrix.trace τ • ρ`. -/
noncomputable def traceSmulLeft {D : ℕ} (ρ : Operator D) :
    Operator D →ₗ[ℂ] Operator D where
  toFun τ := Matrix.trace τ • ρ
  map_add' := by
    intro a b
    ext i j
    simp [Matrix.trace_add, add_mul]
  map_smul' := by
    intro c a
    ext i j
    simp [Matrix.trace_smul, Matrix.trace_smul, mul_assoc]

/-- The map `traceSmulLeft ρ` acts by multiplying `ρ` by the input trace. -/
theorem traceSmulLeft_apply {D : ℕ} (ρ τ : Operator D) :
    traceSmulLeft ρ τ = Matrix.trace τ • ρ := rfl

/-- Extending the trace-and-prepare map by a reference register replaces the system by `ρ` and
retains the left partial trace. -/
theorem tensorLeft_traceSmulLeft {D R : ℕ} (ρ : Operator D)
    (σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (traceSmulLeft ρ) σ = TensorGate ρ (Matrix.traceLeft σ) := by
  ext ⟨i, b⟩ ⟨j, b'⟩
  show (∑ k : Fin D, σ (k, b) (k, b')) * ρ i j
      = ρ i j * (∑ k : Fin D, σ (k, b) (k, b'))
  rw [mul_comm]

/-- The reference extension of left multiplication by `ρ` is left multiplication by `TensorGate
ρ 1`. -/
theorem tensorLeft_mulLeft {D R : ℕ} (ρ : Operator D)
    (σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (LinearMap.mulLeft ℂ ρ) σ = TensorGate ρ (1 : Operator R) * σ := by
  ext ⟨i, b⟩ ⟨j, b'⟩
  classical
  simp only [tensorLeft, LinearMap.mulLeft_apply, Matrix.mul_apply, tensorGate_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The reference extension of right multiplication by `ρ` is right multiplication by
`TensorGate ρ 1`. -/
theorem tensorLeft_mulRight {D R : ℕ} (ρ : Operator D)
    (σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (LinearMap.mulRight ℂ ρ) σ = σ * TensorGate ρ (1 : Operator R) := by
  ext ⟨i, b⟩ ⟨j, b'⟩
  classical
  simp only [tensorLeft, LinearMap.mulRight_apply, Matrix.mul_apply, tensorGate_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The reference extension of a trace-preserving map preserves trace. -/
theorem tensorLeft_trace {D E R : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (hT : TracePreserving T) (σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    Matrix.trace (tensorLeft T σ) = Matrix.trace σ := by
  have key : ∀ b : Fin R, Matrix.trace (T (fun i j => σ (i, b) (j, b)))
      = Matrix.trace (fun i j => σ (i, b) (j, b)) := fun b => hT _
  simp only [Matrix.trace, Matrix.diag_apply, tensorLeft, Fintype.sum_prod_type]
  calc ∑ x : Fin E, ∑ b : Fin R, (T (fun i j => σ (i, b) (j, b))) x x
      = ∑ b : Fin R, ∑ x : Fin E, (T (fun i j => σ (i, b) (j, b))) x x := Finset.sum_comm
    _ = ∑ b : Fin R, Matrix.trace (T (fun i j => σ (i, b) (j, b))) :=
        Finset.sum_congr rfl fun b _ => rfl
    _ = ∑ b : Fin R, Matrix.trace (fun i j => σ (i, b) (j, b)) :=
        Finset.sum_congr rfl fun b _ => key b
    _ = ∑ b : Fin R, ∑ i : Fin D, σ (i, b) (i, b) := rfl
    _ = ∑ i : Fin D, ∑ b : Fin R, σ (i, b) (i, b) := Finset.sum_comm

/-- With a reference register, partial-swap output is the cosine-square input plus the
sine-square reset term minus the sine-cosine commutator term. It preserves positivity and
trace for a density copy. -/
theorem partial_swap_reference_output_formula {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (θ : ℝ) (r : ℕ)
    (σ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    partialSwapReferenceOutput ρ θ r σ =
      ((Real.cos θ)^2 : ℂ) • σ + ((Real.sin θ)^2 : ℂ) • TensorGate ρ (Matrix.traceLeft σ) -
      (Complex.I * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) •
        (TensorGate ρ (1 : Operator r) * σ - σ * TensorGate ρ (1 : Operator r)) ∧
    (σ.PosSemidef → (partialSwapReferenceOutput ρ θ r σ).PosSemidef) ∧
    Matrix.trace (partialSwapReferenceOutput ρ θ r σ) = Matrix.trace σ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [partial_swap_actual_reference_bridge ρ hρ θ r σ]
    have hmap : (partialSwapChannel ρ hρ θ).map
        = ((Real.cos θ : ℂ))^2 • LinearMap.id
          + ((Real.sin θ : ℂ))^2 • traceSmulLeft ρ
          - (Complex.I * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) •
              ((LinearMap.mulLeft ℂ ρ) - (LinearMap.mulRight ℂ ρ)) := by
      apply LinearMap.ext
      intro τ
      rw [partialSwapChannel_map ρ hρ θ τ, partial_swap_actual_output_formula ρ τ θ,
        hρ.2, one_smul]
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        traceSmulLeft_apply, smul_sub]
    rw [hmap, tensorLeft_map_sub, tensorLeft_map_add, tensorLeft_map_smul,
      tensorLeft_map_smul, tensorLeft_map_smul, tensorLeft_map_sub, tensorLeft_id,
      tensorLeft_traceSmulLeft, tensorLeft_mulLeft, tensorLeft_mulRight]
  · intro hσ
    rw [partial_swap_actual_reference_bridge ρ hρ θ r σ]
    exact tensorLeft_posSemidef (partialSwapChannel ρ hρ θ).completelyPositive hσ
  · rw [partial_swap_actual_reference_bridge ρ hρ θ r σ]
    exact tensorLeft_trace _ (partialSwapChannel ρ hρ θ).tracePreserving σ

/-- The left endpoint belongs to the real segment joining two real numbers. -/
private theorem self_mem_segment_left (a b : ℝ) : a ∈ segment ℝ a b := by
  rw [← affineSegment_eq_segment]
  exact left_mem_affineSegment (R := ℝ) _ _

/-- The right endpoint belongs to the real segment joining two real numbers. -/
private theorem self_mem_segment_right (a b : ℝ) : b ∈ segment ℝ a b := by
  rw [← affineSegment_eq_segment]
  exact right_mem_affineSegment (R := ℝ) _ _

/-- The trigonometric remainder `|θ - sin θ * cos θ|` is at most `2 * θ ^ 2`. -/
private theorem abs_sub_sin_mul_cos_le (θ : ℝ) :
    |θ - Real.sin θ * Real.cos θ| ≤ 2 * θ ^ 2 := by
  rcases le_or_gt 1 |θ| with hbig | hsmall
  · have h1 : |Real.sin θ * Real.cos θ| ≤ 1 := by
      rw [abs_mul]
      nlinarith [Real.abs_sin_le_one θ, Real.abs_cos_le_one θ,
        abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
    have habssq : |θ| * |θ| = θ * θ := by rw [abs_mul_abs_self]
    have habs : |θ| ≤ θ ^ 2 := by nlinarith [hbig, habssq, abs_nonneg θ]
    calc |θ - Real.sin θ * Real.cos θ| ≤ |θ| + |Real.sin θ * Real.cos θ| := abs_sub _ _
      _ ≤ |θ| + 1 := add_le_add (le_refl _) h1
      _ ≤ 2 * θ ^ 2 := by nlinarith
  · have hderiv : ∀ x : ℝ, HasDerivAt (fun t => t - Real.sin t * Real.cos t)
        (1 - (Real.cos x * Real.cos x + Real.sin x * -Real.sin x)) x :=
      fun x => (hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x))
    have hbound : ∀ x ∈ segment ℝ 0 θ,
        ‖deriv (fun t => t - Real.sin t * Real.cos t) x‖ ≤ 2 * θ ^ 2 := by
      intro x hx
      rw [(hderiv x).deriv]
      have hval : (1 - (Real.cos x * Real.cos x + Real.sin x * -Real.sin x)
          : ℝ) = 2 * Real.sin x * Real.sin x := by
        linear_combination -(Real.cos_sq_add_sin_sq x)
      have hxle : |x| ≤ |θ| := by
        rcases le_or_gt 0 θ with hθ | hθ
        · rw [mem_segment_iff_wbtw] at hx
          rw [wbtw_iff_of_le hθ] at hx
          rw [abs_of_nonneg hθ, abs_of_nonneg hx.1]
          exact hx.2
        · rw [segment_symm] at hx
          rw [mem_segment_iff_wbtw] at hx
          rw [wbtw_iff_of_le (by linarith : θ ≤ 0)] at hx
          rw [abs_of_nonpos (by linarith : θ ≤ 0), abs_of_nonpos hx.2]
          linarith
      have hxx : |x| * |x| = x * x := by rw [abs_mul_abs_self]
      have hθθ : |θ| * |θ| = θ * θ := by rw [abs_mul_abs_self]
      have hprod : |x| * |x| ≤ |θ| * |θ| :=
        mul_le_mul hxle hxle (abs_nonneg x) (abs_nonneg θ)
      have hx2 : x ^ 2 ≤ θ ^ 2 := by nlinarith [hprod, hxx, hθθ]
      rw [hval, Real.norm_eq_abs,
        abs_of_nonneg (by nlinarith [mul_self_nonneg (Real.sin x)])]
      nlinarith [Real.sin_sq_le_sq (x := x), hx2]
    have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun t => t - Real.sin t * Real.cos t)
      (s := segment ℝ (0 : ℝ) θ) (fun x hx => (hderiv x).differentiableAt) hbound
      (convex_segment (0 : ℝ) θ) (self_mem_segment_left (0 : ℝ) θ)
      (self_mem_segment_right (0 : ℝ) θ)
    have hle : |θ - Real.sin θ * Real.cos θ| ≤ 2 * θ ^ 2 * |θ| := by
      simpa [Real.norm_eq_abs] using hMVT
    nlinarith [hsmall, hle, sq_nonneg θ]

/-- The operator-norm error of the first-order commutator approximation is bounded by the stated
squared-sine reset term and trigonometric commutator correction. -/
theorem partial_swap_derived_first_order_error {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (σ : Operator D) (θ : ℝ) :
    ‖partialSwapOutput ρ θ σ - (σ - (Complex.I * (θ : ℂ)) • (ρ*σ-σ*ρ))‖ ≤
      (Real.sin θ)^2 * (‖Matrix.trace σ‖ * ‖ρ‖ + ‖σ‖) +
      2 * |θ - Real.sin θ * Real.cos θ| * ‖ρ‖ * ‖σ‖ := by
  have hcast : ((Real.cos θ)^2 : ℂ) = ((Real.cos θ : ℂ)) * ((Real.cos θ : ℂ)) := by
    push_cast; ring
  have hc2 : ((Real.cos θ : ℂ)) * ((Real.cos θ : ℂ))
      = 1 - ((Real.sin θ : ℂ)) * ((Real.sin θ : ℂ)) := by
    linear_combination complex_cos_sq_add_sin_sq θ
  have key : partialSwapOutput ρ θ σ - (σ - (Complex.I * (θ : ℂ)) • (ρ*σ-σ*ρ))
      = ((Real.sin θ)^2 : ℂ) • (Matrix.trace σ • ρ - σ)
        - (Complex.I * (((Real.sin θ : ℂ)) * ((Real.cos θ : ℂ)) - (θ : ℂ))) • (ρ*σ - σ*ρ) := by
    rw [partial_swap_actual_output_formula ρ σ θ, hρ.2, one_smul, hcast, hc2]
    module
  have hcoeff : (((Real.sin θ : ℂ)) * ((Real.cos θ : ℂ)) - (θ : ℂ))
      = ((Real.sin θ * Real.cos θ - θ : ℝ) : ℂ) := by
    push_cast
    ring
  have hcomm : ‖ρ*σ - σ*ρ‖ ≤ 2 * ‖ρ‖ * ‖σ‖ := by
    calc ‖ρ*σ - σ*ρ‖ ≤ ‖ρ*σ‖ + ‖σ*ρ‖ := norm_sub_le _ _
      _ ≤ ‖ρ‖ * ‖σ‖ + ‖σ‖ * ‖ρ‖ := add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
      _ = 2 * ‖ρ‖ * ‖σ‖ := by ring
  rw [key]
  have hnormcast : ‖((Real.sin θ)^2 : ℂ)‖ = (Real.sin θ)^2 := by
    have hc : ((Real.sin θ)^2 : ℂ) = ((Real.sin θ : ℂ)) * ((Real.sin θ : ℂ)) := by
      push_cast; ring
    rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_mul_abs_self (Real.sin θ)).trans (pow_two (Real.sin θ)).symm
  have hsmul : ‖Matrix.trace σ • ρ - σ‖ ≤ ‖Matrix.trace σ‖ * ‖ρ‖ + ‖σ‖ := by
    calc ‖Matrix.trace σ • ρ - σ‖ ≤ ‖Matrix.trace σ • ρ‖ + ‖σ‖ := norm_sub_le _ _
      _ = ‖Matrix.trace σ‖ * ‖ρ‖ + ‖σ‖ := by rw [norm_smul]
  calc ‖((Real.sin θ)^2 : ℂ) • (Matrix.trace σ • ρ - σ)
          - (Complex.I * (((Real.sin θ : ℂ)) * ((Real.cos θ : ℂ)) - (θ : ℂ))) • (ρ*σ - σ*ρ)‖
      ≤ ‖((Real.sin θ)^2 : ℂ) • (Matrix.trace σ • ρ - σ)‖
          + ‖(Complex.I * (((Real.sin θ : ℂ)) * ((Real.cos θ : ℂ)) - (θ : ℂ))) • (ρ*σ - σ*ρ)‖ :=
        norm_sub_le _ _
    _ = (Real.sin θ)^2 * ‖Matrix.trace σ • ρ - σ‖
          + ‖Complex.I * (((Real.sin θ : ℂ)) * ((Real.cos θ : ℂ)) - (θ : ℂ))‖ * ‖ρ*σ - σ*ρ‖ := by
        rw [norm_smul, norm_smul, hnormcast]
    _ = (Real.sin θ)^2 * ‖Matrix.trace σ • ρ - σ‖
          + |θ - Real.sin θ * Real.cos θ| * ‖ρ*σ - σ*ρ‖ := by
        rw [norm_mul, Complex.norm_I, one_mul, hcoeff, Complex.norm_real, Real.norm_eq_abs,
          abs_sub_comm]
    _ ≤ (Real.sin θ)^2 * (‖Matrix.trace σ‖ * ‖ρ‖ + ‖σ‖)
          + |θ - Real.sin θ * Real.cos θ| * (2 * ‖ρ‖ * ‖σ‖) := by
        have hscalar : |θ - Real.sin θ * Real.cos θ| ≥ 0 := abs_nonneg _
        have h1 : (0:ℝ) ≤ ‖Matrix.trace σ‖ * ‖ρ‖ + ‖σ‖ := by positivity
        nlinarith [hsmul, hcomm, hscalar, h1]
    _ = (Real.sin θ)^2 * (‖Matrix.trace σ‖ * ‖ρ‖ + ‖σ‖)
          + 2 * |θ - Real.sin θ * Real.cos θ| * ‖ρ‖ * ‖σ‖ := by ring

/-- The sine-cosine remainder is bounded quadratically, yielding the stated `θ ^ 2`
operator-norm bound for the first-order partial-swap approximation with a density copy. -/
theorem partial_swap_trig_and_quadratic_error :
    (∀ θ : ℝ, |θ - Real.sin θ * Real.cos θ| ≤ 2 * θ^2) ∧
      (∀ {D : ℕ} (ρ : Operator D) (_hρ : IsDensityOperator ρ) (σ : Operator D) (θ : ℝ),
        ‖partialSwapOutput ρ θ σ - (σ - (Complex.I * (θ : ℂ)) • (ρ*σ-σ*ρ))‖ ≤
          θ^2 * (‖Matrix.trace σ‖ * ‖ρ‖ + ‖σ‖ + 4 * ‖ρ‖ * ‖σ‖)) := by
  refine ⟨abs_sub_sin_mul_cos_le, fun {D} ρ _hρ σ θ => ?_⟩
  have hG7 := partial_swap_derived_first_order_error ρ _hρ σ θ
  have hs2 : (Real.sin θ)^2 ≤ θ^2 := Real.sin_sq_le_sq
  have hscalar := abs_sub_sin_mul_cos_le θ
  have hn : (0:ℝ) ≤ ‖ρ‖ := norm_nonneg _
  have hn' : (0:ℝ) ≤ ‖σ‖ := norm_nonneg _
  have hnt : (0:ℝ) ≤ ‖Matrix.trace σ‖ := norm_nonneg _
  have hAB : (0:ℝ) ≤ ‖Matrix.trace σ‖ * ‖ρ‖ + ‖σ‖ := by positivity
  have hC : (0:ℝ) ≤ ‖ρ‖ * ‖σ‖ := by positivity
  nlinarith [hG7, hs2, hscalar, hn, hn', hnt, hAB, hC]

end Qatlib.Concepts.CopyEvolution.Discriminate
