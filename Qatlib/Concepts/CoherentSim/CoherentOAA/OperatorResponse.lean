/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Operator-valued responses and Hermitian dilation

This module extends the phased alternating response identities from scalar singular pairs to
operator intertwiners. An `OperatorSignalPair` relates two signal embeddings to a common matrix
parameter, and its response is expressed by polynomial evaluation at that matrix.

The Hermitian dilation of a rectangular encoded matrix supplies such an intertwiner. Odd and
even compressed QSVT sequences consequently equal the appropriate blocks of a polynomial in the
dilation, following the singular value transformation framework of [GilyenSuLowWiebe2019].

## Main statements

* `OperatorSignalPair.phased_response`: the full response splits into signal and residual
  polynomial terms.
* `qsvt_operator_intertwiner`: compression evaluates the response polynomial on the intertwining
  operator.
* `qsvt_odd_eq_dilation`: odd QSVT selects the upper-right polynomial block.
* `qsvt_even_left_eq_dilation`: even QSVT selects the upper-left polynomial block.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib
open Qatlib
open Qatlib
local notation:70 A " ⬝ₘ " B =>
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]

/-- A unitary, two orthogonal projectors, and two fixed signal matrices satisfying forward and
backward intertwining equations with a common operator `S`. -/
structure OperatorSignalPair (U P Q : Matrix H H ℂ) (S : Matrix K K ℂ)
    (r l : Matrix H K ℂ) : Prop where
  unitary : U ∈ Matrix.unitaryGroup H ℂ
  right_projector : IsOrthogonalProjector P
  left_projector : IsOrthogonalProjector Q
  right_fixed : P * r = r
  left_fixed : Q * l = l
  forward : (Q * U * r : Matrix H K ℂ) = l * S
  backward : (P * Uᴴ * l : Matrix H K ℂ) = r * S

/-- The backward residual `Uᴴ * l - r * S` of an operator signal pair. -/
noncomputable def operatorRightResidual (U : Matrix H H ℂ) (S : Matrix K K ℂ)
    (r l : Matrix H K ℂ) : Matrix H K ℂ := Uᴴ * l - r * S

/-- The forward residual `U * r - l * S` of an operator signal pair. -/
noncomputable def operatorLeftResidual (U : Matrix H H ℂ) (S : Matrix K K ℂ)
    (r l : Matrix H K ℂ) : Matrix H K ℂ := U * r - l * S

/-- Taking the unitary adjoint and exchanging the projectors and signal matrices preserves the
operator signal-pair conditions. -/
theorem OperatorSignalPair.adjoint {U P Q : Matrix H H ℂ} {S : Matrix K K ℂ}
    {r l : Matrix H K ℂ} (h : OperatorSignalPair U P Q S r l) :
    OperatorSignalPair Uᴴ Q P S l r := by
  refine ⟨adjoint_unitary h.unitary, h.left_projector, h.right_projector,
    h.left_fixed, h.right_fixed, h.backward, ?_⟩
  simpa using h.forward

/-- The left projector annihilates the forward residual of an operator signal pair. -/
theorem OperatorSignalPair.leftResidual_zero {U P Q : Matrix H H ℂ} {S : Matrix K K ℂ}
    {r l : Matrix H K ℂ} (h : OperatorSignalPair U P Q S r l) :
    Q * operatorLeftResidual U S r l = 0 := by
  simp only [operatorLeftResidual, Matrix.mul_sub, ← Matrix.mul_assoc,
    h.forward, h.left_fixed, sub_self]

omit [DecidableEq H] in

/-- The forward action on the right signal matrix splits into `l * S` and the forward residual. -/
theorem operator_signal_first (U : Matrix H H ℂ) (S : Matrix K K ℂ)
    (r l : Matrix H K ℂ) : (U * r : Matrix H K ℂ) = l * S + operatorLeftResidual U S r l := by
  unfold operatorLeftResidual
  abel

/-- Applying the unitary to the backward residual gives `l * (1 - S ^ 2)` minus the forward
residual times `S`. -/
theorem OperatorSignalPair.signal_second [DecidableEq K]
    {U P Q : Matrix H H ℂ} {S : Matrix K K ℂ}
    {r l : Matrix H K ℂ} (h : OperatorSignalPair U P Q S r l) :
    (U * operatorRightResidual U S r l : Matrix H K ℂ) =
      l * (1 - S ^ 2) - operatorLeftResidual U S r l * S := by
  have hu : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using h.unitary.2
  simp only [operatorRightResidual, operatorLeftResidual, pow_two,
    Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hu, Matrix.one_mul,
    Matrix.mul_one]
  abel

/-- A phased unitary step transforms a signal-residual combination according to the
operator-valued two-term recurrence. -/
theorem OperatorSignalPair.step [DecidableEq K]
    {U P Q : Matrix H H ℂ} {S : Matrix K K ℂ}
    {r l : Matrix H K ℂ} (h : OperatorSignalPair U P Q S r l)
    (z : ℂ) (a b : Matrix K K ℂ) :
    (phaseRotation Q z * U * (r * a + operatorRightResidual U S r l * b) : Matrix H K ℂ) =
      l * (z • (S * a + (1 - S ^ 2) * b)) +
        operatorLeftResidual U S r l * (star z • (a - S * b)) := by
  rw [Matrix.mul_assoc, Matrix.mul_add, ← Matrix.mul_assoc U r a,
    ← Matrix.mul_assoc U (operatorRightResidual U S r l) b,
    operator_signal_first U S r l, h.signal_second]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    ← Matrix.mul_assoc, phaseRotation_mul_of_fixed h.left_fixed,
    phaseRotation_mul_of_zero h.leftResidual_zero, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_sub]
  module

/-- The phased alternating word acts on its parity-selected source as the sum of the signal and
residual response polynomials evaluated at `S`. -/
theorem OperatorSignalPair.phased_response [DecidableEq K]
    {U P Q : Matrix H H ℂ} {S : Matrix K K ℂ}
    {r l : Matrix H K ℂ} (h : OperatorSignalPair U P Q S r l) (base : ℂ) (zs : List ℂ) :
    (phasedAlternating U P Q base zs * alternatingSource r l zs : Matrix H K ℂ) =
      l * aeval S (responseP base zs) +
        operatorLeftResidual U S r l * aeval S (responseQ base zs) := by
  induction zs generalizing U P Q r l with
  | nil =>
    simpa [phasedAlternating, alternatingSource, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_smul] using phaseRotation_mul_of_fixed h.left_fixed base
  | cons z zs ih =>
    rw [phasedAlternating, alternatingSource, Matrix.mul_assoc, ih h.adjoint]
    have hs := h.step z (aeval S (responseP base zs)) (aeval S (responseQ base zs))
    simpa [operatorLeftResidual, operatorRightResidual, responseP_cons, responseQ_cons,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul] using hs

/-- Projection onto the left signal space removes the residual term, leaving `l * aeval S
(responseP base zs)`. -/
theorem OperatorSignalPair.projected_response [DecidableEq K]
    {U P Q : Matrix H H ℂ} {S : Matrix K K ℂ}
    {r l : Matrix H K ℂ} (h : OperatorSignalPair U P Q S r l) (base : ℂ) (zs : List ℂ) :
    (Q * phasedAlternating U P Q base zs * alternatingSource r l zs : Matrix H K ℂ) =
      l * aeval S (responseP base zs) := by
  rw [Matrix.mul_assoc, h.phased_response]
  simp [Matrix.mul_add, ← Matrix.mul_assoc, h.left_fixed, h.leftResidual_zero]

section Encoding

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- Two matrix intertwiners for an encoded block and its adjoint lift to an operator signal pair
in the encoding frames. -/
theorem operatorSignalPair_of_encoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {S : Matrix K K ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : (A * v : Matrix O K ℂ) = w * S)
    (haw : (Aᴴ * w : Matrix I K ℂ) = v * S) :
    OperatorSignalPair U (rangeProjector R) (rangeProjector L) S (R * v) (L * w) := by
  refine ⟨h.unitary, rangeProjector_isOrthogonalProjector h.right_isometry,
    rangeProjector_isOrthogonalProjector h.left_isometry, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, rangeProjector_mul h.right_isometry]
  · rw [← Matrix.mul_assoc, rangeProjector_mul h.left_isometry]
  · rw [lift_compressed_action h, hav, Matrix.mul_assoc]
  · rw [lift_compressed_action h.adjoint, haw, Matrix.mul_assoc]

/-- Compressing the phased response of lifted intertwiners yields the left intertwiner
multiplied by the response polynomial evaluated at `S`. -/
theorem qsvt_operator_intertwiner [DecidableEq K]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {S : Matrix K K ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : (A * v : Matrix O K ℂ) = w * S)
    (haw : (Aᴴ * w : Matrix I K ℂ) = v * S) (base : ℂ) (zs : List ℂ) :
    Lᴴ * (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs *
      alternatingSource (R * v) (L * w) zs) = w * aeval S (responseP base zs) := by
  have hp := (operatorSignalPair_of_encoding h hav haw).projected_response base zs
  have hL : Lᴴ * L = 1 := h.left_isometry
  have he := congrArg (fun M : Matrix H K ℂ => Lᴴ * M) hp
  simpa [rangeProjector, ← Matrix.mul_assoc, hL] using he

/-- For odd phase-list length, the cross-frame compressed sequence acts on `v` as `w` times the
response polynomial evaluated at `S`. -/
theorem qsvt_operator_odd [DecidableEq K]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {S : Matrix K K ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : (A * v : Matrix O K ℂ) = w * S)
    (haw : (Aᴴ * w : Matrix I K ℂ) = v * S) (base : ℂ) (zs : List ℂ)
    (hodd : zs.length % 2 = 1) :
    (compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R * v :
      Matrix O K ℂ) = w * aeval S (responseP base zs) := by
  have he := qsvt_operator_intertwiner h hav haw base zs
  simpa [compress, Matrix.mul_assoc, alternatingSource_eq, hodd] using he

/-- For even phase-list length, the left-frame compressed sequence acts on `w` by right
multiplication with the response polynomial evaluated at `S`. -/
theorem qsvt_operator_even_left [DecidableEq K]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {S : Matrix K K ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : (A * v : Matrix O K ℂ) = w * S)
    (haw : (Aᴴ * w : Matrix I K ℂ) = v * S) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    (compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L * w :
      Matrix O K ℂ) = w * aeval S (responseP base zs) := by
  have he := qsvt_operator_intertwiner h hav haw base zs
  simpa [compress, Matrix.mul_assoc, alternatingSource_eq, heven] using he

end Encoding

/-- The block matrix with zero diagonal blocks and off-diagonal blocks `A` and `Aᴴ`. -/
noncomputable def hermitianDilation {I O : Type*} (A : Matrix O I ℂ) : Matrix (O ⊕ I) (O ⊕ I) ℂ :=
  Matrix.fromBlocks 0 A Aᴴ 0

omit [Fintype H] [DecidableEq H] [Fintype K] in

/-- The Hermitian dilation equals its conjugate transpose. -/
theorem hermitianDilation_adjoint {I O : Type*} (A : Matrix O I ℂ) :
    (hermitianDilation A)ᴴ = hermitianDilation A := by
  ext i j
  cases i <;> cases j <;> simp [hermitianDilation, Matrix.conjTranspose_apply]

/-- The row-block selector for the output summand of the dilation space. -/
def dilationLeft {I O : Type*} [DecidableEq O] : Matrix O (O ⊕ I) ℂ :=
  Matrix.fromCols 1 0

/-- The row-block selector for the input summand of the dilation space. -/
def dilationRight {I O : Type*} [DecidableEq I] : Matrix I (O ⊕ I) ℂ :=
  Matrix.fromCols 0 1

section Dilation

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

omit [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq I] in

/-- Left multiplication by the output selector extracts the first row block. -/
theorem dilationLeft_mul {J : Type*} (M : Matrix (O ⊕ I) J ℂ) :
    (dilationLeft ⬝ₘ M : Matrix O J ℂ) = M.toRows₁ := by
  rw [dilationLeft, ← Matrix.fromRows_toRows M, Matrix.fromCols_mul_fromRows]
  simp

omit [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq O] in

/-- Left multiplication by the input selector extracts the second row block. -/
theorem dilationRight_mul {J : Type*} (M : Matrix (O ⊕ I) J ℂ) :
    (dilationRight ⬝ₘ M : Matrix I J ℂ) = M.toRows₂ := by
  rw [dilationRight, ← Matrix.fromRows_toRows M, Matrix.fromCols_mul_fromRows]
  simp

omit [Fintype H] [DecidableEq H] [Fintype K] in

/-- The input selector followed by `A` equals the output selector followed by the Hermitian
dilation. -/
theorem dilation_forward (A : Matrix O I ℂ) :
    (A ⬝ₘ dilationRight : Matrix O (O ⊕ I) ℂ) = dilationLeft ⬝ₘ hermitianDilation A := by
  simp [dilationLeft, dilationRight, hermitianDilation, Matrix.fromCols_mul_fromBlocks]

omit [Fintype H] [DecidableEq H] [Fintype K] in

/-- The output selector followed by `Aᴴ` equals the input selector followed by the Hermitian
dilation. -/
theorem dilation_backward (A : Matrix O I ℂ) :
    (Aᴴ ⬝ₘ dilationLeft : Matrix I (O ⊕ I) ℂ) = dilationRight ⬝ₘ hermitianDilation A := by
  simp [dilationLeft, dilationRight, hermitianDilation, Matrix.fromCols_mul_fromBlocks]

omit [Fintype K] in

/-- The cross-frame compression of an odd phased sequence equals the upper-right block of its
response polynomial evaluated on the Hermitian dilation. -/
theorem qsvt_odd_eq_dilation {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (hodd : zs.length % 2 = 1) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R =
      (aeval (hermitianDilation A) (responseP base zs)).toBlocks₁₂ := by
  have he := qsvt_operator_odd h (dilation_forward A) (dilation_backward A) base zs hodd
  rw [dilationLeft_mul] at he
  simpa only [dilationRight, Matrix.mul_fromCols, Matrix.mul_zero, Matrix.mul_one,
    Matrix.toCols₂_fromCols] using! congrArg Matrix.toCols₂ he

omit [Fintype K] in

/-- The left-frame compression of an even phased sequence equals the upper-left block of its
response polynomial evaluated on the Hermitian dilation. -/
theorem qsvt_even_left_eq_dilation {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L =
      (aeval (hermitianDilation A) (responseP base zs)).toBlocks₁₁ := by
  have he := qsvt_operator_even_left h (dilation_forward A) (dilation_backward A) base zs heven
  rw [dilationLeft_mul] at he
  simpa only [dilationLeft, Matrix.mul_fromCols, Matrix.mul_zero, Matrix.mul_one,
    Matrix.toCols₁_fromCols] using! congrArg Matrix.toCols₁ he

omit [Fintype K] in

/-- The right-frame compression of the even sequence using the adjoint oracle equals the
lower-right block of its response polynomial evaluated on the Hermitian dilation. -/
theorem qsvt_even_right_eq_dilation {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    compress R (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R =
      (aeval (hermitianDilation A) (responseP base zs)).toBlocks₂₂ := by
  have he := qsvt_operator_even_left h.adjoint (dilation_backward A)
    (by simpa using dilation_forward A) base zs heven
  rw [dilationRight_mul] at he
  simpa only [dilationRight, Matrix.mul_fromCols, Matrix.mul_zero, Matrix.mul_one,
    Matrix.toCols₂_fromCols] using! congrArg Matrix.toCols₂ he

end Dilation

end Qatlib.Concepts.CoherentSim.CoherentOAA
