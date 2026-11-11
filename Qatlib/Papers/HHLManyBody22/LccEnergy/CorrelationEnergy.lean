/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Qatlib.Concepts.QlsReadoutSpec.PseudoInverse
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Inverse quadratic forms for LCC correlation energy

`lccCorrelationEnergy` is the negative inverse quadratic form `-⟪b, A⁻¹b⟫`. The module relates
it to solutions of the linear system, proves reality for Hermitian invertible matrices, and
establishes a strictly negative real part for positive definite matrices and nonzero input.

`lccCorrelationEnergy_continuousHHLMatrix_eq_pseudoinverse` identifies the inverse solution with
the pseudoinverse solution for a unitary spectral representation with nonzero eigenvalues. See
[BaskaranEtAl2023].

## Main statements

* `conj_lccCorrelationEnergy_eq_self`: For Hermitian `A` with invertible determinant, the
  correlation energy is fixed by conjugation.
* `re_lccCorrelationEnergy_neg_of_posDef`: For positive definite `A` and nonzero `b`, the
  correlation energy has strictly negative real part.
* `lccCorrelationEnergy_continuousHHLMatrix_eq_pseudoinverse`: For a unitary spectral basis with
  all eigenvalues nonzero, the continuous HHL pseudoinverse vector solves the linear system and
  gives the correlation energy through the negative input pairing.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.HHLManyBody22.LccEnergy

open Qatlib.Concepts.QlsReadoutSpec.PseudoInverse
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The negative inverse quadratic form `-(star b ⬝ᵥ (A⁻¹ *ᵥ b))`. -/
def lccCorrelationEnergy (A : Matrix N N ℂ) (b : N → ℂ) : ℂ :=
  - (star b ⬝ᵥ (A⁻¹ *ᵥ b))

/-- Unfolds the correlation energy as the negative inner product of `b` with `A⁻¹ *ᵥ b`. -/
theorem lccCorrelationEnergy_def (A : Matrix N N ℂ) (b : N → ℂ) :
    lccCorrelationEnergy A b = - (star b ⬝ᵥ (A⁻¹ *ᵥ b)) := rfl

/-- If `A` has invertible determinant and `A *ᵥ x = b`, the correlation energy equals `-(star b
⬝ᵥ x)`. -/
theorem lccCorrelationEnergy_eq_neg_inner
    {A : Matrix N N ℂ} (hA : IsUnit A.det) {x b : N → ℂ} (hx : A *ᵥ x = b) :
    lccCorrelationEnergy A b = - (star b ⬝ᵥ x) := by
  have hinv : A⁻¹ *ᵥ b = x := by
    letI := Matrix.invertibleOfIsUnitDet A hA
    exact Matrix.inv_mulVec_eq_vec hx.symm
  rw [lccCorrelationEnergy_def, hinv]

omit [DecidableEq N] in

/-- For Hermitian `A`, pairing `A *ᵥ x` with `x` equals pairing `x` with `A *ᵥ x`. -/
theorem star_mulVec_dotProduct_self {A : Matrix N N ℂ} (hA : A.IsHermitian) (x : N → ℂ) :
    star (A *ᵥ x) ⬝ᵥ x = star x ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.star_mulVec, hA.eq]
  exact (Matrix.dotProduct_mulVec (star x) A x).symm

omit [DecidableEq N] in

/-- The quadratic form of a Hermitian matrix is fixed by complex conjugation. -/
theorem conj_dotProduct_mulVec_self
    {A : Matrix N N ℂ} (hA : A.IsHermitian) (x : N → ℂ) :
    star (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (A *ᵥ x) := by
  rw [← Matrix.star_dotProduct (A *ᵥ x) x]
  exact star_mulVec_dotProduct_self hA x

omit [DecidableEq N] in

/-- If Hermitian `A` satisfies `A *ᵥ x = b`, then `star b ⬝ᵥ x` is fixed by conjugation. -/
theorem conj_dotProduct_solution_eq_self
    {A : Matrix N N ℂ} (hA : A.IsHermitian) {x b : N → ℂ} (hx : A *ᵥ x = b) :
    star (star b ⬝ᵥ x) = star b ⬝ᵥ x := by
  rw [← hx, star_mulVec_dotProduct_self hA x]
  exact conj_dotProduct_mulVec_self hA x

/-- For Hermitian `A` with invertible determinant, the correlation energy is fixed by
conjugation. -/
theorem conj_lccCorrelationEnergy_eq_self
    {A : Matrix N N ℂ} (hA : A.IsHermitian) (hAinv : IsUnit A.det) (b : N → ℂ) :
    star (lccCorrelationEnergy A b) = lccCorrelationEnergy A b := by
  let x : N → ℂ := A⁻¹ *ᵥ b
  have hx : A *ᵥ x = b := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv A hAinv, Matrix.one_mulVec]
  have h : lccCorrelationEnergy A b = - (star b ⬝ᵥ x) :=
    lccCorrelationEnergy_eq_neg_inner hAinv hx
  rw [h, star_neg, conj_dotProduct_solution_eq_self hA hx]

/-- For positive definite `A` and nonzero `b`, the correlation energy has strictly negative real
part. -/
theorem re_lccCorrelationEnergy_neg_of_posDef
    {A : Matrix N N ℂ} (hA : A.PosDef) (b : N → ℂ) (hb : b ≠ 0) :
    RCLike.re (lccCorrelationEnergy A b) < 0 := by
  have hAinv : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  let x : N → ℂ := A⁻¹ *ᵥ b
  have hx : A *ᵥ x = b := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv A hAinv, Matrix.one_mulVec]
  have hxne : x ≠ 0 := by
    intro h
    apply hb
    rw [← hx, h, Matrix.mulVec_zero]
  have hpair : star b ⬝ᵥ x = star x ⬝ᵥ (A *ᵥ x) := by
    rw [← hx]
    exact star_mulVec_dotProduct_self hA.isHermitian x
  have hpos : 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x)) := hA.re_dotProduct_pos hxne
  have heq : lccCorrelationEnergy A b = - (star x ⬝ᵥ (A *ᵥ x)) := by
    rw [lccCorrelationEnergy_eq_neg_inner hAinv hx, hpair]
  rw [heq, map_neg]
  exact neg_neg_of_pos hpos

/-- For a unitary spectral basis with all eigenvalues nonzero, the continuous HHL pseudoinverse
vector solves the linear system and gives the correlation energy through the negative input
pairing. -/
theorem lccCorrelationEnergy_continuousHHLMatrix_eq_pseudoinverse
    {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hne : ∀ i, eig i ≠ 0) (b : Fin D → ℂ) :
    continuousHHLMatrix eig V *ᵥ (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ b) = b ∧
      lccCorrelationEnergy (continuousHHLMatrix eig V) b =
        - (star b ⬝ᵥ (matrixPseudoinverse (continuousHHLMatrix eig V) *ᵥ b)) := by
  obtain ⟨hpseudo, hleft, -⟩ :=
    singular_hermitian_pseudoinverse_and_least_squares D eig V hV

  have hspec : spectralSupport eig V = 1 := by
    unfold spectralSupport
    have hdiag : (fun i => if eig i = 0 then (0 : ℂ) else 1) = fun _ => 1 := by
      funext i; rw [if_neg (hne i)]
    rw [hdiag, Matrix.diagonal_one, Matrix.mul_one]
    exact Matrix.mem_unitaryGroup_iff.mp hV
  have hAR : continuousHHLMatrix eig V * matrixPseudoinverse (continuousHHLMatrix eig V) = 1 := by
    rw [hleft, hspec]
  have hAinv : (continuousHHLMatrix eig V)⁻¹ = matrixPseudoinverse (continuousHHLMatrix eig V) :=
    Matrix.inv_eq_right_inv hAR
  constructor
  · rw [Matrix.mulVec_mulVec, hAR, Matrix.one_mulVec]
  · rw [lccCorrelationEnergy_def, hAinv]

end Qatlib.Papers.HHLManyBody22.LccEnergy
