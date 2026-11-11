/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation

/-!
# Matrix pseudoinverses and QSVT approximation

This module defines `matrixPseudoinverse` from the singular vector decomposition and proves the
four Moore–Penrose identities and uniqueness. The products with the original matrix are
orthogonal projectors, and the pseudoinverse gives a minimum operator norm solution of each
solvable matrix equation.

For a projected unitary encoding, approximation of the scaled reciprocal on positive singular
values yields a block encoding of the scaled pseudoinverse. The construction and its query
counts fit the singular value transformation framework of [GilyenSuLowWiebe2019].

## Main statements

* `matrixPseudoinverse_unique`: the four Moore–Penrose identities characterize the
  pseudoinverse.
* `matrixPseudoinverse_minimumNorm_solution`: solvable systems have the prescribed minimum norm
  solution.
* `matrixPseudoinverse_norm_le`: a positive singular-value gap bounds the pseudoinverse norm.
* `qsvt_pseudoinverse_counted_approximation`: reciprocal approximation yields a counted circuit
  encoding.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

section Algebra
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

/-- The diagonal indicator of the nonzero singular values of `A`. -/
noncomputable def singularSupport (A : Matrix O I ℂ) :
    Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ :=
  diagonal (fun i => if matrixSingularValues A i = 0 then 0 else 1)

/-- The conjugate transpose of the odd singular transform of `A` by the reciprocal function. -/
noncomputable def matrixPseudoinverse (A : Matrix O I ℂ) : Matrix I O ℂ :=
  (oddSingularTransform A (fun x => (x : ℂ)⁻¹))ᴴ

/-- The pseudoinverse is the product of the right singular basis, reciprocal singular-value
diagonal, and adjoint left singular columns. -/
theorem matrixPseudoinverse_eq (A : Matrix O I ℂ) :
    matrixPseudoinverse A = basisColumns (rightSingularBasis A) *
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)⁻¹) *
        (leftSingularColumns A)ᴴ := by
  have hd : (diagonal (fun i : Fin (Fintype.card I) =>
      (matrixSingularValues A i : ℂ)⁻¹))ᴴ =
        diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)⁻¹) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.conjTranspose_apply, hij, Ne.symm]
  simp only [matrixPseudoinverse, oddSingularTransform, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hd, Matrix.mul_assoc]

/-- The singular support matrix is Hermitian. -/
theorem singularSupport_adjoint (A : Matrix O I ℂ) : (singularSupport A)ᴴ = singularSupport A := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [singularSupport]
  · simp [singularSupport, hij, Ne.symm hij]

/-- Right multiplication by the singular support leaves the left singular columns unchanged. -/
theorem leftSingularColumns_mul_support (A : Matrix O I ℂ) :
    leftSingularColumns A * singularSupport A = leftSingularColumns A := by
  classical
  ext o i
  rw [singularSupport, Matrix.mul_diagonal]
  by_cases hi : matrixSingularValues A i = 0
  · simp [hi, leftSingularColumns, leftSingularVector_eq_zero A i hi]
  · simp only [if_neg hi, mul_one]

/-- Left multiplication by the singular support leaves the adjoint left singular columns
unchanged. -/
theorem support_mul_leftSingularColumns_adjoint (A : Matrix O I ℂ) :
    singularSupport A * (leftSingularColumns A)ᴴ = (leftSingularColumns A)ᴴ := by
  have he := congrArg Matrix.conjTranspose (leftSingularColumns_mul_support A)
  simpa only [Matrix.conjTranspose_mul, singularSupport_adjoint] using! he

/-- The singular-value diagonal multiplied by its reciprocal diagonal equals the singular
support. -/
private theorem singular_diagonal_mul_inv (A : Matrix O I ℂ) :
    diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)⁻¹) =
        singularSupport A := by
  classical
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : matrixSingularValues A i = 0
  · rw [if_pos hi, hi, Complex.ofReal_zero, zero_mul]
  · have hc : (matrixSingularValues A i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi
    simp only [if_neg hi, mul_inv_cancel₀ hc]

/-- The reciprocal singular-value diagonal multiplied by the singular-value diagonal equals the
singular support. -/
private theorem inv_singular_diagonal_mul (A : Matrix O I ℂ) :
    diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)⁻¹) *
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) =
        singularSupport A := by
  rw [Matrix.diagonal_mul_diagonal]
  simpa only [Matrix.diagonal_mul_diagonal, mul_comm] using! singular_diagonal_mul_inv A

/-- The product of `A` with its pseudoinverse equals the left singular columns times their
conjugate transpose. -/
theorem mul_matrixPseudoinverse (A : Matrix O I ℂ) :
    A * matrixPseudoinverse A = leftSingularColumns A * (leftSingularColumns A)ᴴ := by
  rw [matrixPseudoinverse_eq, ← Matrix.mul_assoc A, ← Matrix.mul_assoc A,
    mul_rightSingularBasis_columns, Matrix.mul_assoc (leftSingularColumns A),
    singular_diagonal_mul_inv, leftSingularColumns_mul_support]

/-- The product of the pseudoinverse with `A` is the singular support conjugated by the right
singular basis. -/
theorem matrixPseudoinverse_mul (A : Matrix O I ℂ) :
    matrixPseudoinverse A * A = basisColumns (rightSingularBasis A) * singularSupport A *
      (basisColumns (rightSingularBasis A))ᴴ := by
  have ha : (leftSingularColumns A)ᴴ * A =
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
        (basisColumns (rightSingularBasis A))ᴴ := by
    have hf : A = leftSingularColumns A *
        diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
        (basisColumns (rightSingularBasis A))ᴴ := (oddSingularTransform_id A).symm
    have hd : singularSupport A *
        diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) =
          diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) := by
      classical
      rw [singularSupport, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : matrixSingularValues A i = 0
      · rw [if_pos hi, hi, Complex.ofReal_zero, mul_zero]
      · rw [if_neg hi, one_mul]
    calc
      (leftSingularColumns A)ᴴ * A = (leftSingularColumns A)ᴴ *
          (leftSingularColumns A *
            diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
              (basisColumns (rightSingularBasis A))ᴴ) :=
        congrArg (fun M => (leftSingularColumns A)ᴴ * M) hf
      _ = singularSupport A *
          diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
            (basisColumns (rightSingularBasis A))ᴴ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, leftSingularColumns_gram]
        rfl
      _ = _ := congrArg (fun M => M * (basisColumns (rightSingularBasis A))ᴴ) hd
  rw [matrixPseudoinverse_eq, Matrix.mul_assoc _ _ A, ha,
    ← Matrix.mul_assoc, Matrix.mul_assoc (basisColumns (rightSingularBasis A)),
    inv_singular_diagonal_mul]

/-- The pseudoinverse satisfies `A * matrixPseudoinverse A * A = A`. -/
theorem mul_matrixPseudoinverse_mul (A : Matrix O I ℂ) :
    A * matrixPseudoinverse A * A = A := by
  rw [Matrix.mul_assoc A, matrixPseudoinverse_mul, ← Matrix.mul_assoc A,
    ← Matrix.mul_assoc A, mul_rightSingularBasis_columns]
  have hd : diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
      singularSupport A = diagonal (fun i : Fin (Fintype.card I) =>
        (matrixSingularValues A i : ℂ)) := by
    classical
    rw [singularSupport, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : matrixSingularValues A i = 0
    · rw [if_pos hi, hi, Complex.ofReal_zero, zero_mul]
    · rw [if_neg hi, mul_one]
  rw [Matrix.mul_assoc (leftSingularColumns A), hd]
  exact oddSingularTransform_id A

/-- The pseudoinverse satisfies `matrixPseudoinverse A * A * matrixPseudoinverse A =
matrixPseudoinverse A`. -/
theorem matrixPseudoinverse_mul_self (A : Matrix O I ℂ) :
    matrixPseudoinverse A * A * matrixPseudoinverse A = matrixPseudoinverse A := by
  rw [Matrix.mul_assoc, mul_matrixPseudoinverse, matrixPseudoinverse_eq,
    ← Matrix.mul_assoc, Matrix.mul_assoc _ (leftSingularColumns A)ᴴ,
    leftSingularColumns_gram]
  change (basisColumns (rightSingularBasis A) *
    diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)⁻¹) *
      singularSupport A) * (leftSingularColumns A)ᴴ = _
  rw [Matrix.mul_assoc _ (singularSupport A), support_mul_leftSingularColumns_adjoint]

/-- The product of `A` with its pseudoinverse is Hermitian. -/
theorem mul_matrixPseudoinverse_adjoint (A : Matrix O I ℂ) :
    (A * matrixPseudoinverse A)ᴴ = A * matrixPseudoinverse A := by
  rw [mul_matrixPseudoinverse]
  simp

/-- The product of the pseudoinverse with `A` is Hermitian. -/
theorem matrixPseudoinverse_mul_adjoint (A : Matrix O I ℂ) :
    (matrixPseudoinverse A * A)ᴴ = matrixPseudoinverse A * A := by
  rw [matrixPseudoinverse_mul]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    singularSupport_adjoint, Matrix.mul_assoc]

/-- The pseudoinverse of the zero matrix is zero. -/
theorem matrixPseudoinverse_zero : matrixPseudoinverse (0 : Matrix O I ℂ) = 0 := by
  simp [matrixPseudoinverse, oddSingularTransform_zero]

/-- Any matrix satisfying the two Moore–Penrose product identities and the two Hermitian product
conditions equals `matrixPseudoinverse A`. -/
theorem matrixPseudoinverse_unique (A : Matrix O I ℂ) (B : Matrix I O ℂ)
    (hABA : A * B * A = A) (hBAB : B * A * B = B)
    (hAB : (A * B)ᴴ = A * B) (hBA : (B * A)ᴴ = B * A) :
    B = matrixPseudoinverse A := by
  have hrow : B * A = matrixPseudoinverse A * A := by
    have h₁ : (B * A) * (matrixPseudoinverse A * A) = B * A := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, mul_matrixPseudoinverse_mul]
    have h₂ : (matrixPseudoinverse A * A) * (B * A) = matrixPseudoinverse A * A := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hABA]
    have ht := congrArg Matrix.conjTranspose h₂
    rw [Matrix.conjTranspose_mul, hBA, matrixPseudoinverse_mul_adjoint] at ht
    exact h₁.symm.trans ht
  have hcol : A * B = A * matrixPseudoinverse A := by
    have h₁ : (A * B) * (A * matrixPseudoinverse A) = A * matrixPseudoinverse A := by
      rw [← Matrix.mul_assoc, hABA]
    have h₂ : (A * matrixPseudoinverse A) * (A * B) = A * B := by
      rw [← Matrix.mul_assoc, mul_matrixPseudoinverse_mul]
    have ht := congrArg Matrix.conjTranspose h₁
    rw [Matrix.conjTranspose_mul, hAB, mul_matrixPseudoinverse_adjoint] at ht
    exact h₂.symm.trans ht
  calc
    B = B * A * B := hBAB.symm
    _ = matrixPseudoinverse A * A * B := congrArg (fun M => M * B) hrow
    _ = matrixPseudoinverse A * (A * B) := Matrix.mul_assoc _ _ _
    _ = matrixPseudoinverse A * (A * matrixPseudoinverse A) := congrArg _ hcol
    _ = matrixPseudoinverse A := by rw [← Matrix.mul_assoc, matrixPseudoinverse_mul_self]

/-- The pseudoinverse of an isometry is its conjugate transpose. -/
theorem matrixPseudoinverse_of_isometry {A : Matrix O I ℂ} (hA : IsIsometry A) :
    matrixPseudoinverse A = Aᴴ := by
  have h : Aᴴ * A = 1 := hA
  apply Eq.symm
  apply matrixPseudoinverse_unique A Aᴴ
  · rw [Matrix.mul_assoc, h, Matrix.mul_one]
  · rw [h, Matrix.one_mul]
  · simp
  · simp

/-- If `A * Aᴴ = 1`, the pseudoinverse of `A` is its conjugate transpose. -/
theorem matrixPseudoinverse_of_coisometry [DecidableEq O]
    {A : Matrix O I ℂ} (hA : A * Aᴴ = 1) : matrixPseudoinverse A = Aᴴ := by
  apply Eq.symm
  apply matrixPseudoinverse_unique A Aᴴ
  · rw [hA, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hA, Matrix.mul_one]
  · simp
  · simp

/-- The products of a matrix and its pseudoinverse in either order are orthogonal projectors. -/
theorem matrixPseudoinverse_projectors (A : Matrix O I ℂ) :
    IsOrthogonalProjector (A * matrixPseudoinverse A) ∧
      IsOrthogonalProjector (matrixPseudoinverse A * A) := by
  constructor
  · exact ⟨by
      change (A * matrixPseudoinverse A) * (A * matrixPseudoinverse A) = _
      rw [← Matrix.mul_assoc, mul_matrixPseudoinverse_mul],
      mul_matrixPseudoinverse_adjoint A⟩
  · exact ⟨by
      change (matrixPseudoinverse A * A) * (matrixPseudoinverse A * A) = _
      rw [← Matrix.mul_assoc, matrixPseudoinverse_mul_self],
      matrixPseudoinverse_mul_adjoint A⟩

/-- An orthogonal projector has operator norm at most one. -/
theorem orthogonalProjector_spectralNorm_le_one {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : IsOrthogonalProjector P) : ‖P‖ ≤ 1 := by
  have hn := Matrix.l2_opNorm_conjTranspose_mul_self P
  have hs : Pᴴ = P := hP.2
  have hid : P * P = P := hP.1
  rw [hs, hid] at hn
  nlinarith [norm_nonneg P]

/-- The normal-equation condition `Aᴴ * (A * x - b) = 0` for a matrix right-hand side. -/
def IsNormalSolution {K : Type*} (A : Matrix O I ℂ) (b : Matrix O K ℂ)
    (x : Matrix I K ℂ) : Prop := Aᴴ * (A * x - b) = 0

/-- The pseudoinverse applied to `b` satisfies the normal equation. -/
theorem matrixPseudoinverse_normal {K : Type*} (A : Matrix O I ℂ) (b : Matrix O K ℂ) :
    IsNormalSolution A b (matrixPseudoinverse A * b) := by
  have he : Aᴴ * (A * matrixPseudoinverse A) = Aᴴ := by
    calc
      Aᴴ * (A * matrixPseudoinverse A) = (A * matrixPseudoinverse A * A)ᴴ := by
        rw [Matrix.conjTranspose_mul, mul_matrixPseudoinverse_adjoint]
      _ = Aᴴ := congrArg Matrix.conjTranspose (mul_matrixPseudoinverse_mul A)
  unfold IsNormalSolution
  rw [Matrix.mul_sub, ← Matrix.mul_assoc A, ← Matrix.mul_assoc Aᴴ, he, sub_self]

/-- Projecting any normal solution by `matrixPseudoinverse A * A` gives `matrixPseudoinverse A *
b`. -/
theorem normalSolution_project {K : Type*} (A : Matrix O I ℂ) (b : Matrix O K ℂ)
    {y : Matrix I K ℂ} (hy : IsNormalSolution A b y) :
    matrixPseudoinverse A * A * y = matrixPseudoinverse A * b := by
  have he : matrixPseudoinverse A * (matrixPseudoinverse A)ᴴ * Aᴴ =
      matrixPseudoinverse A := by
    rw [Matrix.mul_assoc, ← Matrix.conjTranspose_mul, mul_matrixPseudoinverse_adjoint,
      ← Matrix.mul_assoc, matrixPseudoinverse_mul_self]
  have hz := congrArg (fun M : Matrix I K ℂ =>
    (matrixPseudoinverse A * (matrixPseudoinverse A)ᴴ) * M) hy
  change (matrixPseudoinverse A * (matrixPseudoinverse A)ᴴ) * (Aᴴ * (A * y - b)) = _ at hz

  rw [← Matrix.mul_assoc, he, Matrix.mul_zero, Matrix.mul_sub, ← Matrix.mul_assoc,
    sub_eq_zero] at hz
  exact hz

/-- The pseudoinverse normal solution has operator norm at most that of every other normal
solution. -/
theorem matrixPseudoinverse_minimumNorm_normal {K : Type*} [Fintype K] [DecidableEq K]
    (A : Matrix O I ℂ) (b : Matrix O K ℂ) {y : Matrix I K ℂ}
    (hy : IsNormalSolution A b y) : ‖matrixPseudoinverse A * b‖ ≤ ‖y‖ := by
  rw [← normalSolution_project A b hy]
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul_of_nonneg_right
      (orthogonalProjector_spectralNorm_le_one (matrixPseudoinverse_projectors A).2)
      (norm_nonneg y)).trans_eq (one_mul _))

/-- If `A * y = b` has a solution, applying the pseudoinverse to `b` also solves it. -/
theorem matrixPseudoinverse_solves {K : Type*} (A : Matrix O I ℂ) (b : Matrix O K ℂ)
    (hb : ∃ y : Matrix I K ℂ, A * y = b) : A * (matrixPseudoinverse A * b) = b := by
  obtain ⟨y, rfl⟩ := hb
  simp only [← Matrix.mul_assoc, mul_matrixPseudoinverse_mul]

/-- The condition that `x` solves `A * x = b` and has operator norm no greater than any other
solution. -/
def IsMinimumNormSolution {K : Type*} [Fintype K] [DecidableEq K] (A : Matrix O I ℂ)
    (b : Matrix O K ℂ) (x : Matrix I K ℂ) : Prop :=
  A * x = b ∧ ∀ y : Matrix I K ℂ, A * y = b → ‖x‖ ≤ ‖y‖

/-- For a solvable matrix equation, the pseudoinverse applied to the right-hand side is a
minimum operator norm solution. -/
theorem matrixPseudoinverse_minimumNorm_solution {K : Type*} [Fintype K] [DecidableEq K]
    (A : Matrix O I ℂ) (b : Matrix O K ℂ) (hb : ∃ y : Matrix I K ℂ, A * y = b) :
    IsMinimumNormSolution A b (matrixPseudoinverse A * b) := by
  refine ⟨matrixPseudoinverse_solves A b hb, ?_⟩
  intro y hy
  exact matrixPseudoinverse_minimumNorm_normal A b (by simp [IsNormalSolution, hy])

end Algebra
end Qatlib.Concepts.CoherentSim.CoherentOAA

namespace Qatlib.Concepts.CoherentSim.CoherentOAA.Encoding
open Matrix
open scoped Matrix.Norms.L2Operator

end Qatlib.Concepts.CoherentSim.CoherentOAA.Encoding

namespace Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

section Approximation
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

omit [DecidableEq O] in

/-- Multiplying the scalar response function by a complex scalar scales its odd singular
transform by that scalar. -/
theorem oddSingularTransform_smul (A : Matrix O I ℂ) (c : ℂ) (f : ℝ → ℂ) :
    oddSingularTransform A (fun x => c * f x) = c • oddSingularTransform A f := by
  unfold oddSingularTransform
  have hd : diagonal (fun i : Fin (Fintype.card I) => c * f (matrixSingularValues A i)) =
      c • diagonal (fun i : Fin (Fintype.card I) => f (matrixSingularValues A i)) := by
    rw [← Matrix.diagonal_smul]
    rfl
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq O] in

/-- For real `c`, the adjoint of the singular transform with response `c / x` is `c` times the
pseudoinverse. -/
theorem inverseTransform_adjoint (A : Matrix O I ℂ) (c : ℝ) :
    (oddSingularTransform A (fun x => (c : ℂ) / (x : ℂ)))ᴴ =
      (c : ℂ) • matrixPseudoinverse A := by
  simp only [div_eq_mul_inv, oddSingularTransform_smul, Matrix.conjTranspose_smul,
    RCLike.star_def, Complex.conj_ofReal, matrixPseudoinverse]

/-- If every positive singular value is at least a positive `δ`, the pseudoinverse has operator
norm at most `δ⁻¹`. -/
theorem matrixPseudoinverse_norm_le {A : Matrix O I ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      δ ≤ matrixSingularValues A i) : ‖matrixPseudoinverse A‖ ≤ δ⁻¹ := by
  rw [matrixPseudoinverse, Matrix.l2_opNorm_conjTranspose]
  apply oddSingularTransform_norm_le_positive A _ (inv_nonneg.mpr hδ.le)
  intro i hi
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hi.le]
  exact inv_anti₀ hδ (hgap i hi)

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- An odd response approximating `c / x` at every positive singular value yields, after taking
the circuit adjoint, a scale-one block encoding of `c` times the pseudoinverse. -/
theorem qsvt_pseudoinverse_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) -
        (c : ℂ) / (matrixSingularValues A i : ℂ)‖ ≤ ε) :
    BlockEncoding ((c : ℂ) • matrixPseudoinverse A)
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs)ᴴ R L 1 ε := by
  have he := Qatlib.Concepts.BlockEncoding.Encoding.BlockEncoding.adjoint
    (qsvt_odd_positive_approximation h hb zs hzs hodd
      (fun x => (c : ℂ) / (x : ℂ)) hε happrox)
  simpa only [inverseTransform_adjoint] using! he

/-- An odd reciprocal response approximation yields a circuit encoding `c` times the
pseudoinverse with `zs.length` queries and `zs.length + 1` fixed gates. -/
theorem qsvt_pseudoinverse_counted_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) -
        (c : ℂ) / (matrixSingularValues A i : ℂ)‖ ≤ ε) :
    ∃ cs : List (AdjointStep H),
      BlockEncoding ((c : ℂ) • matrixPseudoinverse A) (evaluate U cs) R L 1 ε ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨adjointCircuit (compileQSVT (rangeProjector R) (rangeProjector L) base zs), ?_, ?_, ?_⟩
  · rw [evaluate_adjointCircuit, evaluate_compileQSVT]
    exact qsvt_pseudoinverse_approximation h hb zs hzs hodd c hε happrox
  · simp only [adjointQueryCount_adjointCircuit, queryCount_compileQSVT]
  · simp only [adjointGateCount_adjointCircuit, gateCount_compileQSVT]
end Approximation
end Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
