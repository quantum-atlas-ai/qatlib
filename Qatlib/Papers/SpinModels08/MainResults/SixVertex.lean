/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.VertexModel.EightVertex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Six-vertex gates and encoded amplitude identities

This module gives explicit Pauli, exchange, and swap matrices together with six-vertex weights
whose associated two-site gates are unitary. It constructs a singlet preparation map and proves
change-of-state and partition-contraction identities used in the six-vertex correspondence of
[VanDenNestEtAl2009].

## Main statements

* `Hex_eq_two_swap_sub_one`: the exchange matrix is twice the swap minus the identity.
* `sixVertexWeight_unitary`: the trigonometric six-vertex gate satisfies the unitary identity.
* `eq9_prep_specialization`: singlet amplitudes can be rewritten using `prepGate`.
* `sixVertex_amplitude_eq_partition`: six-vertex circuit matrix elements equal partition
  contractions.

## References

* [Van den Nest et al., 2009][VanDenNestEtAl2009]
-/

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.SixVertex

open Qatlib.Papers.SpinModels08.MainResults
open Qatlib.Papers.SpinModels08.MainResults.VertexModel

/-- The Pauli X matrix. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Y matrix. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli Z matrix. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The tensor product of two single-qubit matrices, indexed by pairs of binary indices. -/
def tensor2 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun (i, j) (k, l) => A i k * B j l

/-- A tensor-product entry is the product of the corresponding entries of its two factors. -/
theorem tensor2_apply (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j k l : Fin 2) :
    tensor2 A B (i, j) (k, l) = A i k * B j l := rfl

/-- The exchange matrix `X ⊗ X + Y ⊗ Y + Z ⊗ Z`. -/
def Hex : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tensor2 sigmaX sigmaX + tensor2 sigmaY sigmaY + tensor2 sigmaZ sigmaZ

/-- The two-qubit matrix that swaps the two spin indices. -/
def swapGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun (i, j) (k, l) => if i = l ∧ j = k then 1 else 0

/-- The swap matrix has entry one exactly when the input and output spin pairs are reversed. -/
theorem swapGate_apply (i j k l : Fin 2) :
    swapGate (i, j) (k, l) = if i = l ∧ j = k then 1 else 0 := rfl

/-- The exchange matrix equals the sum of two swap matrices minus the identity. -/
theorem Hex_eq_swap_add_swap_sub_one : Hex = swapGate + swapGate - 1 := by
  ext x y
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Hex, tensor2, sigmaX, sigmaY, sigmaZ, swapGate, Matrix.add_apply,
      Matrix.sub_apply, Complex.I_mul_I]

/-- The exchange matrix equals twice the swap matrix minus the identity. -/
theorem Hex_eq_two_swap_sub_one : Hex = (2 : ℂ) • swapGate - 1 := by
  rw [show (2 : ℂ) • swapGate = swapGate + swapGate from two_smul ℂ swapGate]
  exact Hex_eq_swap_add_swap_sub_one

/-- The six-vertex weights with equal-spin phase `exp (2 * t * I)` and mixed-spin cosine and
sine entries. -/
def sixVertexWeight (t : ℝ) : QWeight 2
  | 0, 0, 0, 0 => Complex.exp (2 * (t : ℂ) * Complex.I)
  | 0, 1, 0, 1 => (Real.cos (2 * t) : ℂ)
  | 0, 1, 1, 0 => Complex.I * (Real.sin (2 * t) : ℂ)
  | 1, 0, 0, 1 => Complex.I * (Real.sin (2 * t) : ℂ)
  | 1, 0, 1, 0 => (Real.cos (2 * t) : ℂ)
  | 1, 1, 1, 1 => Complex.exp (2 * (t : ℂ) * Complex.I)
  | _, _, _, _ => 0

/-- The `0000` six-vertex weight is `exp (2 * t * I)`. -/
theorem sixVertexWeight_0000 (t : ℝ) :
    sixVertexWeight t 0 0 0 0 = Complex.exp (2 * (t : ℂ) * Complex.I) := rfl

/-- The `1111` six-vertex weight is `exp (2 * t * I)`. -/
theorem sixVertexWeight_1111 (t : ℝ) :
    sixVertexWeight t 1 1 1 1 = Complex.exp (2 * (t : ℂ) * Complex.I) := rfl

/-- The `0101` six-vertex weight is `cos (2 * t)`. -/
theorem sixVertexWeight_0101 (t : ℝ) :
    sixVertexWeight t 0 1 0 1 = (Real.cos (2 * t) : ℂ) := rfl

/-- The `1010` six-vertex weight is `cos (2 * t)`. -/
theorem sixVertexWeight_1010 (t : ℝ) :
    sixVertexWeight t 1 0 1 0 = (Real.cos (2 * t) : ℂ) := rfl

/-- The `0110` six-vertex weight is `I * sin (2 * t)`. -/
theorem sixVertexWeight_0110 (t : ℝ) :
    sixVertexWeight t 0 1 1 0 = Complex.I * (Real.sin (2 * t) : ℂ) := rfl

/-- The `1001` six-vertex weight is `I * sin (2 * t)`. -/
theorem sixVertexWeight_1001 (t : ℝ) :
    sixVertexWeight t 1 0 0 1 = Complex.I * (Real.sin (2 * t) : ℂ) := rfl

/-- The trigonometric weights have the six-vertex support pattern. -/
theorem sixVertexWeight_shape (t : ℝ) : IsSixVertexShape (sixVertexWeight t) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp [sixVertexWeight]

/-- The equal-spin phase has real part `cos (2 * t)` and imaginary part `sin (2 * t)`. -/
theorem sixVertexWeight_phase (t : ℝ) :
    Complex.exp (2 * (t : ℂ) * Complex.I) =
      (Real.cos (2 * t) : ℂ) + (Real.sin (2 * t) : ℂ) * Complex.I := by
  have h : (2 : ℂ) * (t : ℂ) * Complex.I = ((2 * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I]

/-- The real part of the complex cosine at `2 * t` equals the real cosine. -/
theorem cos2_re (t : ℝ) : (Complex.cos ((2 : ℂ) * (t : ℂ))).re = Real.cos (2 * t) := by
  rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.cos_ofReal_re]

/-- The complex cosine at the real argument `2 * t` has zero imaginary part. -/
theorem cos2_im (t : ℝ) : (Complex.cos ((2 : ℂ) * (t : ℂ))).im = 0 := by
  rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.cos_ofReal_im]

/-- The real part of the complex sine at `2 * t` equals the real sine. -/
theorem sin2_re (t : ℝ) : (Complex.sin ((2 : ℂ) * (t : ℂ))).re = Real.sin (2 * t) := by
  rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.sin_ofReal_re]

/-- The complex sine at the real argument `2 * t` has zero imaginary part. -/
theorem sin2_im (t : ℝ) : (Complex.sin ((2 : ℂ) * (t : ℂ))).im = 0 := by
  rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.sin_ofReal_im]

/-- The two-site matrix associated with `sixVertexWeight t` satisfies `Uᴴ * U = 1`
[VanDenNestEtAl2009]. -/
theorem sixVertexWeight_unitary (t : ℝ) :
    IsUnitary (twoLocalGate (sixVertexWeight t)) := by
  rw [IsUnitary]
  ext x y
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    rw [Complex.ext_iff] <;> constructor <;>
    simp [twoLocalGate, sixVertexWeight, Matrix.one_apply, sixVertexWeight_phase,
      cos2_re, cos2_im, sin2_re, sin2_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im] <;>
    nlinarith [Real.cos_sq_add_sin_sq (2 * t)]

/-- The six-vertex encoding weights with a normalized signed mixed-spin block and unit
equal-spin entries. -/
def encodingWeight : QWeight 2
  | 0, 0, 0, 0 => 1
  | 1, 1, 1, 1 => 1
  | 0, 1, 0, 1 => ((Real.sqrt 2)⁻¹ : ℂ)
  | 1, 0, 1, 0 => ((Real.sqrt 2)⁻¹ : ℂ)
  | 0, 1, 1, 0 => ((Real.sqrt 2)⁻¹ : ℂ)
  | 1, 0, 0, 1 => -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  | _, _, _, _ => 0

/-- The `0000` encoding weight equals one. -/
theorem encodingWeight_0000 : encodingWeight 0 0 0 0 = 1 := rfl

/-- The `1111` encoding weight equals one. -/
theorem encodingWeight_1111 : encodingWeight 1 1 1 1 = 1 := rfl

/-- The `0101` encoding weight equals the reciprocal of `sqrt 2`. -/
theorem encodingWeight_0101 : encodingWeight 0 1 0 1 = ((Real.sqrt 2)⁻¹ : ℂ) := rfl

/-- The `1010` encoding weight equals the reciprocal of `sqrt 2`. -/
theorem encodingWeight_1010 : encodingWeight 1 0 1 0 = ((Real.sqrt 2)⁻¹ : ℂ) := rfl

/-- The `0110` encoding weight equals the reciprocal of `sqrt 2`. -/
theorem encodingWeight_0110 : encodingWeight 0 1 1 0 = ((Real.sqrt 2)⁻¹ : ℂ) := rfl

/-- The `1001` encoding weight equals minus the reciprocal of `sqrt 2`. -/
theorem encodingWeight_1001 : encodingWeight 1 0 0 1 = -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := rfl

/-- The encoding weights have the six-vertex support pattern. -/
theorem encodingWeight_shape : IsSixVertexShape encodingWeight := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp [encodingWeight]

/-- The two-site preparation matrix associated with `encodingWeight`. -/
def prepGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  twoLocalGate encodingWeight

/-- The entries of the preparation matrix are the encoding weights. -/
theorem prepGate_apply (i j k l : Fin 2) :
    prepGate (i, j) (k, l) = encodingWeight i j k l := rfl

/-- The computational basis vector supported at the spin pair `(a, b)`. -/
def basisPair (a b : Fin 2) : Fin 2 × Fin 2 → ℂ := fun x => if x = (a, b) then 1 else 0

/-- The normalized antisymmetric vector `( |01⟩ - |10⟩ ) / sqrt 2`. -/
def singlet : Fin 2 × Fin 2 → ℂ := fun (k, l) =>
  if k = 0 ∧ l = 1 then ((Real.sqrt 2)⁻¹ : ℂ)
  else if k = 1 ∧ l = 0 then -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

/-- The preparation matrix maps the computational basis vector `|01⟩` to the singlet. -/
theorem prepGate_mulVec_01 : prepGate.mulVec (basisPair 0 1) = singlet := by
  funext x
  obtain ⟨k, l⟩ := x
  fin_cases k <;> fin_cases l <;>
    simp [prepGate, twoLocalGate, encodingWeight, basisPair, singlet, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The complex inner product obtained by conjugating the first vector and summing coordinate
products. -/
def dot {ι : Type*} [Fintype ι] (a b : ι → ℂ) : ℂ := ∑ i, star (a i) * b i

/-- The defined inner product equals the dot product with the conjugated first vector. -/
theorem dot_eq_dotProduct {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    dot a b = star a ⬝ᵥ b := rfl

/-- Moving a matrix from the first argument of the inner product to the second replaces it by
its conjugate transpose. -/
theorem dot_mulVec {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (v w : ι → ℂ) :
    dot (U.mulVec v) w = dot v (Uᴴ.mulVec w) := by
  rw [dot_eq_dotProduct, dot_eq_dotProduct, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

/-- The expectation in the vector `U v` equals the expectation of `Uᴴ * C * U` in `v`. -/
theorem amplitude_conj {ι : Type*} [Fintype ι] (U C : Matrix ι ι ℂ) (v : ι → ℂ) :
    dot (U.mulVec v) (C.mulVec (U.mulVec v)) = dot v ((Uᴴ * C * U).mulVec v) := by
  rw [dot_mulVec U v (C.mulVec (U.mulVec v))]
  congr 1
  simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- If `V` maps `w` to `v`, the expectation of `C` in `v` equals the expectation of `Vᴴ * C * V`
in `w`. -/
theorem eq9_amplitude_rewrite {ι : Type*} [Fintype ι]
    (V C : Matrix ι ι ℂ) (w v : ι → ℂ) (h : V.mulVec w = v) :
    dot v (C.mulVec v) = dot w ((Vᴴ * C * V).mulVec w) := by
  rw [← h]
  exact amplitude_conj V C w

/-- The singlet expectation of `C` equals the `|01⟩` expectation of the conjugated matrix
`prepGateᴴ * C * prepGate`. -/
theorem eq9_prep_specialization (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    dot singlet (C.mulVec singlet) =
      dot (basisPair 0 1) ((prepGateᴴ * C * prepGate).mulVec (basisPair 0 1)) := by
  rw [← prepGate_mulVec_01]
  exact amplitude_conj prepGate C (basisPair 0 1)

/-- The binary configuration alternating zero and one, starting with zero. -/
def staggeredConfig (N : ℕ) : Config 2 N := fun r => if r.val % 2 = 0 then 0 else 1

/-- The six-vertex circuit matrix element equals its vertex-model partition contraction
[VanDenNestEtAl2009]. -/
theorem sixVertex_amplitude_eq_partition {N M : ℕ} (t : Fin M → Fin N → ℝ)
    (L R : Config 2 N) :
    matElem (vmCircuit M (fun c r => sixVertexWeight (t c r))) L R =
      vmPartition M (fun c r => sixVertexWeight (t c r)) L R :=
  matElem_vmCircuit_eq_vmPartition M _ L R

/-- The six-vertex circuit matrix element with staggered boundary configurations equals the
corresponding partition contraction. -/
theorem sixVertex_staggered_amplitude_eq_partition {N M : ℕ} (t : Fin M → Fin N → ℝ) :
    matElem (vmCircuit M (fun c r => sixVertexWeight (t c r)))
        (staggeredConfig N) (staggeredConfig N) =
      vmPartition M (fun c r => sixVertexWeight (t c r))
        (staggeredConfig N) (staggeredConfig N) :=
  sixVertex_amplitude_eq_partition t _ _

/-- The property that every partition contraction built from the specified six-vertex weights
has a matrix-element representation. -/
def SixVertexAmplitudeForm : Prop :=
  ∀ (N M : ℕ) (t : Fin M → Fin N → ℝ) (L R : Config 2 N),
    ∃ (C : Matrix (Config 2 N) (Config 2 N) ℂ), matElem C L R =
      vmPartition M (fun c r => sixVertexWeight (t c r)) L R

/-- Every partition contraction built from the specified six-vertex weights has the
representation required by `SixVertexAmplitudeForm` [VanDenNestEtAl2009]. -/
theorem sixVertex_amplitude_form : SixVertexAmplitudeForm := by
  intro N M t L R
  exact ⟨vmCircuit M (fun c r => sixVertexWeight (t c r)),
    sixVertex_amplitude_eq_partition t L R⟩

end Qatlib.Papers.SpinModels08.MainResults.SixVertex
