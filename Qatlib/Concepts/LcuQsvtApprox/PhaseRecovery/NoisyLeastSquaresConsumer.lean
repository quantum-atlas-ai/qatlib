/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.ClusterPatterns.WireComposition.PauliMixtureTwirling

/-!
# Concrete noisy least-squares postselection

This module realizes a rectangular rank-one least-squares problem through explicit label
embeddings and a four-dimensional unitary. It computes the pseudoinverse, the inconsistent
right-hand side, the postselection probability and output, and the zero-overlap case.

`lsNoisyU` introduces a unit-modulus phase perturbation and certifies its encoding error and
output guarantee. A second example uses a Hadamard gate to encode the pseudoinverse of a
normalized two-entry column. These examples illustrate the quantum data-fitting setting of
[WiebeBraunLloyd2012].

## Main statements

* `leastSquares_rectangular_consumer_data`: certify the rectangular example and its inconsistent
  input.
* `leastSquares_rectangular_consumer_output`: compute the exact successful output and circuit
  costs.
* `leastSquares_noisy_phase_consumer`: compute the phase-perturbed encoding and output.
* `ridge_actual_output_consumer`: certify the Hadamard-based example.

## References

* [Wiebe et al., 2012][WiebeBraunLloyd2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport

namespace Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery

open Matrix
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

section LabelEmbed

/-- The basis-label embedding matrix associated with the map `f`. -/
def labelEmbed {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (f : I → H) : Matrix H I ℂ := Matrix.of fun h i => if h = f i then 1 else 0

/-- An injective label map defines an isometric label embedding. -/
theorem labelEmbed_isometry {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    {f : I → H} (hf : Function.Injective f) : IsIsometry (labelEmbed f) := by
  ext i j
  show ((labelEmbed f)ᴴ * labelEmbed f) i j = (1 : Matrix I I ℂ) i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, labelEmbed, Matrix.of_apply,
    Matrix.one_apply, RCLike.star_def]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single (f i)]
    · simp
    · intro h _ hne
      simp [hne]
    · simp
  · have hfij : f i ≠ f j := fun e => hij (hf e)
    simp only [if_neg hij]
    apply Finset.sum_eq_zero
    intro h _
    by_cases h1 : h = f i
    · subst h1
      simp [hfij]
    · simp [h1]

/-- Multiplication by `permMatrix σ` composes the label embedding with `σ`. -/
theorem permMatrix_mul_labelEmbed {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (σ : H → H) (g : I → H) :
    permMatrix σ * labelEmbed g = labelEmbed (σ ∘ g) := by
  ext h i
  simp only [Matrix.mul_apply, permMatrix, labelEmbed, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (g i)]
  · by_cases h : h = σ (g i) <;> simp [h]
  · intro h2 _ h2ne
    simp [h2ne]
  · simp

/-- Multiplication by a diagonal matrix weights each embedded label by its diagonal entry. -/
theorem diagonal_mul_labelEmbed {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (d : H → ℂ) (g : I → H) :
    Matrix.diagonal d * labelEmbed g = Matrix.of fun h i => d h * (if h = g i then 1 else 0) := by
  ext h i
  simp [labelEmbed, diagonal_mul]

/-- Compression of a label-map matrix between label embeddings tests whether the output label
equals the transformed input label. -/
theorem compress_labelEmbed_permMatrix {H O I : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (f : O → H) (σ : H → H) (g : I → H) :
    compress (labelEmbed f) (permMatrix σ) (labelEmbed g) =
      Matrix.of fun o i => if f o = σ (g i) then 1 else 0 := by
  rw [compress, Matrix.mul_assoc, permMatrix_mul_labelEmbed σ g]
  ext o i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, labelEmbed, Matrix.of_apply,
    Function.comp_apply, RCLike.star_def]
  rw [Finset.sum_eq_single (f o)]
  · by_cases h : f o = σ (g i) <;> simp [h]
  · intro h1 _ h1ne
    simp [h1ne]
  · simp

/-- Compression of a diagonally weighted label-map matrix gives the matching-label indicator
multiplied by the output diagonal weight. -/
theorem compress_labelEmbed_diagonal_permMatrix {H O I : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (f : O → H) (d : H → ℂ) (σ : H → H) (g : I → H) :
    compress (labelEmbed f) (Matrix.diagonal d * permMatrix σ) (labelEmbed g) =
      Matrix.of fun o i => d (f o) * (if f o = σ (g i) then 1 else 0) := by
  rw [compress, Matrix.mul_assoc, Matrix.mul_assoc (Matrix.diagonal d),
    permMatrix_mul_labelEmbed σ g, diagonal_mul_labelEmbed]
  ext o i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, labelEmbed, Matrix.of_apply,
    Function.comp_apply, RCLike.star_def]
  rw [Finset.sum_eq_single (f o)]
  · by_cases h : f o = σ (g i) <;> simp [h]
  · intro h1 _ h1ne
    simp [h1ne]
  · simp

end LabelEmbed

section LsExample

/-- The `3 × 2` rank-one example matrix with its only nonzero entry equal to one at `(0, 0)`. -/
def lsExampleA : Matrix (Fin 3) (Fin 2) ℂ := !![1, 0; 0, 0; 0, 0]

/-- The embedding of the three output labels into the first three labels of `Fin 4`. -/
def lsExampleL : Matrix (Fin 4) (Fin 3) ℂ := labelEmbed (fun j => ⟨j.val, by omega⟩)

/-- The embedding of the two input labels into the first two labels of `Fin 4`. -/
def lsExampleR : Matrix (Fin 4) (Fin 2) ℂ := labelEmbed (fun j => ⟨j.val, by omega⟩)

/-- The four-dimensional permutation gate swapping labels one and three. -/
def lsExampleU : Operator 4 := permMatrix (Equiv.swap (1 : Fin 4) 3)

/-- The normalized equal superposition of labels zero and one in the three-dimensional output
space. -/
noncomputable def lsExampleB : QState (Fin 3) :=
  fun i => if i = 0 ∨ i = 1 then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- The example unitary preceded by a diagonal factor `ζ` on label zero. -/
noncomputable def lsNoisyU (ζ : ℂ) : Operator 4 :=
  Matrix.diagonal (fun i : Fin 4 => if i = 0 then ζ else 1) * lsExampleU

end LsExample

/-- Computes the conjugate transpose of the rectangular example matrix. -/
theorem lsExampleA_conjTranspose : lsExampleAᴴ = !![1, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lsExampleA, Matrix.conjTranspose_apply]

/-- The product of the example matrix and its conjugate transpose is the projector onto output
label zero. -/
theorem lsExampleA_mul_conjTranspose :
    lsExampleA * lsExampleAᴴ = !![1, 0, 0; 0, 0, 0; 0, 0, 0] := by
  rw [lsExampleA_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lsExampleA, Matrix.mul_apply, Fin.sum_univ_two]

/-- The conjugate-transpose product of the example matrix is the projector onto input label
zero. -/
theorem lsExampleA_conjTranspose_mul : lsExampleAᴴ * lsExampleA = !![1, 0; 0, 0] := by
  rw [lsExampleA_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lsExampleA, Matrix.mul_apply, Fin.sum_univ_three]

/-- The pseudoinverse of the rank-one example matrix equals its conjugate transpose. -/
theorem lsExampleA_pseudoinverse : matrixPseudoinverse lsExampleA = lsExampleAᴴ := by
  apply Eq.symm
  apply matrixPseudoinverse_unique lsExampleA lsExampleAᴴ
  · rw [lsExampleA_mul_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lsExampleA, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [lsExampleA_conjTranspose_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lsExampleA, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two]
  · rw [lsExampleA_mul_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · rw [lsExampleA_conjTranspose_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- The example right-hand side is normalized. -/
theorem lsExampleB_normalized : Normalized lsExampleB := by
  have hbval : ‖(Real.sqrt 2 : ℂ)⁻¹‖^2 = 1/2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
      inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h0 : lsExampleB (0 : Fin 3) = (Real.sqrt 2 : ℂ)⁻¹ := by simp [lsExampleB]
  have h1 : lsExampleB (1 : Fin 3) = (Real.sqrt 2 : ℂ)⁻¹ := by simp [lsExampleB]
  have h2 : lsExampleB (2 : Fin 3) = 0 := by simp [lsExampleB]
  show (∑ i : Fin 3, ‖lsExampleB i‖^2) = 1
  rw [Fin.sum_univ_three, h0, h1, h2, hbval]
  norm_num

/-- The example right-hand side lies outside the range of `lsExampleA`. -/
theorem lsExampleB_inconsistent : ¬ (∃ x : QState (Fin 2), lsExampleA *ᵥ x = lsExampleB) := by
  rintro ⟨x, hx⟩
  have h1 := congrFun hx 1
  have hL : (lsExampleA *ᵥ x) 1 = 0 := by
    simp [lsExampleA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hR : lsExampleB 1 = (Real.sqrt 2 : ℂ)⁻¹ := by simp [lsExampleB]
  rw [hL, hR] at h1
  exact (inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos_of_pos (show (0:ℝ) < 2 by norm_num)).ne')) h1.symm

/-- Certifies the rectangular rank-one example's unitary encoding, isometric frames,
pseudoinverse, normalized right-hand side, and inconsistency. -/
theorem leastSquares_rectangular_consumer_data :
    lsExampleA = !![1,0;0,0;0,0] ∧
    lsExampleU ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧ IsIsometry lsExampleL ∧
    IsIsometry lsExampleR ∧
    ProjectedUnitaryEncoding lsExampleA lsExampleU lsExampleL lsExampleR ∧
    matrixPseudoinverse lsExampleA = lsExampleAᴴ ∧ Normalized lsExampleB ∧
    ¬ (∃ x : QState (Fin 2), lsExampleA *ᵥ x = lsExampleB) := by
  have hU : lsExampleU ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    permMatrix_unitary (fun a => Equiv.swap_apply_self _ _ _)
  have hL : IsIsometry lsExampleL :=
    labelEmbed_isometry (fun a b h => Fin.ext_iff.mpr (by exact congrArg (fun j : Fin 4 => j.val) h))
  have hR : IsIsometry lsExampleR :=
    labelEmbed_isometry (fun a b h => Fin.ext_iff.mpr (by exact congrArg (fun j : Fin 4 => j.val) h))
  have hcomp : compress lsExampleL lsExampleU lsExampleR = lsExampleA := by
    simp only [lsExampleL, lsExampleU, lsExampleR]
    rw [compress_labelEmbed_permMatrix]
    ext o i
    fin_cases o <;> fin_cases i <;>
      simp [lsExampleA, Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left]
  exact ⟨rfl, hU, hL, hR, ⟨hU, hL, hR, hcomp⟩, lsExampleA_pseudoinverse,
    lsExampleB_normalized, lsExampleB_inconsistent⟩

/-- Every computational basis ket is nonzero. -/
theorem ket_ne_zero {I : Type} [Fintype I] [DecidableEq I] (i : I) : Qatlib.Foundations.PureStateMath.Ket i ≠ 0 := by
  intro h
  have hn := normalized_ket i
  rw [h] at hn
  simp [Normalized] at hn

/-- The Euclidean state-vector norm of `c` times a basis ket equals `‖c‖`. -/
theorem stateVector_smul_ket_norm {I : Type} [Fintype I] [DecidableEq I] (c : ℂ) (i : I) :
    ‖stateVector (c • Qatlib.Foundations.PureStateMath.Ket i)‖ = ‖c‖ := by
  rw [show stateVector (c • Qatlib.Foundations.PureStateMath.Ket i) = c • stateVector (Qatlib.Foundations.PureStateMath.Ket i) from rfl, norm_smul,
    show ‖stateVector (Qatlib.Foundations.PureStateMath.Ket i)‖ = 1 from (normalized_iff_stateVector_norm _).mp
      (normalized_ket i), mul_one]

/-- Normalizing a scalar multiple of a basis ket yields the ket multiplied by `‖c‖⁻¹ * c`. -/
theorem postMeasure_smul_ket {I : Type} [Fintype I] [DecidableEq I] (c : ℂ) (i : I) :
    PostMeasure (c • Qatlib.Foundations.PureStateMath.Ket i) Finset.univ = (↑(‖c‖⁻¹) * c) • Qatlib.Foundations.PureStateMath.Ket i := by
  rw [postMeasure_univ_eq_smul, stateVector_smul_ket_norm]
  funext j
  simp only [Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket, smul_eq_mul,
      Complex.real_smul]
  by_cases hj : j = i
  · subst j
    rw [if_pos rfl]
    ring
  · rw [if_neg hj]
    ring

/-- The least-squares vector for the example is `1 / √2` times input ket zero. -/
theorem lsExample_xstar : leastSquaresVector lsExampleA lsExampleB =
    (Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) := by
  funext j
  show (matrixPseudoinverse lsExampleA *ᵥ lsExampleB) j = _
  rw [lsExampleA_pseudoinverse, lsExampleA_conjTranspose]
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, lsExampleB, Qatlib.Foundations.PureStateMath.Ket]

/-- Reversing the example encoding frames compresses the unitary to the conjugate transpose of
`lsExampleA`. -/
theorem lsExample_compress_reverse :
    compress lsExampleR lsExampleU lsExampleL = lsExampleAᴴ := by
  simp only [lsExampleR, lsExampleU, lsExampleL]
  rw [compress_labelEmbed_permMatrix, lsExampleA_conjTranspose]
  ext o i
  fin_cases o <;> fin_cases i <;>
    simp [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left]

/-- The example's reverse-frame postselection vector is `1 / √2` times input ket zero. -/
theorem lsExample_postselectionVector : postselectionVector lsExampleU lsExampleR
    lsExampleL lsExampleB = (Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) := by
  show compress lsExampleR lsExampleU lsExampleL *ᵥ lsExampleB = _
  rw [lsExample_compress_reverse, ← lsExampleA_pseudoinverse]
  exact lsExample_xstar

/-- The least-squares overlap for the example is `1 / √2`. -/
theorem lsExample_overlap : leastSquaresOverlap lsExampleA lsExampleB = (Real.sqrt 2)⁻¹ := by
  have h1 : (lsExampleA * matrixPseudoinverse lsExampleA) *ᵥ lsExampleB =
      lsExampleA *ᵥ ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) := by
    rw [← Matrix.mulVec_mulVec,
      show (matrixPseudoinverse lsExampleA *ᵥ lsExampleB) =
        leastSquaresVector lsExampleA lsExampleB from rfl, lsExample_xstar]
  have hcol : lsExampleA *ᵥ Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) = Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3) := by
    funext i
    fin_cases i <;> simp [lsExampleA, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  show ‖stateVector ((lsExampleA * matrixPseudoinverse lsExampleA) *ᵥ lsExampleB)‖ = _
  rw [h1, Matrix.mulVec_smul, hcol, stateVector_smul_ket_norm, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- Computes the example's least-squares vector, overlap `1 / √2`, success probability `1 / 2`,
normalized output ket zero, and zero-query, one-gate cost. -/
theorem leastSquares_rectangular_consumer_output :
    leastSquaresVector lsExampleA lsExampleB =
      (Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) ∧
    leastSquaresOverlap lsExampleA lsExampleB = (Real.sqrt 2)⁻¹ ∧
    postselectionProbability lsExampleU lsExampleR lsExampleL lsExampleB = 1/2 ∧
    postselectionOutput lsExampleU lsExampleR lsExampleL lsExampleB = some (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) ∧
    IsEuclideanLeastSquares lsExampleA lsExampleB (leastSquaresVector lsExampleA lsExampleB) ∧
    QueryCount ([.gate lsExampleU] : Circuit (Fin 4)) = 0 ∧
    GateCount ([.gate lsExampleU] : Circuit (Fin 4)) = 1 := by
  obtain ⟨-, -, -, hR, -, -, -, -⟩ := leastSquares_rectangular_consumer_data
  refine ⟨lsExample_xstar, lsExample_overlap, ?_, ?_,
    (leastSquares_minimum_residual_and_norm lsExampleA lsExampleB).1, rfl, rfl⟩
  · rw [postselectionProbability_eq_norm_sq hR, lsExample_postselectionVector,
      stateVector_smul_ket_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  · have hne : (Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) ≠ 0 :=
      smul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos_of_pos (show (0:ℝ) < 2 by norm_num)).ne')) (ket_ne_zero 0)
    rw [postselectionOutput, lsExample_postselectionVector,
      conditionalState_eq_some_of_ne_zero hne]
    congr 1
    rw [postMeasure_smul_ket _ 0]
    have hn : ‖(Real.sqrt 2 : ℂ)⁻¹‖ = (Real.sqrt 2)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
    have hs : (↑(‖(Real.sqrt 2 : ℂ)⁻¹‖⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) = 1 := by
      rw [hn, inv_inv]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos_of_pos (show (0:ℝ) < 2 by norm_num)).ne')
    rw [hs, one_smul]

/-- For output ket one, least-squares overlap and postselection probability vanish, and both the
least-squares direction and conditional output are absent. -/
theorem leastSquares_zero_overlap_consumer :
    leastSquaresOverlap lsExampleA (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3)) = 0 ∧
    leastSquaresDirection lsExampleA (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3)) = none ∧
    postselectionProbability lsExampleU lsExampleR lsExampleL (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3)) = 0 ∧
    postselectionOutput lsExampleU lsExampleR lsExampleL (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3)) = none := by
  obtain ⟨-, -, -, hR, -, -, -, -⟩ := leastSquares_rectangular_consumer_data
  have hpsv : postselectionVector lsExampleU lsExampleR lsExampleL (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3)) = 0 := by
    show compress lsExampleR lsExampleU lsExampleL *ᵥ Qatlib.Foundations.PureStateMath.Ket
        (1 : Fin 3) = 0
    rw [lsExample_compress_reverse, lsExampleA_conjTranspose]
    funext j
    fin_cases j <;> simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  have hx : leastSquaresVector lsExampleA (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3)) = 0 := by
    show matrixPseudoinverse lsExampleA *ᵥ Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3) = 0
    rw [lsExampleA_pseudoinverse, lsExampleA_conjTranspose]
    funext j
    fin_cases j <;> simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  refine ⟨(leastSquares_overlap_and_zero lsExampleA (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3))).2.1.mpr hx,
    (leastSquares_direction_spec lsExampleA (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3))).1.mpr hx, ?_, ?_⟩
  · rw [postselectionProbability_eq_norm_sq hR, hpsv]
    simp
  · show ConditionalState (postselectionVector lsExampleU lsExampleR lsExampleL
      (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3))) = none
    rw [hpsv]
    exact conditionalState_zero

/-- For unit-modulus `ζ`, the diagonal phase factor has conjugate-transpose product equal to the
identity. -/
theorem lsNoisyU_diagonal_unitary (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (Matrix.diagonal (fun i : Fin 4 => if i = 0 then ζ else 1))ᴴ *
      Matrix.diagonal (fun i : Fin 4 => if i = 0 then ζ else 1) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    Matrix.one_apply, RCLike.star_def]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, if_pos rfl]
      by_cases hi : i = 0
      · subst i
        rw [if_pos rfl]
        rw [Complex.conj_mul', hζ]
        norm_num
      · rw [if_neg hi]
        simp
    · intro k _ hki
      simp [hki]
    · simp
  · simp only [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i
    · subst k
      simp [hij]
    · simp [hk]

/-- The phase-perturbed example matrix is unitary when `ζ` has unit modulus. -/
theorem lsNoisyU_unitary (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    lsNoisyU ζ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  obtain ⟨-, hU, -, -, -, -, -, -⟩ := leastSquares_rectangular_consumer_data
  have hU' : lsExampleUᴴ * lsExampleU = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [lsNoisyU, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul]
  calc (lsExampleUᴴ * (Matrix.diagonal fun i : Fin 4 => if i = 0 then ζ else 1)ᴴ) *
        (Matrix.diagonal (fun i : Fin 4 => if i = 0 then ζ else 1) * lsExampleU)
      = lsExampleUᴴ * ((Matrix.diagonal fun i : Fin 4 => if i = 0 then ζ else 1)ᴴ *
          Matrix.diagonal (fun i : Fin 4 => if i = 0 then ζ else 1)) * lsExampleU := by
        simp only [Matrix.mul_assoc]
  _ = lsExampleUᴴ * lsExampleU := by rw [lsNoisyU_diagonal_unitary ζ hζ, Matrix.mul_one]
  _ = 1 := hU'

/-- Reverse-frame compression of the phase-perturbed example is `ζ` times the example
pseudoinverse. -/
theorem lsNoisyU_compress (ζ : ℂ) :
    compress lsExampleR (lsNoisyU ζ) lsExampleL = ζ • matrixPseudoinverse lsExampleA := by
  simp only [lsNoisyU, lsExampleR, lsExampleU, lsExampleL]
  rw [compress_labelEmbed_diagonal_permMatrix, lsExampleA_pseudoinverse,
    lsExampleA_conjTranspose]
  ext o i
  fin_cases o <;> fin_cases i <;>
    simp [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left, Matrix.smul_apply, smul_eq_mul]

/-- For unit-modulus `ζ`, certifies encoding error `‖ζ - 1‖`, success probability `1 / 2`,
output `ζ` times ket zero, and the stated least-squares state error under the strict overlap
gap. -/
theorem leastSquares_noisy_phase_consumer :
    ∀ (ζ : ℂ), ‖ζ‖ = 1 →
      BlockEncoding (matrixPseudoinverse lsExampleA) (lsNoisyU ζ) lsExampleR lsExampleL 1
        ‖ζ-1‖ ∧
      postselectionProbability (lsNoisyU ζ) lsExampleR lsExampleL lsExampleB = 1/2 ∧
      postselectionOutput (lsNoisyU ζ) lsExampleR lsExampleL lsExampleB =
        some (ζ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) ∧
      (‖ζ-1‖ < (Real.sqrt 2)⁻¹ → IsLeastSquaresSolutionState lsExampleA lsExampleB
        (ζ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) (2 * ‖ζ-1‖ / (Real.sqrt 2)⁻¹)) := by
  intro ζ hζ
  obtain ⟨-, hU, hL, hR, hPUE, -, hb, -⟩ := leastSquares_rectangular_consumer_data
  have hζne : ζ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hζ
    exact zero_ne_one hζ
  have hAnorm : ‖matrixPseudoinverse lsExampleA‖ ≤ 1 := by
    rw [lsExampleA_pseudoinverse, Matrix.l2_opNorm_conjTranspose, ← hPUE.encoded]
    exact (compress_norm_le hL hR lsExampleU).trans (unitary_norm_le_one hU)
  have hvec : postselectionVector (lsNoisyU ζ) lsExampleR lsExampleL lsExampleB =
      ζ • ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) := by
    show compress lsExampleR (lsNoisyU ζ) lsExampleL *ᵥ lsExampleB = _
    rw [lsNoisyU_compress, Matrix.smul_mulVec,
      show (matrixPseudoinverse lsExampleA *ᵥ lsExampleB) =
        leastSquaresVector lsExampleA lsExampleB from rfl, lsExample_xstar]
  have hne : ζ • ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) ≠ 0 :=
    smul_ne_zero hζne (smul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos_of_pos (show (0:ℝ) < 2 by norm_num)).ne')) (ket_ne_zero 0))
  have hn : ‖(Real.sqrt 2 : ℂ)⁻¹‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos_of_pos (show (0:ℝ) < 2 by norm_num)).ne'
  have hs : (↑(‖ζ * (Real.sqrt 2 : ℂ)⁻¹‖⁻¹) * (ζ * (Real.sqrt 2 : ℂ)⁻¹)) = ζ := by
    rw [Complex.norm_mul, hζ, one_mul, hn, inv_inv]
    calc (↑√2 : ℂ) * (ζ * (↑√2)⁻¹) = ζ * (↑√2 * (↑√2)⁻¹) := by ring
      _ = ζ := by rw [mul_inv_cancel₀ h2, mul_one]
  have hout : postselectionOutput (lsNoisyU ζ) lsExampleR lsExampleL lsExampleB =
      some (ζ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) := by
    rw [postselectionOutput, hvec, conditionalState_eq_some_of_ne_zero hne]
    congr 1
    rw [show ζ • ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) =
        (ζ * (Real.sqrt 2 : ℂ)⁻¹) • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) from by rw [smul_smul],
      postMeasure_smul_ket _ 0, hs]
  refine ⟨?_, ?_, hout, ?_⟩
  · refine ⟨lsNoisyU_unitary ζ hζ, hR, hL, by norm_num, norm_nonneg _, ?_⟩
    rw [lsNoisyU_compress, one_smul]
    have hsub : matrixPseudoinverse lsExampleA - ζ • matrixPseudoinverse lsExampleA =
        (1 - ζ) • matrixPseudoinverse lsExampleA := by
      rw [sub_smul, one_smul]
    rw [hsub, norm_smul]
    calc ‖1 - ζ‖ * ‖matrixPseudoinverse lsExampleA‖ ≤ ‖1 - ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left hAnorm (norm_nonneg _)
      _ = ‖ζ - 1‖ := by rw [mul_one, norm_sub_rev]
  · rw [postselectionProbability_eq_norm_sq hR, hvec]
    have hnorm : ‖stateVector (ζ • ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)))‖ = ‖ζ‖ *
        ‖(Real.sqrt 2 : ℂ)⁻¹‖ := by
      rw [show stateVector (ζ • ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) =
          ζ • stateVector ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) from rfl, norm_smul,
        stateVector_smul_ket_norm]
    rw [hnorm, hζ, one_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  · intro hgap
    have hBE : BlockEncoding ((1:ℂ) • matrixPseudoinverse lsExampleA) (lsNoisyU ζ)
        lsExampleR lsExampleL 1 ‖ζ - 1‖ := by
      refine ⟨lsNoisyU_unitary ζ hζ, hR, hL, by norm_num, norm_nonneg _, ?_⟩
      simp only [lsNoisyU_compress, one_smul]
      have hsub : matrixPseudoinverse lsExampleA - ζ • matrixPseudoinverse lsExampleA =
          (1 - ζ) • matrixPseudoinverse lsExampleA := by
        rw [sub_smul, one_smul]
      rw [hsub, norm_smul]
      calc ‖1 - ζ‖ * ‖matrixPseudoinverse lsExampleA‖ ≤ ‖1 - ζ‖ * 1 :=
          mul_le_mul_of_nonneg_left hAnorm (norm_nonneg _)
        _ = ‖ζ - 1‖ := by rw [mul_one, norm_sub_rev]
    obtain ⟨-, -, φ, hφ, hstate⟩ := leastSquares_actual_postselection lsExampleA lsExampleU
      (lsNoisyU ζ) lsExampleL lsExampleR lsExampleB 1 1 ‖ζ - 1‖ hPUE hBE (by norm_num) hb
      (by rw [one_mul, lsExample_overlap]; exact hgap)
    rw [hout] at hφ
    have hφ' : ζ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) = φ := Option.some.inj hφ
    rw [hφ']
    rwa [one_mul, lsExample_overlap] at hstate

section RidgeExample

/-- Relabeling both indices along an equivalence preserves unitarity. -/
theorem relabelGate_unitary {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    relabelGate e U ∈ Matrix.unitaryGroup J ℂ := by
  have h : Uᴴ * U = 1 := by
    have h' := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h'
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hstar : (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
    ext i j
    simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  have hmul : relabelGate e Uᴴ * relabelGate e U = relabelGate e (Uᴴ * U) := by
    ext i j
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    rw [Equiv.sum_comp e.symm (fun y => Uᴴ (e.symm i) y * U y (e.symm j)),
      ← Matrix.mul_apply]
  rw [hstar, hmul, h]
  ext i j
  simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
    EmbeddingLike.apply_eq_iff_eq]

/-- The normalized `2 × 1` column with both entries equal to `1 / √2`. -/
noncomputable def ridgeExampleA : Matrix (Fin 2) (Fin 1) ℂ := (Real.sqrt 2 : ℂ)⁻¹ • !![1; 1]

/-- The Hadamard gate relabeled from Boolean indices to `Fin 2`. -/
noncomputable def ridgeExampleU : Operator 2 := relabelGate boolEquivFin2 Hadamard

/-- The one-dimensional frame selecting label zero in `Fin 2`. -/
def ridgeExampleR : Matrix (Fin 2) (Fin 1) ℂ := Matrix.of fun i _ => if i = 0 then 1 else 0

/-- The product of two complex copies of `1 / √2` is `1 / 2`. -/
theorem sqrt2_inv_sq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
  rw [← pow_two, inv_pow, sqrt2_sq]
  norm_num

/-- The pseudoinverse of the normalized two-entry column is the row with both entries equal to
`1 / √2`. -/
theorem ridgeExampleA_pseudoinverse :
    matrixPseudoinverse ridgeExampleA = (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1] := by
  apply Eq.symm
  apply matrixPseudoinverse_unique ridgeExampleA ((Real.sqrt 2 : ℂ)⁻¹ • !![1, 1])
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ridgeExampleA, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
        Fin.sum_univ_two] <;>
      linear_combination 2 * (Real.sqrt 2 : ℂ)⁻¹ * sqrt2_inv_sq
  · ext i j
    fin_cases i; fin_cases j <;>
      simp [ridgeExampleA, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] <;>
      linear_combination 2 * sqrt2_inv_sq
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ridgeExampleA, Matrix.mul_apply, Matrix.conjTranspose_apply, smul_eq_mul]
  · ext i j
    fin_cases i; fin_cases j
    simp [ridgeExampleA, Matrix.mul_apply, Matrix.conjTranspose_apply, smul_eq_mul]

/-- The relabeled Hadamard example gate is unitary. -/
theorem ridgeExampleU_unitary : ridgeExampleU ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  relabelGate_unitary boolEquivFin2 hadamard_unitary

/-- The frame selecting label zero is isometric. -/
theorem ridgeExampleR_isometry : IsIsometry ridgeExampleR := by
  show ridgeExampleRᴴ * ridgeExampleR = 1
  ext j j'
  fin_cases j; fin_cases j'
  simp [ridgeExampleR, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Compression of the Hadamard example between the output frame and identity input frame equals
the example pseudoinverse. -/
theorem ridgeExample_compress :
    compress ridgeExampleR ridgeExampleU (1 : Operator 2) =
      matrixPseudoinverse ridgeExampleA := by
  rw [ridgeExampleA_pseudoinverse]
  ext j l
  fin_cases j; fin_cases l <;>
    simp [compress, ridgeExampleR, ridgeExampleU, relabelGate, Hadamard, boolEquivFin2,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- The least-squares vector for the column example and input ket zero is `1 / √2` times the
unique basis ket. -/
theorem ridgeExample_xstar : leastSquaresVector ridgeExampleA (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) =
    (Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 1) := by
  funext j
  fin_cases j
  show (matrixPseudoinverse ridgeExampleA *ᵥ Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) 0 = _
  rw [ridgeExampleA_pseudoinverse]
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul,
      Qatlib.Foundations.PureStateMath.Ket]

/-- The column example's postselection vector is `1 / √2` times the unique basis ket. -/
theorem ridgeExample_postselectionVector :
    postselectionVector ridgeExampleU ridgeExampleR (1 : Operator 2) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) =
      (Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 1) := by
  show compress ridgeExampleR ridgeExampleU
      (1 : Operator 2) *ᵥ Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) = _
  rw [ridgeExample_compress]
  exact ridgeExample_xstar

/-- Certifies the column example's exact pseudoinverse encoding and least-squares vector,
success probability `1 / 2`, normalized output, and zero-query, one-gate cost. -/
theorem ridge_actual_output_consumer :
    leastSquaresVector ridgeExampleA (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) = (Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 1) ∧
    IsEuclideanLeastSquares ridgeExampleA (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 1)) ∧
    BlockEncoding (matrixPseudoinverse ridgeExampleA) ridgeExampleU ridgeExampleR
      (1 : Operator 2) 1 0 ∧
    postselectionProbability ridgeExampleU ridgeExampleR (1 : Operator 2) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) = 1/2 ∧
    postselectionOutput ridgeExampleU ridgeExampleR (1 : Operator 2) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) =
      some (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 1)) ∧
    QueryCount ([.gate ridgeExampleU] : Circuit (Fin 2)) = 0 ∧
    GateCount ([.gate ridgeExampleU] : Circuit (Fin 2)) = 1 := by
  have h1 : (1 : Operator 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    simp
  refine ⟨ridgeExample_xstar, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · have h := (leastSquares_minimum_residual_and_norm ridgeExampleA (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))).1
    rwa [ridgeExample_xstar] at h
  · refine ⟨ridgeExampleU_unitary, ridgeExampleR_isometry, ?_, by norm_num, le_rfl, ?_⟩
    · show (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * 1 = 1
      rw [Matrix.conjTranspose_one, Matrix.mul_one]
    · rw [ridgeExample_compress]
      simp
  · rw [postselectionProbability_eq_norm_sq ridgeExampleR_isometry,
      ridgeExample_postselectionVector, stateVector_smul_ket_norm, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  · have hne : (Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 1) ≠ 0 :=
      smul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos_of_pos (show (0:ℝ) < 2 by norm_num)).ne')) (ket_ne_zero 0)
    rw [postselectionOutput, ridgeExample_postselectionVector,
      conditionalState_eq_some_of_ne_zero hne]
    congr 1
    rw [postMeasure_smul_ket _ 0]
    have hn : ‖(Real.sqrt 2 : ℂ)⁻¹‖ = (Real.sqrt 2)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
    have hs : (↑(‖(Real.sqrt 2 : ℂ)⁻¹‖⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) = 1 := by
      rw [hn, inv_inv]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos_of_pos (show (0:ℝ) < 2 by norm_num)).ne')
    rw [hs, one_smul]

end RidgeExample

end Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
