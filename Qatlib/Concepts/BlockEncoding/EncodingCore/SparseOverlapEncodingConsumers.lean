/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding

/-!
# Gram matrices and success mass of sparse overlap encodings

The overlap frames for a matrix with bounded row and column norm sums also describe its scaled
Gram matrix. `sparse_overlap_same_frame_gram_and_success` identifies both the compressed Gram
expression and the squared norm of the postselected vector.

The mathematical background is described in [GilyenSuLowWiebe2019].

## Main statements

* `sparse_overlap_same_frame_gram_and_success`: Gram compression and output norm formulas.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.BlockEncoding.EncodingCore
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Under positive row and column norm-sum bound `s`, the overlap frames satisfy `Rᴴ * (L * Lᴴ)
* R = (s²)⁻¹ • (Aᴴ * A)`, and their overlap output has squared norm `‖Aψ‖² / s²`. See
[GilyenSuLowWiebe2019]. -/
theorem sparse_overlap_same_frame_gram_and_success :
    ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A : Matrix O I ℂ) (s : ℝ) (ψ : I → ℂ), 0 < s →
      (∀ o, (∑ i, ‖A o i‖) ≤ s) → (∀ i, (∑ o, ‖A o i‖) ≤ s) →
      let L := sparseOverlapLeft A s
      let R := sparseOverlapRight A s
      Rᴴ * (L * Lᴴ) * R = (s ^ 2 : ℂ)⁻¹ • (Aᴴ * A) ∧
      ‖toEuclidean_fromVec ((Lᴴ * R).mulVec ψ)‖ ^ 2 =
        ‖toEuclidean_fromVec (A.mulVec ψ)‖ ^ 2 / s ^ 2 := by
  intro I O _ _ _ _ A s ψ hs hr hc
  obtain ⟨_, _, hcorner⟩ := sparse_overlap_actual_frames_and_corner I O A s hs hr hc
  (try dsimp only)
  have hcompressed : compress (sparseOverlapLeft A s) 1 (sparseOverlapRight A s) =
      (s : ℂ)⁻¹ • A := by simpa [compress] using hcorner
  have hadjoint : (sparseOverlapRight A s)ᴴ * sparseOverlapLeft A s =
      star ((s : ℂ)⁻¹) • Aᴴ := by
    have h := congrArg Matrix.conjTranspose hcompressed
    rw [compress_adjoint] at h
    simpa [compress] using h
  have hscalar : star ((s : ℂ)⁻¹) * (s : ℂ)⁻¹ = (s ^ 2 : ℂ)⁻¹ := by
    simp [pow_two, _root_.mul_inv_rev]
  constructor
  · calc
      _ = ((sparseOverlapRight A s)ᴴ * sparseOverlapLeft A s) *
          ((sparseOverlapLeft A s)ᴴ * sparseOverlapRight A s) := by
        simp only [Matrix.mul_assoc]
      _ = (s ^ 2 : ℂ)⁻¹ • (Aᴴ * A) := by
        rw [hadjoint, hcorner, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul, hscalar]
  · rw [hcorner, Matrix.smul_mulVec]
    have hvec : toEuclidean_fromVec ((s : ℂ)⁻¹ • A.mulVec ψ) =
        (s : ℂ)⁻¹ • toEuclidean_fromVec (A.mulVec ψ) := rfl
    rw [hvec, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rw [mul_pow, inv_pow, inv_mul_eq_div]

end Qatlib.Concepts.BlockEncoding.EncodingCore
