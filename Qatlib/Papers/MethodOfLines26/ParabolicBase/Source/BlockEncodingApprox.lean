/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.BlockEncoding
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
public import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberBridge

@[expose] public section

/-!
# Approximate tensor-product block encodings (Lemma 23)

[arXiv:2606.03407](https://arxiv.org/abs/2606.03407)

[LiangLiu2026], Lemma 23 (Appendix D, PDF p.63) tensors two approximate
block encodings into one for the tensor product of the encoded operators, at
the product scale and with an error ledger accumulated from the two factors.

The abstract predicate
`Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.IsApproxBlockEncoding`
controls only the distinguished corner of a unitary, so it carries no bound on
the operator norm of the encoded matrix. Consequently the ledger
`α₂ε₁ + α₁ε₂ + ε₁ε₂` stated in the paper is not implied by that predicate
alone. The scale-free bound `ε₁ + ε₂ + ε₁ε₂` proved below holds for every
positive scale, and it yields the paper's ledger once `1 ≤ α₁` and `1 ≤ α₂`;
that normalized form is `lemma23_tensor_block_encoding_approx_of_one_le_scales`.
The failure without the normalization is genuine: for one-dimensional factors
with unit corners, encoded operators `0.45`, scales `α₁ = α₂ = 1/2` and errors
`ε₁ = ε₂ = 0.1`, both hypotheses hold with equality while the tensor corner
differs from the encoded tensor operator by `0.19`, which exceeds the claimed
ledger `0.11`.

## Main statements

* `blockCorner_norm_le_one`: a corner of a unitary is a contraction.
* `lemma23_tensor_block_encoding_approx`: the reindexed tensor product of two
  approximate block encodings is one for the tensor product, at scale
  `α₁α₂`, with error `ε₁ + ε₂ + ε₁ε₂`.
* `lemma23_tensor_block_encoding_approx_of_one_le_scales`: the paper's ledger
  `α₂ε₁ + α₁ε₂ + ε₁ε₂` under the normalization `1 ≤ α₁`, `1 ≤ α₂`.

The ancilla count `m₁ + m₂` is a resource parameter and is not part of the
predicate; it is recorded in the docstrings of the paper's statements.
-/

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

open Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.ReferenceError.RefTraceError

/-- The corner of a unitary matrix is a contraction: fixing the ancilla label on both sides is a
compression through an isometry, and a unitary has operator norm at most one. -/
theorem blockCorner_norm_le_one {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] {U : Matrix (J × I) (J × I) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (J × I) ℂ) (j₀ : J) :
    ‖BlockCorner U j₀‖ ≤ 1 := by
  rw [← compress_encodingFiber_blockCorner j₀ U]
  exact (compress_norm_le (encodingFiber_isIsometry j₀) (encodingFiber_isIsometry j₀) U).trans
    (unitary_norm_le_one hU)

/-- Scaling both factors of a tensor gate scales the tensor gate by the product of the scalars. -/
theorem tensorGate_smul_smul {I J : Type*} (c d : ℂ) (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    TensorGate (c • A) (d • B) = (c * d) • TensorGate A B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [TensorGate, Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Lemma 23, approximate form** ([LiangLiu2026], Appendix D, PDF p.63).
For approximate block encodings `U ∈ (α₁, m₁, ε₁)BE(A)` and
`V ∈ (α₂, m₂, ε₂)BE(B)`, the reindexed tensor product `U ⊗ V` is an
approximate block encoding of `A ⊗ B` at scale `α₁α₂` with error
`ε₁ + ε₂ + ε₁ε₂`.

The error term is scale free: it bounds the tensor corner at every positive
scale, and it implies the paper's ledger `α₂ε₁ + α₁ε₂ + ε₁ε₂` once
`1 ≤ α₁` and `1 ≤ α₂` (see `lemma23_tensor_block_encoding_approx_of_one_le_scales`).
The ancilla register of the result is the product of the two ancilla
registers, so the ancilla count is `m₁ + m₂`. -/
theorem lemma23_tensor_block_encoding_approx
    {J I K L : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    {U : Matrix (J × I) (J × I) ℂ} {j₀ : J} {A : Matrix I I ℂ} {α₁ ε₁ : ℝ}
    (hU : IsApproxBlockEncoding U j₀ A α₁ ε₁)
    {V : Matrix (K × L) (K × L) ℂ} {k₀ : K} {B : Matrix L L ℂ} {α₂ ε₂ : ℝ}
    (hV : IsApproxBlockEncoding V k₀ B α₂ ε₂) :
    IsApproxBlockEncoding
      (Matrix.reindex tensorBlockEquiv tensorBlockEquiv (TensorGate U V))
      (j₀, k₀) (TensorGate A B) (α₁ * α₂) (ε₁ + ε₂ + ε₁ * ε₂) := by
  obtain ⟨hUu, hα₁, hUerr⟩ := hU
  obtain ⟨hVu, hα₂, hVerr⟩ := hV
  refine ⟨unitaryGroup_reindex _ (tensorGate_unitary hUu hVu), mul_pos hα₁ hα₂, ?_⟩
  set C₁ : Matrix I I ℂ := BlockCorner U j₀ with hC₁
  set C₂ : Matrix L L ℂ := BlockCorner V k₀ with hC₂
  set A' : Matrix I I ℂ := ((α₁⁻¹ : ℝ) : ℂ) • A with hA'
  set B' : Matrix L L ℂ := ((α₂⁻¹ : ℝ) : ℂ) • B with hB'
  have herr₁ : ‖C₁ - A'‖ ≤ ε₁ := by
    rw [hC₁, hA']
    exact hUerr
  have herr₂ : ‖C₂ - B'‖ ≤ ε₂ := by
    rw [hC₂, hB']
    exact hVerr
  have hC₁le : ‖C₁‖ ≤ 1 := by
    rw [hC₁]
    exact blockCorner_norm_le_one hUu j₀
  have hC₂le : ‖C₂‖ ≤ 1 := by
    rw [hC₂]
    exact blockCorner_norm_le_one hVu k₀
  have hcorner : BlockCorner
      (Matrix.reindex tensorBlockEquiv tensorBlockEquiv (TensorGate U V)) (j₀, k₀)
      = TensorGate C₁ C₂ := by
    rw [blockCorner_reindex_tensorGate, ← hC₁, ← hC₂]
  have hscale : TensorGate A' B' = (((α₁ * α₂)⁻¹ : ℝ) : ℂ) • TensorGate A B := by
    rw [hA', hB']
    have hcast : (((α₁ * α₂)⁻¹ : ℝ) : ℂ) =
        ((α₁⁻¹ : ℝ) : ℂ) * ((α₂⁻¹ : ℝ) : ℂ) := by
      rw [mul_inv]
      push_cast
      ring
    rw [hcast]
    exact tensorGate_smul_smul _ _ _ _
  rw [hcorner, ← hscale]
  have hε₁ : 0 ≤ ε₁ := le_trans (norm_nonneg _) herr₁
  have hε₂ : 0 ≤ ε₂ := le_trans (norm_nonneg _) herr₂
  have hA'norm : ‖A'‖ ≤ 1 + ε₁ := by
    have h : A' = (A' - C₁) + C₁ := by abel
    calc ‖A'‖ = ‖(A' - C₁) + C₁‖ := congrArg norm h
      _ ≤ ‖A' - C₁‖ + ‖C₁‖ := norm_add_le _ _
      _ = ‖C₁ - A'‖ + ‖C₁‖ := by rw [norm_sub_rev]
      _ ≤ ε₁ + 1 := add_le_add herr₁ hC₁le
      _ = 1 + ε₁ := by ring
  have h₁ : ‖C₁ - A'‖ * ‖C₂‖ ≤ ε₁ * 1 :=
    mul_le_mul herr₁ hC₂le (norm_nonneg _) hε₁
  have h₂ : ‖A'‖ * ‖C₂ - B'‖ ≤ (1 + ε₁) * ε₂ :=
    mul_le_mul hA'norm herr₂ (norm_nonneg _) (by linarith)
  calc ‖TensorGate C₁ C₂ - TensorGate A' B'‖
      ≤ ‖C₁ - A'‖ * ‖C₂‖ + ‖A'‖ * ‖C₂ - B'‖ :=
        l2_kronecker_two_factor_error C₁ A' C₂ B'
    _ ≤ ε₁ + ε₂ + ε₁ * ε₂ := by nlinarith [h₁, h₂]

/-- **Lemma 23 with the paper's ledger** ([LiangLiu2026], Appendix D, PDF
p.63), under the block-encoding normalization `1 ≤ α₁` and `1 ≤ α₂` used
throughout the paper's cost statements. The error
`α₂ε₁ + α₁ε₂ + ε₁ε₂` is the ledger printed in the paper; it is deduced from
the scale-free bound `ε₁ + ε₂ + ε₁ε₂` of
`lemma23_tensor_block_encoding_approx`. -/
theorem lemma23_tensor_block_encoding_approx_of_one_le_scales
    {J I K L : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    {U : Matrix (J × I) (J × I) ℂ} {j₀ : J} {A : Matrix I I ℂ} {α₁ ε₁ : ℝ}
    (hU : IsApproxBlockEncoding U j₀ A α₁ ε₁)
    {V : Matrix (K × L) (K × L) ℂ} {k₀ : K} {B : Matrix L L ℂ} {α₂ ε₂ : ℝ}
    (hV : IsApproxBlockEncoding V k₀ B α₂ ε₂)
    (hα₁ : 1 ≤ α₁) (hα₂ : 1 ≤ α₂) :
    IsApproxBlockEncoding
      (Matrix.reindex tensorBlockEquiv tensorBlockEquiv (TensorGate U V))
      (j₀, k₀) (TensorGate A B) (α₁ * α₂) (α₂ * ε₁ + α₁ * ε₂ + ε₁ * ε₂) := by
  obtain ⟨hu, hpos, herr⟩ := lemma23_tensor_block_encoding_approx hU hV
  have hε₁ : 0 ≤ ε₁ := le_trans (norm_nonneg _) hU.2.2
  have hε₂ : 0 ≤ ε₂ := le_trans (norm_nonneg _) hV.2.2
  have h₁ : ε₁ ≤ α₂ * ε₁ := by
    simpa using mul_le_mul_of_nonneg_right hα₂ hε₁
  have h₂ : ε₂ ≤ α₁ * ε₂ := by
    simpa using mul_le_mul_of_nonneg_right hα₁ hε₂
  refine ⟨hu, hpos, herr.trans ?_⟩
  linarith

end Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
