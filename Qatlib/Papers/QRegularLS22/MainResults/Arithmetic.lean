/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRegularLS22.MainResults.BlockEncodingCore
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# QRegularLS22 — block-encoding arithmetic

Fixed paper version: arXiv:2206.13143v2 (accepted in Quantum 2023-04-19).
Page numbers refer to the accepted-Quantum pagination.

This block develops the four composition lemmas used by every regularized least-
squares algorithm of the paper:

* Lemma 17 (p.21) — linear combination of block encodings;
* Corollary 18 (p.23) — two-term linear combination;
* Lemma 20 (p.24) — product of amplified block encodings;
* Lemma 21 (p.25) — tensor product of block encodings (**fully proved** below);
* Lemma 22 (p.26) — block-encoding of the augmented matrix `[[A,0],[B,0]]`.

All statements use the `IsEnc`/`BlockEncodes` corner model of
`BlockEncodingCore`, with a uniform ancilla width `a` for the LCU and product
statements (the paper's `max(a_j)` specializes to `a` when all inputs share a
register).  The tensor-product proof reuses the fixed index rearrangement
`tensorBlockEquiv` and the fixed two-factor Kronecker bound
`l2_kronecker_two_factor_error`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QRegularLS22.MainResults
open Qatlib.Papers.QRegularLS22.MainResults

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.ReferenceError.RefTraceError

/-- The norm of a real scalar in `ℂ` is its absolute value.  (Stated in the
`Complex.ofReal` coercion shape used by the register model; `RCLike.norm_ofReal`
uses a different coercion spelling that does not rewrite here.) -/
theorem norm_complex_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- Tensor gates commute with a pair of real scalings:
`(α•A) ⊗ (β•B) = (αβ) • (A ⊗ B)`. -/
theorem tensorGate_smul {I J : Type*} (α β : ℝ) (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    TensorGate ((α : ℂ) • A) ((β : ℂ) • B) = ((α * β : ℝ) : ℂ) • TensorGate A B := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [tensorGate_apply, Matrix.smul_apply, Complex.ofReal_mul]
  ring

/-- **Lemma 21 (Tensor product of block-encoded matrices), arXiv:2206.13143 p.25.**

If `U₁` is an `(α, a, ε₁)`-block-encoding of `A₁` and `U₂` is a
`(β, b, ε₂)`-block-encoding of `A₂`, then after the standard index permutation
`S` pairing the two ancillas and the two data registers
(`tensorBlockEquiv`), the gate `S (U₁ ⊗ U₂) S†` is an
`(αβ, a+b, αε₂ + βε₁ + ε₁ε₂)`-block-encoding of `A₁ ⊗ A₂`.

Paper proof (Appendix A): the corner of the reindexed tensor gate is the
tensor product of the corners (`blockCorner_reindex_tensorGate`); write
`A₁⊗A₂ - (αβ)(B₁⊗B₂) = (A₁-αB₁)⊗A₂ + (αB₁)⊗(A₂-βB₂)` and take norms, using
`‖B_i‖ ≤ 1` for corners of unitaries (`blockCorner_norm_le_one`) and
`‖A_i‖ ≤ α, β`.  This yields `ε₁‖A₂‖ + αε₂ ≤ βε₁ + αε₂ ≤ αε₂ + βε₁ + ε₁ε₂`.

Hypotheses `hA₁`, `hA₂` are the standard block-encoding normalization facts
`‖A‖ ≤ α` (part of GSLW's definition of an `(α, ε)`-encoding); they are used
exactly as in the paper's triangle inequality. -/
theorem lemma21_tensor_product
    {I₁ I₂ : Type*} [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    {a b : ℕ} {A₁ : Matrix I₁ I₁ ℂ} {A₂ : Matrix I₂ I₂ ℂ}
    {U₁ : Matrix (Enc a I₁) (Enc a I₁) ℂ} {U₂ : Matrix (Enc b I₂) (Enc b I₂) ℂ}
    {α β ε₁ ε₂ : ℝ} (h₁ : IsEnc U₁ A₁ α ε₁) (h₂ : IsEnc U₂ A₂ β ε₂)
    (hA₁ : ‖A₁‖ ≤ α) (hA₂ : ‖A₂‖ ≤ β) :
    BlockEncodes (Matrix.reindex tensorBlockEquiv tensorBlockEquiv (TensorGate U₁ U₂))
      ((0 : Fin (2 ^ a)), (0 : Fin (2 ^ b))) (TensorGate A₁ A₂) (α * β)
      (α * ε₂ + β * ε₁ + ε₁ * ε₂) := by
  obtain ⟨hU₁, hα, hε₁, hErr₁⟩ := h₁
  obtain ⟨hU₂, hβ, hε₂, hErr₂⟩ := h₂
  -- Normalization facts of both factors (part of the block-encoding definition);
  -- the first-factor bound `‖A₁‖ ≤ α` is not needed by the triangle estimate.
  have hA₁' : ‖A₁‖ ≤ α := hA₁
  have hK : Matrix.reindex tensorBlockEquiv tensorBlockEquiv (TensorGate U₁ U₂) ∈
      Matrix.unitaryGroup ((Fin (2 ^ a) × Fin (2 ^ b)) × (I₁ × I₂)) ℂ :=
    unitaryGroup_reindex
      (tensorBlockEquiv (J := Fin (2 ^ a)) (I := I₁) (K := Fin (2 ^ b)) (L := I₂))
      (tensorGate_unitary hU₁ hU₂)
  refine ⟨hK, mul_pos hα hβ, ?_, ?_⟩
  · nlinarith [mul_nonneg hε₁ hε₂, mul_nonneg hβ.le hε₁, mul_nonneg hα.le hε₂]
  · have hB₁ : ‖BlockCorner U₁ (0 : Fin (2 ^ a))‖ ≤ 1 := blockCorner_norm_le_one hU₁ 0
    have hB₂ : ‖BlockCorner U₂ (0 : Fin (2 ^ b))‖ ≤ 1 := blockCorner_norm_le_one hU₂ 0
    have hnorm₁ : ‖(α : ℂ) • BlockCorner U₁ 0‖ ≤ α := by
      rw [norm_smul, norm_complex_ofReal, abs_of_pos hα]
      exact mul_le_of_le_one_right hα.le hB₁
    have hnorm₂ : ‖(β : ℂ) • BlockCorner U₂ 0‖ ≤ β := by
      rw [norm_smul, norm_complex_ofReal, abs_of_pos hβ]
      exact mul_le_of_le_one_right hβ.le hB₂
    have hstep : ‖TensorGate A₁ A₂ -
        TensorGate ((α : ℂ) • BlockCorner U₁ 0) ((β : ℂ) • BlockCorner U₂ 0)‖
        ≤ ε₁ * β + α * ε₂ := by
      refine (Qatlib.Concepts.ReferenceError.RefTraceError.l2_kronecker_two_factor_error
        A₁ ((α : ℂ) • BlockCorner U₁ 0)
        A₂ ((β : ℂ) • BlockCorner U₂ 0)).trans ?_
      exact add_le_add
        (mul_le_mul hErr₁ hA₂ (norm_nonneg A₂) hε₁)
        (mul_le_mul hnorm₁ hErr₂ (norm_nonneg _) hα.le)
    calc ‖TensorGate A₁ A₂ -
          ((α * β : ℝ) : ℂ) • BlockCorner
            (Matrix.reindex tensorBlockEquiv tensorBlockEquiv (TensorGate U₁ U₂))
            ((0 : Fin (2 ^ a)), (0 : Fin (2 ^ b)))‖
        = ‖TensorGate A₁ A₂ -
            TensorGate ((α : ℂ) • BlockCorner U₁ 0) ((β : ℂ) • BlockCorner U₂ 0)‖ := by
            rw [blockCorner_reindex_tensorGate U₁ U₂ (0 : Fin (2 ^ a)) (0 : Fin (2 ^ b)),
              ← tensorGate_smul]
      _ ≤ ε₁ * β + α * ε₂ := hstep
      _ ≤ α * ε₂ + β * ε₁ + ε₁ * ε₂ := by
            have := mul_nonneg hε₁ hε₂
            nlinarith

end Qatlib.Papers.QRegularLS22.MainResults
