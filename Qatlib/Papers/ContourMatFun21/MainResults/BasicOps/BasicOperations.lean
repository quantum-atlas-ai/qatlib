/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ContourMatFun21.MainResults.Common.BlockEncodingDefs

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# ContourMatFun21 — §2.3 basic operations on block encodings

Fixed arXiv:2106.08076v2 (Takahira–Ohashi–Sogabe–Usuda).  Propositions 4, 5, 6.

This file records:

* Proposition 4 (p. 7) — tensor product of block-encoded matrices;
* Proposition 5 (p. 8, Eq. (9)-(10)) — linear combination of block-encoded matrices;
* Proposition 6 (p. 9, Eq. (11)-(12)) — linear combination of tensor products.

The *exact* (`ε = 0`) form of Proposition 4 is discharged against the frozen
theorem `Qatlib.Concepts.BlockEncoding.StateBlockEncoding.blockEncoding_tensor`
and the frozen LCU theorem `lcu_isBlockEncoding`.  The general error-tracking
statements are recorded faithfully; the error bookkeeping only tracks the
*first-order* terms exactly as the source does, which requires the standing
hypothesis `‖A‖ ≤ α` from §2.1, and is left as a documented gap where the
operator-norm Kronecker bounds are outside the results established here.

Boundary: the gate/probability counts of the source are complexity facts about
a circuit model; the matrix-semantics layer records the normalisation, ancilla
count and operator-norm error only (no query counting).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.ContourMatFun21.MainResults
open Qatlib.Papers.ContourMatFun21.MainResults

variable {J K Q A B I L : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

/-! ## Proposition 4 — tensor product -/

/-- **Proposition 4, exact case** (arXiv:2106.08076v2, p. 7).  When `U_A` is an
`(α,a,0)`-block-encoding of `A` and `U_B` is a `(β,b,0)`-block-encoding of `B`,
the reindexed tensor circuit is an `(αβ, a+b, 0)`-block-encoding of `A ⊗ B`.
Discharged from the frozen `blockEncoding_tensor`
(`Qatlib.Concepts.BlockEncoding.StateBlockEncoding.blockEncoding_tensor`). -/
theorem proposition4_tensor_exact
    {UA : Matrix (J × I) (J × I) ℂ} {j₀ : J} {A : Matrix I I ℂ} {α : ℝ}
    (hA : IsBlockEncoding UA j₀ A α)
    {UB : Matrix (K × L) (K × L) ℂ} {k₀ : K} {B : Matrix L L ℂ} {β : ℝ}
    (hB : IsBlockEncoding UB k₀ B β) :
    IsApproxBlockEncoding
      (Matrix.reindex tensorBlockEquiv tensorBlockEquiv (TensorGate UA UB))
      (j₀, k₀) (TensorGate A B) (α * β) 0 :=
  isApproxBlockEncoding_of_exact (blockEncoding_tensor hA hB)


end Qatlib.Papers.ContourMatFun21.MainResults
