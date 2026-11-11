/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegularLS22.MainResults.BlockEncodingCore
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# QRegularLS22 — rectangular padding and spectral targets

Fixed paper version: arXiv:2206.13143v2 (accepted in Quantum 2023-04-19).

The paper's data matrices `A, L ∈ R^{N×d}` are rectangular, while the block-
encoding model `IsEnc` of `BlockEncodingCore` is stated for square targets.  The
paper itself embeds rectangular operators into square ones when composing
encodings (Lemma 22: `[[A,0],[B,0]]`; Theorem 32: `A_L = [[A,0],[√λL,0]]`).
This module fixes that convention once:

* `padOp A = [[0,A],[0,0]]` is the square padding of `A : Matrix N d ℂ` into
  `Matrix (N ⊕ d) (N ⊕ d)`; on vectors supported on the `d`-summand it acts as
  `b ↦ A b`;
* `HasSVD A P Q σ` records the singular value decomposition `A = P · diag σ · Qᴴ`
  with `P, Q` unitary and `σ ≥ 0` (existence is the standard SVD; it is taken as
  data, as the frozen library does not package SVD of complex matrices);
* `svPower P Q σ c` is the spectral power `A^{-c} = Q · diag (σ^{-c}) · Pᴴ`,
  used for Theorems 26, 27, 28, 30 and Lemma 41 (`c = 1`, `c = 1/2`);
* `zeroFlagVec`/`oneFlagVec` embed a data register into the flagged `2N`-space
  used by the singular-value-discrimination operator of Theorem 24.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QRegularLS22.MainResults

open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection

/-- Square padding of a rectangular matrix, `[[0, A], [0, 0]]` with rows
`N ⊕ d` and columns `N ⊕ d` (the paper's convention in Lemma 22/Theorem 32:
only the corner that touches the data register is used). -/
noncomputable def padOp {N d : Type*} (A : Matrix N d ℂ) : Matrix (N ⊕ d) (N ⊕ d) ℂ :=
  Matrix.fromBlocks 0 A 0 0

/-- Singular value data of a square matrix: `A = P · diag σ · Qᴴ` with `P, Q`
unitary and real nonnegative singular values `σ`. -/
def HasSVD {I : Type*} [Fintype I] [DecidableEq I]
    (A P Q : Matrix I I ℂ) (σ : I → ℝ) : Prop :=
  P ∈ Matrix.unitaryGroup I ℂ ∧ Q ∈ Matrix.unitaryGroup I ℂ ∧
    (∀ i, 0 ≤ σ i) ∧ A = P * Matrix.diagonal (fun i => (σ i : ℂ)) * Qᴴ

/-- The spectral power `A^{-c}` read off from the singular value data: with
`A = P · diag σ · Qᴴ`, the paper's `A^{-c}` is `Q · diag (σ^{-c}) · Pᴴ`. -/
noncomputable def svPower {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : Matrix I I ℂ) (σ : I → ℝ) (c : ℝ) : Matrix I I ℂ :=
  Q * Matrix.diagonal (fun i => (((σ i) ^ (-c) : ℝ) : ℂ)) * Pᴴ

/-- Flag `0` embedding `v ↦ |0⟩|v⟩` (Theorem 24's `|0⟩|v_j⟩`). -/
def zeroFlagVec {I : Type*} (v : QState I) : QState (Fin 2 × I) :=
  fun x => if x.1 = 0 then v x.2 else 0

/-- Flag `1` embedding `v ↦ |1⟩|v⟩` (Theorem 24's `|1⟩|v_j⟩`). -/
def oneFlagVec {I : Type*} (v : QState I) : QState (Fin 2 × I) :=
  fun x => if x.1 = 1 then v x.2 else 0

end Qatlib.Papers.QRegularLS22.MainResults
