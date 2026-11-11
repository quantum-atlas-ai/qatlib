/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QEigenProc24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# QEigenProc24 — block encodings

Fixed source: arXiv:2401.06240v3, Section 2.1 (block encodings) and Appendix D.

The paper writes `O_A` for a block encoding of `A/α_A`: a unitary `B` on the system register
together with an ancilla register such that `⟨0|B|0⟩ = A/α_A` exactly, and `Ĥ`-accuracy
block encodings such as Eq. (230) satisfy `‖⟨0|B|0⟩ - M‖ ≤ ε` (paper's `ε` is an error in the
L2 operator norm).  This module records that vocabulary so that the transformation,
integral and Fourier-coefficient claims can quantify over the encoded unitary.

Reused FQN: the same notion is available in Frozen as
`QuantumAlgorithm.Papers.QSingValue19.BlockEncoding.BlockEncoding`; the paper-level statement
here only needs the top-left block, so we keep the local, minimal definition.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.QEigenProc24.MainResults.BlockEncoding

open Qatlib.Papers.QEigenProc24.MainResults

/-- A unitary on `n` basis states: `B B† = B† B = 1`. -/
def IsUnitary {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) : Prop :=
  B * Bᴴ = 1 ∧ Bᴴ * B = 1

/-- An operator on the system register together with an `a`-dimensional ancilla register. -/
abbrev BlockOp (d a : ℕ) : Type := Matrix (Fin d ⊕ Fin a) (Fin d ⊕ Fin a) ℂ

/-- The system block `⟨0| B |0⟩` of a block encoding. -/
def topLeft {d a : ℕ} (B : BlockOp d a) : Op d := fun i j => B (Sum.inl i) (Sum.inl j)

/-- `B` block encodes `M` with accuracy `δ`: it is a unitary whose system block is within
`δ` (L2 operator norm) of `M` (Section 2.1 of the paper). -/
def BlockEncodes {d a : ℕ} (B : BlockOp d a) (M : Op d) (δ : ℝ) : Prop :=
  IsUnitary B ∧ ‖topLeft B - M‖ ≤ δ

/-- A block encoding of `M` to accuracy `δ` produced by a circuit making `queries` queries to
controlled-`O_A` (and its inverse).  This bundles the encoded unitary with the query count of
the construction, as in the "using O(·) queries" clauses of Theorems 5, 6 and Lemma 21. -/
structure CostedBlockEncoding (d a : ℕ) (M : Op d) (δ : ℝ) where
  B : BlockOp d a
  encodes : BlockEncodes B M δ
  queries : ℕ

/-- A block encoding built from value oracles (absolute value / argument), with the register
sizes and resource counts displayed in Lemma 21 (p. 61) and Theorem 6 (p. 66): the input
register size `inRegisters`, the value-register sizes `absRegisters`, `argRegisters`, the
numbers of queries to the two oracles, and the two-qubit gate count. -/
structure OracleBlockEncodingCost (d a : ℕ) (M : Op d) (δ : ℝ) where
  B : BlockOp d a
  encodes : BlockEncodes B M δ
  inRegisters : ℕ
  absRegisters : ℕ
  argRegisters : ℕ
  absQueries : ℕ
  argQueries : ℕ
  twoQubitGates : ℕ

end Qatlib.Papers.QEigenProc24.MainResults.BlockEncoding
