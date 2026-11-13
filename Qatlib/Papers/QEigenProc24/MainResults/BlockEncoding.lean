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

The legacy resource records below have independent counters. Only the explicit
word implementation predicates connect those counters to evaluated operations.
The conditional transfer theorem assumes a supplied primitive interpretation and
an encoding proof; it does not construct the paper's quantum algorithms.

Reused FQN: the same notion is available in the existing library as
`Qatlib.Papers.QSingValue19.BlockEncoding.BlockEncoding`; the paper-level statement
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

/-- A block encoding with an unverified query annotation. The encoding proof is genuine,
but the counter alone gives no implementation guarantee; use `ImplementsCosted`. -/
structure CostedBlockEncoding (d a : ℕ) (M : Op d) (δ : ℝ) where
  B : BlockOp d a
  encodes : BlockEncodes B M δ
  queries : ℕ

/-- A block encoding with unverified register and resource annotations, retained for
compatibility. `ImplementsOracleCost` certifies word evaluation and operation counts;
neither record by itself certifies the register layout or circuit synthesis. -/
structure OracleBlockEncodingCost (d a : ℕ) (M : Op d) (δ : ℝ) where
  B : BlockOp d a
  encodes : BlockEncodes B M δ
  inRegisters : ℕ
  absRegisters : ℕ
  argRegisters : ℕ
  absQueries : ℕ
  argQueries : ℕ
  twoQubitGates : ℕ

/-- Primitive kinds. Inverse calls have the same kind and cost as forward calls. -/
inductive EncodingStepKind where
  | controlled | absolute | argument | gate
  deriving DecidableEq

/-- A named primitive in a supplied catalog; `inverse` selects its adjoint. -/
structure EncodingStep where
  kind : EncodingStepKind
  label : ℕ
  inverse : Bool

/-- Count occurrences of a primitive kind, including inverse calls. -/
def encodingCount (k : EncodingStepKind) (w : List EncodingStep) : ℕ :=
  (w.filter (fun s => s.kind = k)).length

/-- Evaluate a word in a fixed primitive catalog. Gate entries must be supplied as
two-qubit implementations by the caller; locality is not certified by this matrix model. -/
def encodingEval {d a : ℕ} (primitive : EncodingStepKind → ℕ → BlockOp d a)
    (w : List EncodingStep) : BlockOp d a :=
  w.foldr (fun s B => (if s.inverse then (primitive s.kind s.label)ᴴ
    else primitive s.kind s.label) * B) 1

/-- Explicit controlled-oracle word contract. Other oracle kinds are forbidden.
The primitive catalog and its physical implementation are hypotheses. -/
def ImplementsCosted {d a : ℕ} {M : Op d} {δ : ℝ}
    (primitive : EncodingStepKind → ℕ → BlockOp d a)
    (C : CostedBlockEncoding d a M δ) (w : List EncodingStep) : Prop :=
  C.B = encodingEval primitive w ∧
  C.queries = encodingCount .controlled w ∧
  encodingCount .absolute w = 0 ∧ encodingCount .argument w = 0 ∧
  ∀ s ∈ w, IsUnitary (primitive s.kind s.label)

/-- Value-oracle word contract, excluding controlled-oracle calls. Register annotations
are not certified. The supplied catalog must independently implement the named primitives. -/
def ImplementsOracleCost {d a : ℕ} {M : Op d} {δ : ℝ}
    (primitive : EncodingStepKind → ℕ → BlockOp d a)
    (C : OracleBlockEncodingCost d a M δ) (w : List EncodingStep) : Prop :=
  C.B = encodingEval primitive w ∧
  C.absQueries = encodingCount .absolute w ∧
  C.argQueries = encodingCount .argument w ∧
  C.twoQubitGates = encodingCount .gate w ∧ encodingCount .controlled w = 0 ∧
  ∀ s ∈ w, IsUnitary (primitive s.kind s.label)

/-- Conditional transfer of the existing encoding proof to the supplied word,
with its exact controlled-oracle count. No word is synthesized here. -/
theorem encoding_of_implementation {d a : ℕ} {M : Op d} {δ : ℝ}
    {primitive : EncodingStepKind → ℕ → BlockOp d a}
    {C : CostedBlockEncoding d a M δ} {w : List EncodingStep}
    (h : ImplementsCosted primitive C w) :
    BlockEncodes (encodingEval primitive w) M δ ∧
      C.queries = encodingCount .controlled w := by
  exact ⟨h.1 ▸ C.encodes, h.2.1⟩

/-- The empty word evaluates to the identity, independently of the target encoding. -/
theorem encodingEval_nil {d a : ℕ}
    (primitive : EncodingStepKind → ℕ → BlockOp d a) : encodingEval primitive [] = 1 := rfl

/-- Conditional value-oracle accounting for the evaluated encoding. Primitive
interpretation and word implementation are supplied, not synthesized. -/
theorem oracle_encoding_of_implementation {d a : ℕ} {M : Op d} {δ : ℝ}
    {primitive : EncodingStepKind → ℕ → BlockOp d a}
    {C : OracleBlockEncodingCost d a M δ} {w : List EncodingStep}
    (h : ImplementsOracleCost primitive C w) :
    BlockEncodes (encodingEval primitive w) M δ ∧
      C.absQueries = encodingCount .absolute w ∧
      C.argQueries = encodingCount .argument w ∧
      C.twoQubitGates = encodingCount .gate w := by
  exact ⟨h.1 ▸ C.encodes, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Primitive counts add under word concatenation. -/
theorem encodingCount_append (k : EncodingStepKind) (u v : List EncodingStep) :
    encodingCount k (u ++ v) = encodingCount k u + encodingCount k v := by
  simp [encodingCount]

end Qatlib.Papers.QEigenProc24.MainResults.BlockEncoding
