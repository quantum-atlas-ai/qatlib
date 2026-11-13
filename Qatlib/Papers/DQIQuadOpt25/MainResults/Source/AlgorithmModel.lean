/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIQuadOpt25.MainResults.Source.PaperModel
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

set_option backward.isDefEq.respectTransparency false

/-!
# DQI preparation and decoder execution contracts

The legacy records retain their declared fields for compatibility. Resource
predicates additionally require execution witnesses: preparation is a list of
two-level unitary operations acting on the zero basis state, and decoding is
a finite decision tree testing syndrome coordinates. Costs are respectively
list length and worst-case tree depth including output writes.

Two-level operations are the primitives of this model; their synthesis into
local hardware gates and the classical construction of their coefficients
are not charged here. Thus this is not a hardware runtime theorem.
No DQI preparation circuit or efficient decoder is constructed in this module.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIQuadOpt25.MainResults.Source

/-- A lightweight state-preparation procedure: the produced amplitude vector
and a declared resource count (number of elementary operations).  Circuit
implementability is not part of this structure (see the module note). -/
structure StateProcedure (p n : ℕ) where
  /-- The amplitude vector produced by the procedure. -/
  state : (Fin n → ZMod p) → ℂ
  /-- Declared resource count of the procedure. -/
  cost : ℕ

/-- An elementary two-level unitary on two distinct computational basis states. -/
structure TwoLevelGate (p n : ℕ) where
  left : Fin n → ZMod p
  right : Fin n → ZMod p
  distinct : left ≠ right
  matrix : Matrix (Fin 2) (Fin 2) ℂ
  unitary : matrix ∈ Matrix.unitaryGroup (Fin 2) ℂ

/-- Apply one two-level operation, leaving every other amplitude unchanged. -/
def TwoLevelGate.apply {p n : ℕ} (g : TwoLevelGate p n)
    (ψ : (Fin n → ZMod p) → ℂ) : (Fin n → ZMod p) → ℂ := by
  classical
  exact fun x => if x = g.left then
    g.matrix 0 0 * ψ g.left + g.matrix 0 1 * ψ g.right
  else if x = g.right then
    g.matrix 1 0 * ψ g.left + g.matrix 1 1 * ψ g.right
  else ψ x

/-- The fixed initial computational basis state. -/
def zeroBasis {p n : ℕ} : (Fin n → ZMod p) → ℂ := by
  classical
  exact fun x => if x = (fun _ => 0) then 1 else 0

/-- Execute an explicit operation list from the fixed initial state. -/
def executeGates {p n : ℕ} (gates : List (TwoLevelGate p n)) :
    (Fin n → ZMod p) → ℂ :=
  gates.foldl (fun ψ g => g.apply ψ) zeroBasis

/-- Execution contract: the legacy state and cost must equal the output and
length of an explicit two-level operation list. -/
def PreparesIn {p n : ℕ} (ψ : (Fin n → ZMod p) → ℂ) (T : ℕ) : Prop :=
  ∃ Q : StateProcedure p n, ∃ gates : List (TwoLevelGate p n),
    Q.state = executeGates gates ∧ Q.cost = gates.length ∧ Q.state = ψ ∧ Q.cost ≤ T

/-- A zero operation budget can only produce the fixed initial basis state. -/
theorem preparesIn_zero {p n : ℕ} {ψ : (Fin n → ZMod p) → ℂ}
    (h : PreparesIn ψ 0) : ψ = zeroBasis := by
  obtain ⟨Q, gates, hs, hc, hψ, hT⟩ := h
  have hz : gates.length = 0 := Nat.eq_zero_of_le_zero (hc ▸ hT)
  have hg : gates = [] := by
    cases gates with
    | nil => rfl
    | cons g gs => simp at hz
  subst gates
  exact hψ.symm.trans hs

/-- Hamming weight of a vector over `F_p`. -/
def hammingWeight {p n : ℕ} (y : Fin n → ZMod p) : ℕ :=
  (Finset.univ.filter fun j => y j ≠ 0).card

/-- The parity-check syndrome map `y ↦ Dᵀy = ∑_i D_{ij}y_i` of Algorithm 1,
Step 5: column `i` of `D` is the diagonal of the constraint matrix `C_i`. -/
def syndrome {p m n : ℕ} (D : Fin m → Fin n → ZMod p) (y : Fin m → ZMod p) :
    Fin n → ZMod p :=
  fun j => ∑ i, D i j * y i

/-- A single-valued decoder for the syndrome map `syndrome D`, correct on all
error vectors of Hamming weight at most `ℓ`, with a declared classical cost.
This is the paper's "efficient decoding scheme" for the parity-check matrix
whose columns are the diagonals of the `C_i`. -/
structure EfficientDecoder (p m n ℓ : ℕ) (D : Fin m → Fin n → ZMod p) where
  /-- The classical decoding function. -/
  decode : (Fin n → ZMod p) → (Fin m → ZMod p)
  /-- Correctness on errors of weight at most `ℓ` (the weight range occurring
  in the degree-`ℓ` DQI state). -/
  correct : ∀ y : Fin m → ZMod p, hammingWeight y ≤ ℓ → decode (syndrome D y) = y
  /-- Declared classical cost of one decoding call. -/
  cost : ℕ

/-- A classical decoder program using coordinate equality tests and constant
output vectors. Every branch is explicit; no arbitrary function is a primitive. -/
inductive DecoderProgram (p m n : ℕ) where
  | output : (Fin m → ZMod p) → DecoderProgram p m n
  | test : Fin n → ZMod p → DecoderProgram p m n →
      DecoderProgram p m n → DecoderProgram p m n

/-- Execute the decision tree on a syndrome. -/
def DecoderProgram.run {p m n : ℕ} (s : Fin n → ZMod p) :
    DecoderProgram p m n → (Fin m → ZMod p)
  | .output y => y
  | .test j a yes no => if s j = a then yes.run s else no.run s

/-- Worst-case number of tests and output writes, including a halt step. -/
def DecoderProgram.steps {p m n : ℕ} : DecoderProgram p m n → ℕ
  | .output _ => m + 1
  | .test _ _ yes no => 1 + max yes.steps no.steps

/-- Actual number of tests and output writes on one input. -/
def DecoderProgram.time {p m n : ℕ} (s : Fin n → ZMod p) :
    DecoderProgram p m n → ℕ
  | .output _ => m + 1
  | .test j a yes no => 1 + if s j = a then yes.time s else no.time s

/-- The declared tree bound dominates the executed path on every input. -/
theorem DecoderProgram.time_le_steps {p m n : ℕ}
    (prog : DecoderProgram p m n) (s : Fin n → ZMod p) :
    prog.time s ≤ prog.steps := by
  induction prog with
  | output y => exact le_rfl
  | test j a yes no hy hn =>
    simp only [DecoderProgram.time, DecoderProgram.steps]
    split
    · exact Nat.add_le_add_left (hy.trans (Nat.le_max_left _ _)) 1
    · exact Nat.add_le_add_left (hn.trans (Nat.le_max_right _ _)) 1

/-- An efficient decoder contract requires a program computing the declared
function and a cost equal to its worst-case step count. Polynomial efficiency
is only a pointwise bound here; no uniform family is supplied. -/
def HasEfficientDecoder {p m n ℓ : ℕ} (D : Fin m → Fin n → ZMod p) : Prop :=
  ∃ dec : EfficientDecoder p m n ℓ D, ∃ prog : DecoderProgram p m n,
    (∀ s, prog.run s = dec.decode s) ∧ dec.cost = prog.steps ∧
      ∃ c : ℕ, dec.cost ≤ (m + n + 1) ^ c + 1

end Qatlib.Papers.DQIQuadOpt25.MainResults.Source
