/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Pauli-path source model

Aharonov--Gao--Landau--Liu--Vazirani, fixed arXiv:2211.03999v1
("A polynomial-time classical algorithm for noisy random circuit sampling").

This file introduces the discrete objects used by the paper's Pauli-path analysis:
single-qubit Paulis `{I,X,Y,Z}`, the normalized single-qubit Pauli matrices, `n`-qubit
Pauli assignments, Pauli paths of depth `d`, their Hamming weight, gate architectures
(each layer pairs the `n` qubits), the legality predicate of Definition 6, and the
Fourier weight of Definition 5.  All quantum-mechanical content is represented by
explicit `2 × 2` complex matrices, so that the trace identities used in Lemmas 2 and 5
can be checked unconditionally.

Source locations: Definition 1 (p.7, Eq. (5)--(8)), Definition 2 (p.8, Eqs. (9)--(12)),
Definition 5 (p.11, Eq. (24)), Definition 6 (p.13).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

open Matrix BigOperators

/-- Single-qubit Pauli labels, ordered `I, X, Y, Z` (Definition 1 / Eq. (5), p.7). -/
inductive Pauli1 where
  | I | X | Y | Z
  deriving DecidableEq, Fintype, Repr

/-- The (unnormalized) single-qubit Pauli matrices. -/
def Pauli1.mat : Pauli1 → Matrix (Fin 2) (Fin 2) ℂ
  | .I => 1
  | .X => !![0, 1; 1, 0]
  | .Y => !![0, -Complex.I; Complex.I, 0]
  | .Z => !![1, 0; 0, -1]

/-- The normalized Pauli matrices `P/√2` used in the paper's operator basis
`P_n = {I/√2, X/√2, Y/√2, Z/√2}^{⊗n}` (Eq. (5), p.7). -/
def Pauli1.normMat (P : Pauli1) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • P.mat

/-- Conjugation sign: `V P V† = conjSign V P • P` for single-qubit Paulis.  It is `+1`
exactly when `V = I`, `P = I`, or `V = P` (all other pairs anticommute). -/
def Pauli1.conjSign (V P : Pauli1) : ℂ :=
  if V = Pauli1.I ∨ P = Pauli1.I ∨ V = P then 1 else -1

/-- Every single-qubit Pauli matrix is Hermitian (used for `V† = V`). -/
theorem Pauli1.mat_conjTranspose (P : Pauli1) : (P.mat)ᴴ = P.mat := by
  fin_cases P <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Pauli1.mat, Matrix.conjTranspose_apply]

/-- Conjugation of a single-qubit Pauli matrix by another Pauli matrix only changes the
sign: `V P V† = conjSign V P • P`.  Checked by exhaustive case analysis on the four
Pauli labels (the three `{X,Y,Z}` matrices pairwise anticommute). -/
theorem Pauli1.mat_conj (V P : Pauli1) :
    V.mat * P.mat * (V.mat)ᴴ = Pauli1.conjSign V P • P.mat := by
  fin_cases V <;> fin_cases P <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Pauli1.mat, Pauli1.conjSign, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.smul_apply, Fin.sum_univ_two] <;>
        try norm_num

/-- Right-associated form of `Pauli1.mat_conj`, convenient inside Kronecker products. -/
theorem Pauli1.mat_conj_assoc (V P : Pauli1) :
    V.mat * (P.mat * (V.mat)ᴴ) = Pauli1.conjSign V P • P.mat := by
  simpa [mul_assoc] using Pauli1.mat_conj V P

/-- The Pauli character is orthogonal: for distinct single-qubit Paulis `P ≠ Q`, the
average of `conjSign (·) P * conjSign (·) Q` over the four Paulis vanishes.  This is the
one-qubit core of Eq. (20), p.9. -/
theorem Pauli1.char_sum_zero (P Q : Pauli1) (h : P ≠ Q) :
    ∑ V : Pauli1, Pauli1.conjSign V P * Pauli1.conjSign V Q = 0 := by
  have huniv : (Finset.univ : Finset Pauli1) = {Pauli1.I, Pauli1.X, Pauli1.Y, Pauli1.Z} := by
    decide
  fin_cases P <;> fin_cases Q <;>
    first
      | exact False.elim (h rfl)
      | · rw [huniv]
          simp [Pauli1.conjSign]
          try norm_num

/-- An `n`-qubit Pauli assignment (unnormalized), Eq. (5), p.7. -/
abbrev Pauli (n : ℕ) := Fin n → Pauli1

/-- A Pauli path of circuit depth `d`: `d+1` time slices, Eq. (6), p.7. -/
abbrev PauliPath (n d : ℕ) := Fin (d + 1) → Pauli n

/-- Hamming weight of one time slice: number of non-identity single-qubit Paulis. -/
def sliceWeight {n : ℕ} (s : Pauli n) : ℕ :=
  (Finset.univ.filter (fun q => s q ≠ Pauli1.I)).card

/-- Hamming weight `|s|` of a Pauli path (Definition 2, p.8). -/
def pathWeight {n d : ℕ} (s : PauliPath n d) : ℕ :=
  ∑ i : Fin (d + 1), sliceWeight (s i)

/-- A circuit architecture: in every layer `i : Fin d` every qubit is paired with a
partner (`mate`), the pairing is an involution, and no qubit is paired with itself
(Definition 3, p.9; `n` is even and each layer consists of `n/2` two-qubit gates). -/
structure Architecture (n d : ℕ) where
  mate : Fin d → Fin n → Fin n
  mate_invol : ∀ i q, mate i (mate i q) = q
  mate_ne : ∀ i q, mate i q ≠ q

/-- The input/output pair of a two-qubit gate is either both `I` or both non-`I`
(first legality condition of Definition 6, p.13). -/
def pairLegal (a b : Pauli1) : Prop :=
  (a = Pauli1.I ∧ b = Pauli1.I) ∨ (a ≠ Pauli1.I ∧ b ≠ Pauli1.I)

instance (a b : Pauli1) : Decidable (pairLegal a b) := by
  unfold pairLegal; infer_instance

/-- A single gate is legal when both its input pair and its output pair satisfy
`pairLegal`. -/
def gateLegal (a b c e : Pauli1) : Prop := pairLegal a b ∧ pairLegal c e

/-- A path satisfies the `I`/`Z` boundary condition when a slice uses only `I` and `Z`. -/
def boundaryLegal {n : ℕ} (s : Pauli n) : Prop :=
  ∀ q, s q = Pauli1.I ∨ s q = Pauli1.Z

/-- Definition 6 (p.13): a Pauli path is legal for an architecture when every two-qubit
gate preserves the all-identity status of its pair, and the first and last slices
contain only `I` and `Z`. -/
def IsLegal {n d : ℕ} (A : Architecture n d) (s : PauliPath n d) : Prop :=
  (∀ (i : Fin d) (q : Fin n),
      gateLegal (s i.castSucc q) (s i.castSucc (A.mate i q)) (s i.succ q)
        (s i.succ (A.mate i q))) ∧
  boundaryLegal (s 0) ∧ boundaryLegal (s (Fin.last d))

/-- Number of legal Pauli paths with Hamming weight exactly `k` (used in Lemma 6). -/
def legalPathCount (n d : ℕ) (A : Architecture n d) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : PauliPath n d => IsLegal A s ∧ pathWeight s = k)).card

/-- Number of legal Pauli paths with Hamming weight at most `ℓ` (used in Lemmas 7--8). -/
def legalPathCountUpTo (n d : ℕ) (A : Architecture n d) (ℓ : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : PauliPath n d => IsLegal A s ∧ pathWeight s ≤ ℓ)).card

end Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel
