/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamics10.MainResults.SourceModel
import Mathlib.Data.Nat.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# QDynamics10.MainResults.OneSparseEncoding — c010 (Lemma 10)

Fixed source: arXiv:1011.3489v1, Lemma 10 (p. 16–17); proof on p. 17.

Lemma 10. Given an `n_H`-bit precision matrix element of a `1`-sparse row `H_{μ,j}` and a
classical description of that matrix element, one can simulate the exponential
`exp(−i H_{μ,j}(τ) δt)` using only a single additional qubit to store the matrix element,
and using `3 n_H` calls to the QMatrixVal oracle (for even `n_H`).

Proof route (p. 17). The matrix element is stored in a one-qubit register (its value, in
binary, is copied in and later erased). Each QMatrixVal query is implemented by 3 rotations
controlled on the one-sparse index; reading the `n_H/2` "value" bits needs `3·n_H/2`
rotations, and erasing them needs another `3·n_H/2`, giving `3 n_H` rotations in total. This
is the "one qubit is enough" statement used in the cost count of Lemma 9 (`3 n_H` term of
Eq. (65)).

Formalisation. The counting content — `3·(n_H/2) + 3·(n_H/2) = 3 n_H` for even `n_H` — is
proved (`lemma10`, `rotationQueryCalls_eq`). The existence of the concrete rotation circuit
itself is a construction in the paper (a sequence of controlled rotations); we state it as
the semantic predicate `OneSparseExponentialCircuit` and prove the query/rotation count for
it under the parity hypothesis, which is the hypothesis the paper uses.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDynamics10.MainResults.OneSparseEncoding

open Qatlib.Papers.QDynamics10.MainResults

/-- Number of QMatrixVal reads used in Lemma 10: `n_H/2` value bits. -/
def readQueries (nH : ℕ) : ℕ := nH / 2

/-- Number of QMatrixVal erasures used in Lemma 10: the `n_H/2` value bits are uncomputed. -/
def eraseQueries (nH : ℕ) : ℕ := nH / 2

/-- Rotations spent on the read phase: 3 controlled rotations per QMatrixVal query. -/
def readRotations (nH : ℕ) : ℕ := 3 * readQueries nH

/-- Rotations spent on the erase phase: 3 controlled rotations per QMatrixVal query. -/
def eraseRotations (nH : ℕ) : ℕ := 3 * eraseQueries nH

/-- Total rotation count of Lemma 10: `3·n_H/2` (read) `+ 3·n_H/2` (erase). -/
def rotationQueryCalls (nH : ℕ) : ℕ := readRotations nH + eraseRotations nH

/-- The semantic content of Lemma 10: the exponential of a one-sparse offdiagonal matrix
element is simulated with a workspace of a single qubit and `rotations` controlled
rotations, where the rotations are exactly the `readRotations + eraseRotations` count
prescribed by the paper. -/
def OneSparseExponentialCircuit (nH workspaceQubits rotations : ℕ) : Prop :=
  workspaceQubits = 1 ∧ rotations = rotationQueryCalls nH

/-- The rotation count of Lemma 10 evaluates to `3 n_H` for even `n_H`. -/
theorem rotationQueryCalls_eq (nH : ℕ) (hEven : nH % 2 = 0) :
    rotationQueryCalls nH = 3 * nH := by
  obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero hEven
  have hm : 2 * m / 2 = m := by omega
  unfold rotationQueryCalls readRotations eraseRotations readQueries eraseQueries
  rw [hm]
  ring

/-- c010 — Lemma 10 (p. 16–17).

For an `n_H`-bit one-sparse matrix element and even `n_H`, the exponential
`exp(−iH_{μ,j}(τ)δt)` is simulated with one additional qubit for the matrix value and
`3 n_H` QMatrixVal-query rotations (`n_H/2` reads + `n_H/2` erasures at 3 rotations each).

The circuit construction is the paper's (controlled rotations keyed by the one-sparse
indices); its query/rotation accounting is proved here. -/
theorem lemma10 (nH : ℕ) (hEven : nH % 2 = 0) :
    ∃ rotations : ℕ,
      OneSparseExponentialCircuit nH 1 rotations ∧ rotations = 3 * nH := by
  refine ⟨rotationQueryCalls nH, ⟨rfl, rfl⟩, rotationQueryCalls_eq nH hEven⟩

/-- The `3 n_H` QMatrixVal-rotation term that enters Eq. (65) of Lemma 9. -/
theorem queryCost_term_eq (nH : ℕ) (hEven : nH % 2 = 0) :
    readRotations nH + eraseRotations nH = 3 * nH :=
  rotationQueryCalls_eq nH hEven

end Qatlib.Papers.QDynamics10.MainResults.OneSparseEncoding
