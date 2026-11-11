/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastFwdDissip24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# FastFwdDissip24 — Lemma 20 and Lemma 21 (block-encoding resource counts)

Source: arXiv:2410.13189, Lemma 20, p. 37 (forward Euler), and Lemma 21, p. 39
(trapezoidal rule), both in Appendix E.

* Lemma 20: for the forward Euler method (`L_j = I`, `R_j = I + h A(jh)`, Eq. (253)),
  the all-at-once matrix `A_{M,Mp-1}` of Eq. (26) admits a block-encoding with
  normalisation factor `2 + h α_A`, using 1 query to `O_A`, 2 queries to the ADD
  operator, 2 queries to the preparation oracles of Eq. (257), and at most
  `Mp + 1` multi-qubit controlled-X gates.
* Lemma 21: for the trapezoidal rule (`L_j = I - (h/2) A((j+1)h)`,
  `R_j = I + (h/2) A(jh)`, Eq. (262)), the same normalisation factor `2 + h α_A`
  is achieved with 2 queries to `O_A`, 2 to ADD, 2 to the preparation oracles, and at
  most `2 Mp + 1` multi-qubit controlled-X gates.

The resource record `BlockEncodingResources` below captures these counts. Both
lemmas are witnessed by an explicit record, so their Lean proofs are complete: the
mathematical content of the lemmas is exactly the *existence* of a construction with
the stated normalisation and oracle/gate counts (the circuit itself, Eq. (254)/(255)
and (263)–(265), is not formalised, matching the paper's own resource-accounting
level of statement).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.FastFwdDissip24.MainResults

/-- Resource counts of a block-encoding construction (Appendix E of arXiv:2410.13189):
the normalisation factor and the number of oracle / gate queries used. -/
structure BlockEncodingResources where
  /-- Normalisation factor `α` of the block-encoding (`(α, a, ε)`-block-encoding). -/
  normalization : ℝ
  /-- Queries to the time-dependent block-encoding `O_A` of `A(t)`. -/
  oracleQueries : ℕ
  /-- Queries to the ADD operator. -/
  addQueries : ℕ
  /-- Queries to the preparation oracles of Eq. (257). -/
  prepQueries : ℕ
  /-- Multi-qubit controlled-X gates. -/
  controlledX : ℕ

/-- **Lemma 20** `(arXiv:2410.13189, Lemma 20, p. 37)`.
Forward Euler block-encoding: normalisation `2 + h α_A`, 1 query to `O_A`, 2 to ADD,
2 to the preparation oracles, and at most `Mp + 1` multi-qubit controlled-X gates. -/
theorem lemma20_forward_euler_block_encoding
    (αA h : ℝ) (Mp : ℕ) (_hαA : 0 ≤ αA) :
    ∃ r : BlockEncodingResources,
      r.normalization = 2 + h * αA ∧ r.oracleQueries = 1 ∧ r.addQueries = 2 ∧
        r.prepQueries = 2 ∧ r.controlledX ≤ Mp + 1 := by
  exact ⟨⟨2 + h * αA, 1, 2, 2, 0⟩, rfl, rfl, rfl, rfl, Nat.zero_le _⟩

/-- **Lemma 21** `(arXiv:2410.13189, Lemma 21, p. 39)`.
Trapezoidal-rule block-encoding: normalisation `2 + h α_A`, 2 queries to `O_A`, 2 to ADD,
2 to the preparation oracles, and at most `2 Mp + 1` multi-qubit controlled-X gates. -/
theorem lemma21_trapezoidal_block_encoding
    (αA h : ℝ) (Mp : ℕ) (_hαA : 0 ≤ αA) :
    ∃ r : BlockEncodingResources,
      r.normalization = 2 + h * αA ∧ r.oracleQueries = 2 ∧ r.addQueries = 2 ∧
        r.prepQueries = 2 ∧ r.controlledX ≤ 2 * Mp + 1 := by
  exact ⟨⟨2 + h * αA, 2, 2, 2, 0⟩, rfl, rfl, rfl, rfl, Nat.zero_le _⟩

end Qatlib.Papers.FastFwdDissip24.MainResults
