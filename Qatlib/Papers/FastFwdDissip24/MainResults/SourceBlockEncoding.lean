/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.FastFwdDissip24.MainResults.SourceModel

@[expose] public section


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

Resource ledgers alone do not construct a block encoding. Each result below
requires a unitary/corner certificate as a structural hypothesis; deriving that
certificate and the oracle counts from the Euler/trapezoidal circuits is open.
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

/-- A genuine unitary block encoding linked to its resource ledger.
The structural certificate does not model the gate/oracle execution trace. -/
structure BlockEncodingWitness {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j0 : J)
    (r : BlockEncodingResources) where
  /-- Unitary implementing the encoded matrix. -/
  U : Matrix (J × I) (J × I) ℂ
  /-- Positive block normalization. -/
  positive : 0 < r.normalization
  /-- The encoding circuit is unitary. -/
  unitary : U ∈ Matrix.unitaryGroup (J × I) ℂ
  /-- Its selected ancilla corner equals the scaled target matrix. -/
  corner : ∀ i j, (r.normalization : ℂ) * U (j0, i) (j0, j) = A i j

/-- Conditional forward-Euler reduction: the resource bound is attached to
an actual unitary/corner certificate, supplied by the unproved circuit bridge. -/
theorem lemma20_forward_euler_block_encoding
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j0 : J) (αA h : ℝ) (Mp : ℕ)
    (r : BlockEncodingResources) (B : BlockEncodingWitness A j0 r)
    (hcounts : r.normalization = 2 + h * αA ∧ r.oracleQueries = 1 ∧
      r.addQueries = 2 ∧ r.prepQueries = 2 ∧ r.controlledX ≤ Mp + 1) :
    ∃ r : BlockEncodingResources, Nonempty (BlockEncodingWitness A j0 r) ∧
      r.normalization = 2 + h * αA ∧ r.oracleQueries = 1 ∧ r.addQueries = 2 ∧
        r.prepQueries = 2 ∧ r.controlledX ≤ Mp + 1 := by
  exact ⟨r, ⟨B⟩, hcounts⟩

/-- Conditional trapezoidal reduction, requiring the actual matrix encoding
and a resource certificate from the missing circuit construction. -/
theorem lemma21_trapezoidal_block_encoding
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j0 : J) (αA h : ℝ) (Mp : ℕ)
    (r : BlockEncodingResources) (B : BlockEncodingWitness A j0 r)
    (hcounts : r.normalization = 2 + h * αA ∧ r.oracleQueries = 2 ∧
      r.addQueries = 2 ∧ r.prepQueries = 2 ∧ r.controlledX ≤ 2 * Mp + 1) :
    ∃ r : BlockEncodingResources, Nonempty (BlockEncodingWitness A j0 r) ∧
      r.normalization = 2 + h * αA ∧ r.oracleQueries = 2 ∧ r.addQueries = 2 ∧
        r.prepQueries = 2 ∧ r.controlledX ≤ 2 * Mp + 1 := by
  exact ⟨r, ⟨B⟩, hcounts⟩

end Qatlib.Papers.FastFwdDissip24.MainResults
