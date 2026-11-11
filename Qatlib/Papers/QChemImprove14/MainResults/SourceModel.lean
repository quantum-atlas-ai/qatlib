/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QChemImprove14 — source model for the gate-count claims

Hastings, Wecker, Bauer, Troyer, *Improving Quantum Algorithms for Quantum
Chemistry*, fixed arXiv:1403.1539v2 (23 Mar 2014).

This file fixes the combinatorial/arithmetic objects underlying the paper's
five active claims, so the claim files can state and prove the actual
reductions (Secs. 1, 2, 6 and Eqs. (3), (4), (A1)–(A5)).  Nothing here
asserts Lean coverage of the physics; these are the paper's own gate-count
and string-length quantities.
-/

set_option autoImplicit false
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QChemImprove14.MainResults

/-! ## Jordan–Wigner string combinatorics (Sec. 1, Eqs. (3), (4)) -/

/-- The Pauli subterms of an `Hpqrs` term: assignments of `X`/`Y` to the four
orbitals with an even number of `X` operators (equivalently an even number of
`Y` operators), as in Sec. 1 between Eqs. (4) and (5). -/
def pauliSubterms : Finset (Fin 4 → Bool) :=
  Finset.univ.filter
    (fun σ => (Finset.univ.filter (fun i => σ i = true)).card % 2 = 0)

/-- There are exactly eight admissible `X`/`Y` subterms for an `Hpqrs` term
(the even-cardinality subsets of a four-element set), Sec. 1. -/
theorem pauliSubterms_card : pauliSubterms.card = 8 := by
  decide

/-- Length of the Jordan–Wigner `Z` string of an `Hpqrs` term with
`p < q < r < s`: the string covers orbitals `p+1..q-1` and `r+1..s-1`,
i.e. `(q-p-1) + (s-r-1)` qubits (Eqs. (3), (4)). -/
def jwStringLength (p q r s : ℕ) : ℕ := (q - p - 1) + (s - r - 1)

/-- Total string cost of the standard circuit of Fig. 1: the string is
applied once per Pauli subterm. -/
def standardStringCost (L : ℕ) : ℕ := pauliSubterms.card * L

/-- Total string cost of the modified circuit of Fig. 2: the string sits
outside all basis changes and is applied once per term. -/
def modifiedStringCost (L : ℕ) : ℕ := L

/-- Ancilla count of the constant-overhead modification of Fig. 2: none. -/
def modifiedAncillaCount : ℕ := 0

/-! ## Parallelization and gate-depth model (Secs. 2, 6) -/

/-- Number of `Hpqrs` terms, asymptotically `N^4` for `N` spin orbitals. -/
def twoBodyTermCount (N : ℕ) : ℕ := N ^ 4

/-- With the ancilla circuit and nesting, up to `Θ(N)` terms run in parallel
per round (Sec. 2). -/
def termsPerRound (N : ℕ) : ℕ := N

/-- Number of sequential rounds needed to schedule `T` terms at parallelism
`K` (the ceiling of `T/K`). -/
def roundCount (T K : ℕ) : ℕ := (T + K - 1) / K

/-- Serial gate count (one unit of work per term). -/
def serialWork (N : ℕ) : ℕ := twoBodyTermCount N

/-- Parallel depth of the nested circuit (one unit per round). -/
def parallelDepth (N : ℕ) : ℕ := roundCount (twoBodyTermCount N) (termsPerRound N)

/-- Gate depth of Ref. 17, scaling as `N^9` (Sec. 6). -/
noncomputable def refGateDepth (N : ℕ) : ℝ := (N : ℝ) ^ 9

/-- Depth after cancelling the Jordan–Wigner strings: `N^8`. -/
noncomputable def jwCancelledDepth (N : ℕ) : ℝ := (N : ℝ) ^ 8

/-- Depth after nesting/parallelizing the rotations: `N^7`. -/
noncomputable def nestedGateDepth (N : ℕ) : ℝ := (N : ℝ) ^ 7

end Qatlib.Papers.QChemImprove14.MainResults
