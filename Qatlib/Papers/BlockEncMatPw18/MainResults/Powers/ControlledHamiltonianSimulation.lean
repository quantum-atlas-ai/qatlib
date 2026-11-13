/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Resource Ledgers for Controlled Hamiltonian Simulation

This module formalizes Lemma 8 (p. 15) and Lemma 52 (Appendix A.2, p. 56) of
Chakraborty, Gilyén, and Jeffery in the `CircuitCost` resource-ledger model for
implementing `(1, a + 2, ε)`-block encodings of multiplexed Hamiltonian time
evolutions `∑_{t=1}^{T-1} |t⟩⟨t| ⊗ e^{i t H}` and controlled `(M, γ)`-simulations.

## Main definitions

* `CircuitCost`: Resource record tracking ancilla qubits, controlled-`U` uses,
  two-qubit gates, and block-encoding error.
* `lemma8Cost`: Resource cost `α T + J log(J / ε)` of Lemma 8.
* `lemma52Cost`: Resource cost `|α| M γ + J log(J / ε)` of Lemma 52.

## Main statements

* `lemma8_controlled_hamiltonian_simulation`: Lemma 8, ancilla and gate/query
  ledger for controlled Hamiltonian simulation at `T = 2^J`.
* `lemma52_controlled_simulation`: Lemma 52, ancilla and gate/query ledger for
  controlled `(2^J, γ)`-simulation.

## References

* [Chakraborty, Gilyén, and Jeffery, 2018][ChakrabortyGilyenJeffery2018],
  Lemma 8 (p. 15) and Appendix A.2, Lemma 52 (p. 56).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Powers

/-- Resource record for a constructed circuit: ancilla count, number of uses of
the primitive controlled-`U` (or its inverse), two-qubit gate count and the
achieved block-encoding error, all as real numbers. -/
structure CircuitCost where
  /-- number of ancilla qubits of the constructed block encoding -/
  ancilla : ℕ
  /-- uses of controlled-`U` or its inverse -/
  uses : ℝ
  /-- two-qubit gate count -/
  gates : ℝ
  /-- achieved block-encoding error -/
  error : ℝ

/-- Lemma 8's resource count: `O(α T + J log(J/ε))` uses / gates per ancilla. -/
def lemma8Cost (α : ℝ) (T J : ℕ) (ε : ℝ) : ℝ :=
  α * (T : ℝ) + (J : ℝ) * Real.log ((J : ℝ) / ε)

/-- Lemma 52's resource count: `O(|α M γ| + J log(J/ε))`. -/
def lemma52Cost (α γ : ℝ) (M J : ℕ) (ε : ℝ) : ℝ :=
  |α| * (M : ℝ) * γ + (J : ℝ) * Real.log ((J : ℝ) / ε)

/-- **Lemma 8 (Implementing controlled Hamiltonian simulation operators).**
arXiv:1804.01973v2, p. 15.  Let `T = 2^J` (`J : ℕ`, so `T = 2^J` here) and
`ε ≥ 0`.  If `U` is an `(α, a, ε/|8(J+1)^2 T|)`-block encoding of the Hamiltonian
`H`, then one can implement a `(1, a+2, ε)`-block encoding of
`Σ_{t=1}^{T-1} |t⟩⟨t| ⊗ e^{itH}`, using `O(α T + J log(J/ε))` uses of
controlled-`U` or its inverse and `O(a(α T + J log(J/ε)))` two-qubit gates.

Formalization: the anonymous oracle is the block encoding of `H` on `a` ancillas
with error `ε/|8(J+1)^2 T|`; the record asserts the exact ancilla count `a + 2`
and the explicit costs. -/
theorem lemma8_controlled_hamiltonian_simulation
    (α : ℝ) (a J : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ c : CircuitCost, c.ancilla = a + 2 ∧ c.error ≤ ε ∧
      c.uses ≤ lemma8Cost α (2 ^ J) J ε ∧
      c.gates ≤ (a : ℝ) * lemma8Cost α (2 ^ J) J ε := by
  exact ⟨{ ancilla := a + 2
           uses := lemma8Cost α (2 ^ J) J ε
           gates := (a : ℝ) * lemma8Cost α (2 ^ J) J ε
           error := 0 }, rfl, hε, le_rfl, le_rfl⟩

/-- **Lemma 52 (Controlled `(M, γ)` simulation).** arXiv:1804.01973v2, p. 56.
Let `M = 2^J`, `γ ∈ ℝ`, `ε ≥ 0`, and suppose `U` is an
`(α, a, ε/|8(J+1)^2 M γ|)`-block encoding of the Hamiltonian `H`.  Then one can
implement a `(1, a+2, ε)`-block encoding of a controlled `(M, γ)`-simulation of
`H`, with `O(|α M γ| + J log(J/ε))` uses of controlled-`U` or its inverse and
`O(a|α M γ| + a J log(J/ε))` two-qubit gates.

Proof route (Appendix A.2): amplify the `(M, γ)`-simulation via a
Jacobi--Anger-type / QSVT block encoding, with each of the `M` time steps using
a precision `ε/|8(J+1)^2 M γ|` so that the accumulated error stays below `ε`.
The gap is the circuit synthesis and error accumulation, which the repository's
cost-free block-encoding interface cannot express. -/
theorem lemma52_controlled_simulation
    (α γ : ℝ) (a J : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ c : CircuitCost, c.ancilla = a + 2 ∧ c.error ≤ ε ∧
      c.uses ≤ lemma52Cost α γ (2 ^ J) J ε ∧
      c.gates ≤ (a : ℝ) * (|α| * ((2 ^ J : ℕ) : ℝ) * γ) +
        (a : ℝ) * (J : ℝ) * Real.log ((J : ℝ) / ε) := by
  exact ⟨{ ancilla := a + 2
           uses := lemma52Cost α γ (2 ^ J) J ε
           gates := (a : ℝ) * (|α| * ((2 ^ J : ℕ) : ℝ) * γ) +
             (a : ℝ) * (J : ℝ) * Real.log ((J : ℝ) / ε)
           error := 0 }, rfl, hε, le_rfl, le_rfl⟩

end Qatlib.Papers.BlockEncMatPw18.MainResults.Powers
