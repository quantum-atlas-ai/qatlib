/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# ControlledHamiltonianSimulation

The `_statement` definitions are unproved resource specifications requiring an
implementation relation. Numeric records alone do not certify execution or correctness.
No quantum circuit synthesis is proved here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Powers

/-- Legacy numeric metadata for a simulation specification. These stored values
are not operation counts without a separate implementation contract. -/
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

/-- **Statement only — not proved in Qatlib.** Resource specification for `lemma8_controlled_hamiltonian_simulation`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def lemma8_controlled_hamiltonian_simulation_statement
    (α : ℝ) (a J : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (Realizes : CircuitCost → Prop) : Prop :=
    ∃ c : CircuitCost, Realizes c ∧ c.ancilla = a + 2 ∧ c.error ≤ ε ∧
      c.uses ≤ lemma8Cost α (2 ^ J) J ε ∧
      c.gates ≤ (a : ℝ) * lemma8Cost α (2 ^ J) J ε

/-- **Statement only — not proved in Qatlib.** Resource specification for `lemma52_controlled_simulation`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def lemma52_controlled_simulation_statement
    (α γ : ℝ) (a J : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (Realizes : CircuitCost → Prop) : Prop :=
    ∃ c : CircuitCost, Realizes c ∧ c.ancilla = a + 2 ∧ c.error ≤ ε ∧
      c.uses ≤ lemma52Cost α γ (2 ^ J) J ε ∧
      c.gates ≤ (a : ℝ) * (|α| * ((2 ^ J : ℕ) : ℝ) * γ) +
        (a : ℝ) * (J : ℝ) * Real.log ((J : ℝ) / ε)

end Qatlib.Papers.BlockEncMatPw18.MainResults.Powers
