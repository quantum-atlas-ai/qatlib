/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.ComputationDefs

/-!
# AdiabEquiv04 — simulation theorems (Theorems 1.1, 1.3, 3.1, 3.15, 4.1 and Corollary 1.2)

Statements of the paper's main simulation results, in terms of the concrete
Hamiltonians of `HistoryConstruction` and the complexity classes of
`ComputationModel`:

* Theorem 1.1 (p. 2): the 3-local adiabatic model is polynomially equivalent to
  the standard circuit model (`AdiabaticPolyClass 3 = StandardCircuitPolyClass`);
* Corollary 1.2 (p. 3): the same for explicit sparse Hamiltonians;
* Theorem 3.1 (p. 8): the 5-local construction `H_init, H_final` of equations
  (4)-(6) on `n + L` qubits simulates any circuit in `poly(L, 1/ε)` time, with
  output `ε`-close in trace distance to `U|0ⁿ⟩` after tracing out the clock;
* Theorem 3.15 (p. 17): the 3-local construction `H'_init, H'_final` with
  `J = ε⁻²L⁶` achieves the same;
* Theorem 1.3 (p. 4) / Theorem 4.1 (p. 21): a 2-local nearest-neighbour
  Hamiltonian on six-state particles of a two-dimensional grid simulates any
  circuit, with polynomially many particles and `poly(L, 1/ε)` running time.

The global statements are recorded as `Prop`-valued definitions (`…Statement`).
They are not proved: their mathematical content is carried by the adiabatic
theorem (Theorem 2.1 of the paper), which is not mechanised, and by the spectral
and composition lemmas of the sibling modules, which are likewise recorded as
statements.  The module contains no `sorry`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Simulation

open Qatlib.Papers.AdiabEquiv04.MainResults

open Qatlib.Papers.AdiabEquiv04.MainResults.Model

/-- **Theorem 3.1** (arXiv:quant-ph/0405098v2, p. 8), recorded statement.  Given
a quantum circuit on `n` qubits with `L` two-qubit gates implementing a unitary
`U` and `ε > 0`, the 5-local construction `H_init = H_clockinit + H_input +
H_clock` and `H_final = ½ Σ H_ℓ + H_input + H_clock` on `n + L` qubits yields
an adiabatic computation of locality 5, running time `poly(L, 1/ε)`, whose
output, after tracing out the clock qubits, is `ε`-close in trace distance to
`U|0ⁿ⟩`.  Moreover `H_init` and `H_final` have polynomial-size term descriptions
("computable by a polynomial-time Turing machine"). -/
def theorem_3_1_five_localStatement : Prop :=
  ∀ (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (ε : ℝ), 0 < ε →
    ∃ (A : AdiabaticComputation (TotalBasis n L)) (T : ℝ),
      A.Hinit = Hinit n L hL2 ∧
      A.Hfinal = Hfinal n L hL2 gates ∧
      A.locality = 5 ∧ 0 < T ∧
      (∃ C : ℝ, 0 < C ∧ ∃ d e : ℕ,
        T ≤ C * ((L : ℝ) + 1) ^ d * (1 / ε) ^ e) ∧
      (∃ ψ : Vector (TotalBasis n L), AdiabaticRunsTo ε A ψ) ∧
      StateClose (partialTrace A.output) (alpha gates L) ε ∧
      HasPolyTermDescription A.Hinit ∧ HasPolyTermDescription A.Hfinal

/-- **Theorem 3.15** (arXiv:quant-ph/0405098v2, p. 17), recorded statement.
The three-local construction `H'_init = H_clockinit + H_input + J·H_clock` and
`H'_final = ½ Σ H'_ℓ + H_input + J·H_clock` with `J = ε⁻²L⁶` gives, for every
circuit on `n` qubits with `L` gates and every `ε > 0`, a 3-local adiabatic
computation of running time `poly(L, 1/ε)` whose output, traced over the clock,
is `ε`-close in trace distance to `U|0ⁿ⟩`, with polynomial-size term
descriptions for both endpoint Hamiltonians. -/
def theorem_3_15_three_localStatement : Prop :=
  ∀ (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (ε : ℝ), 0 < ε →
    ∃ (A : AdiabaticComputation (TotalBasis n L)) (T : ℝ),
      A.Hinit = Hinit3 n L hL2 ((ε ^ 2)⁻¹ * (L : ℝ) ^ 6) ∧
      A.Hfinal = Hfinal3 n L hL2 gates ((ε ^ 2)⁻¹ * (L : ℝ) ^ 6) ∧
      A.locality = 3 ∧ 0 < T ∧
      (∃ C : ℝ, 0 < C ∧ ∃ d e : ℕ,
        T ≤ C * ((L : ℝ) + 1) ^ d * (1 / ε) ^ e) ∧
      (∃ ψ : Vector (TotalBasis n L), AdiabaticRunsTo ε A ψ) ∧
      StateClose (partialTrace A.output) (alpha gates L) ε ∧
      HasPolyTermDescription A.Hinit ∧ HasPolyTermDescription A.Hfinal

/-- **Theorem 1.1** (arXiv:quant-ph/0405098v2, p. 2), recorded statement.  The
model of adiabatic computation is polynomially equivalent to the standard model
of quantum computation: the class of languages decided by polynomial-time
3-local adiabatic computations equals the class decided by polynomial-size
quantum circuits.

(The paper first proves the 5-local version and then the 3-local version in
Section 3.2; the definition `AdiabaticPolyClass k` fixes the locality, and
`k = 3` is the paper's final locality.) -/
def theorem_1_1_poly_equivStatement : Prop :=
  AdiabaticPolyClass 3 = StandardCircuitPolyClass

/-- **Corollary 1.2** (arXiv:quant-ph/0405098v2, p. 3), recorded statement.  The
model of adiabatic computation with explicit sparse Hamiltonians is
polynomially equivalent to the standard model of quantum computation. -/
def corollary_1_2_sparse_equivStatement : Prop :=
  SparseAdiabaticPolyClass = StandardCircuitPolyClass

/-- **Theorem 4.1** (arXiv:quant-ph/0405098v2, p. 21), recorded statement.
Given a quantum circuit on `n` qubits with `L` two-qubit gates, `ε > 0`, there
is a 2-local adiabatic computation on six-state particles arranged on a
two-dimensional grid, with polynomially many particles, `poly(L, 1/ε)` running
time, and output `ε`-close in trace distance to `U|0ⁿ⟩` after a partial
measurement of the particles. -/
def theorem_4_1_two_local_gridStatement : Prop :=
  TwoLocalGridSimulatesCircuits

/-- **Theorem 1.3** (arXiv:quant-ph/0405098v2, p. 4), recorded statement.  Any
quantum computation can be efficiently simulated by an adiabatic computation
with two-local nearest-neighbour Hamiltonians on six-state particles set on a
two-dimensional grid.  This is the qualitative statement of Theorem 4.1
(p. 21), from which it follows directly. -/
def theorem_1_3_two_local_gridStatement : Prop :=
  theorem_4_1_two_local_gridStatement

end Qatlib.Papers.AdiabEquiv04.MainResults.Simulation
