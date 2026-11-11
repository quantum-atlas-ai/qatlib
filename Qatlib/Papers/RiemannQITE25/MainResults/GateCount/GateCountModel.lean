/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# RiemannQITE25 — DB-QITE gate-count ledger (model)

Source: arXiv:2504.01065v1 (1 Apr 2025), *Role of Riemannian geometry in
double-bracket quantum imaginary-time evolution* (Zander, Seidel, Xiaoyue,
Gluza).  Fixed Claim `c001`, paper §3.1, pp. 5–6 and footnote 3.

The source states (without printing a derivation): the compiled DB-QITE
procedure needs `3.5 n - 4` entangling gates and executes a single phase gate;
when mid-circuit measurements are disallowed it needs `6 n - 6` entangling
gates.  What the paper *does* print is the compilation route:

* the reflection `e^{i√s |0⟩⟨0|}` is a phase gate controlled on the remaining
  `n - 1` qubits; its control status is computed into a fresh ancilla with
  Gidney's logical AND, the single phase gate is applied to that ancilla, and
  the ancilla is uncomputed (§3.1, p. 5);
* footnote 3 (p. 5) charges `0.5 n` in expectation for the
  classically-controlled `Z` of a measurement-based uncompute;
* each two-local Trotter term is two CNOTs (§3.1, p. 4), and Eq. (16)'s 1-D
  Heisenberg chain on `n` qubits has the three Pauli-pair terms `XX`, `YY`,
  `ZZ` on each of its `n - 1` bonds.

## Boundary

The paper does not print the per-gadget Qrisp numbers, so the ledger below is
the explicit reconstruction consistent with §3.1, footnote 3 and the two
reported totals.  The theorems in `SourceGateCount` prove the arithmetic closed
forms of this ledger; they do not verify the Qrisp compiler itself.  Keeping
the reconstruction explicit (rather than hiding it in a hypothesis) is the
point: every charged component is named and auditable.
-/

namespace Qatlib.Papers.RiemannQITE25.MainResults.GateCount

/-- Control count of the `n`-qubit reflection `e^{i√s |0⟩⟨0|}`: the phase is
controlled on the remaining `n - 1` qubits (§3.1, p. 5). -/
def reflectionControlCount (n : ℕ) : ℕ := n - 1

/-- Length of the Gidney-AND compute ladder: combining `n - 1` control bits
into one ancilla needs `n - 2` binary ANDs (§3.1, p. 5, Gidney [8]). -/
def andLadderLength (n : ℕ) : ℕ := n - 2

/-- Entangling gates charged by the compute stage of one Gidney logical AND. -/
def andComputeCost : ℚ := 3

/-- Entangling gates charged by the explicit inverse (measurement-free)
uncompute stage of one Gidney logical AND. -/
def andUncomputeCost : ℚ := 3

/-- Expected charge of the measurement-based uncompute for the whole ladder.
Footnote 3 (p. 5) states that the classically-controlled `Z` is triggered
half of the times and adds `0.5 n` to the runtime. -/
def classicalCorrectionCount (n : ℕ) : ℚ := (n : ℚ) / 2

/-- Entangling cost of the final rung, whose ancilla carries the phase.  With
mid-circuit measurements it is the relative-phase Toffoli core (2 entangling
gates); the measurement-free compilation uses the full Toffoli (6 entangling
gates). -/
def finalRungCost : Bool → ℚ
  | true => 2
  | false => 6

/-- Entangling cost of one non-final rung of the ladder: the Gidney-AND
compute, plus the explicit inverse when no mid-circuit measurement is allowed
(the measurement-based uncompute is charged separately in
`classicalCorrectionCount`). -/
def rungCost : Bool → ℚ
  | true => andComputeCost
  | false => andComputeCost + andUncomputeCost

/-- Entangling-gate ledger of the compiled `n`-qubit reflection of one DB-QITE
step.  `midCircuit = true` means that mid-circuit measurements are allowed,
so uncomputation is measurement based (footnote 3); `false` is the
measurement-free compilation used in the paper's experiments (§3.1, p. 6).

The ledger is `(n - 2)` non-final rungs, plus the final rung that holds the
phase, plus — in the mid-circuit mode — the expected classical corrections of
footnote 3. -/
def dbqiteEntanglingCount (n : ℕ) (midCircuit : Bool) : ℚ :=
  (andLadderLength n : ℚ) * rungCost midCircuit + finalRungCost midCircuit +
    (if midCircuit then classicalCorrectionCount n else 0)

/-- The compiled reflection executes exactly one phase gate: the single phase
on the ancilla (§3.1, p. 5). -/
def dbqitePhaseGateCount (_n : ℕ) : ℕ := 1

/-- Entangling gates in one two-local Trotter term: two CNOTs (§3.1, p. 4). -/
def twoLocalTermEntanglingCount : ℕ := 2

/-- Bonds of the 1-D Heisenberg chain of Eq. (16) on `n` qubits. -/
def heisenbergBondCount (n : ℕ) : ℕ := n - 1

/-- Two-local Pauli-pair terms of Eq. (16): `XX`, `YY`, `ZZ` on every bond. -/
def heisenbergTermCount (n : ℕ) : ℕ := 3 * heisenbergBondCount n

/-- Entangling gates of one measurement-free Hamiltonian-simulation layer:
every two-local term is two CNOTs. -/
def heisenbergTrotterEntangling (n : ℕ) : ℕ :=
  heisenbergTermCount n * twoLocalTermEntanglingCount

end Qatlib.Papers.RiemannQITE25.MainResults.GateCount
