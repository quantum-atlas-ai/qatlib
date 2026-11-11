/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiemannQITE25.MainResults.GateCount.GateCountModel

set_option backward.isDefEq.respectTransparency false

/-!
# RiemannQITE25 — compiled DB-QITE gate counts

Source: arXiv:2504.01065v1 (1 Apr 2025), *Role of Riemannian geometry in
double-bracket quantum imaginary-time evolution* (Zander, Seidel, Xiaoyue,
Gluza).  Fixed Claim `c001` (paper §3.1, pp. 5–6, footnote 3):

> The overall procedure has a favorable scaling valid in both the short and
> the long term: The procedure requires `3.5 n − 4` entangling gates [...] and
> only a single phase gate is executed [...]. When compiled without mid-circuit
> measurements, as done in the experiments, the procedure still has a favorable
> scaling of `6 n − 6` entangling gates.

The compiled object is the reflection `e^{i√s |0⟩⟨0|}` of Eq. (12): a phase
gate controlled on the remaining `n - 1` qubits, compiled by computing the
control status into a fresh ancilla with Gidney's logical AND, applying the
single phase gate there, and uncomputing the ancilla (§3.1, p. 5).  The paper's
two totals differ exactly in whether that uncomputation is measurement based
(footnote 3 charges its classically-controlled `Z` as `0.5 n` in expectation)
or fully coherent.

The ledger is defined in `GateCountModel`; the theorems below establish its
closed forms and the structural facts that the Claim asserts.  The modeling
boundary (the paper does not print per-gadget Qrisp numbers) is documented in
that file.
-/

set_option autoImplicit false

namespace Qatlib.Papers.RiemannQITE25.MainResults.GateCount

/-- **c001 — `3.5 n − 4` entangling gates with mid-circuit measurements.**
For `n ≥ 2`, the compiled `n`-qubit reflection of one DB-QITE step uses
`3.5 n − 4` entangling gates when the ancilla uncomputation may use
mid-circuit measurements: `n - 2` ladder rungs at `3` gates each, the
relative-phase Toffoli core at `2` gates, and the `0.5 n` expected
classically-controlled corrections of footnote 3.

Paper: §3.1, pp. 5–6 (arXiv:2504.01065v1). -/
theorem dbqite_entangling_count_midCircuit (n : ℕ) (hn : 2 ≤ n) :
    dbqiteEntanglingCount n true = 3.5 * (n : ℚ) - 4 := by
  unfold dbqiteEntanglingCount andLadderLength rungCost andComputeCost
    finalRungCost classicalCorrectionCount
  have h : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := Nat.cast_sub hn
  rw [h]
  norm_num
  ring

/-- **c001 — `6 n − 6` entangling gates without mid-circuit measurements.**
For `n ≥ 2`, the measurement-free compilation of the same reflection uses
`6 n − 6` entangling gates: `n - 2` ladder rungs at `3 + 3` gates
(compute plus explicit inverse), and the full Toffoli core at `6` gates.

Paper: §3.1, p. 6 (arXiv:2504.01065v1). -/
theorem dbqite_entangling_count_noMidCircuit (n : ℕ) (hn : 2 ≤ n) :
    dbqiteEntanglingCount n false = 6 * (n : ℚ) - 6 := by
  unfold dbqiteEntanglingCount andLadderLength rungCost andComputeCost
    andUncomputeCost finalRungCost
  have h : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := Nat.cast_sub hn
  rw [h]
  norm_num
  ring

/-- **c001 — exactly one phase gate.**  The compiled reflection executes a
single phase gate, on the ancilla holding the control status; everything else
is Clifford + T + RZ.

Paper: §3.1, pp. 5–6 (arXiv:2504.01065v1). -/
theorem dbqite_single_phase_gate (n : ℕ) : dbqitePhaseGateCount n = 1 := rfl

/-- **c001 — affinity of the count (short- and long-term scaling).**  In
either compilation mode the entangling-gate count is an affine function of the
qubit number, with the paper's slope and intercept: `6 n - 6` for the
measurement-free mode and `3.5 n - 4` with mid-circuit measurements.

Paper: §3.1, pp. 5–6 (arXiv:2504.01065v1). -/
theorem dbqite_entangling_affine (midCircuit : Bool) :
    ∃ a b : ℚ, ∀ n : ℕ, 2 ≤ n →
      dbqiteEntanglingCount n midCircuit = a * (n : ℚ) + b := by
  cases midCircuit
  · exact ⟨6, -6, fun n hn => by
      rw [dbqite_entangling_count_noMidCircuit n hn]
      ring⟩
  · exact ⟨7 / 2, -4, fun n hn => by
      rw [dbqite_entangling_count_midCircuit n hn]
      ring⟩

/-- **c001 — mid-circuit compilation is never more expensive.**  Allowing
mid-circuit measurements does not increase the entangling-gate count for
`n ≥ 2` (`3.5 n - 4 ≤ 6 n - 6`), so the paper's "favorable scaling" holds in
both compilation modes.

Paper: §3.1, pp. 5–6 (arXiv:2504.01065v1). -/
theorem dbqite_midCircuit_le_noMidCircuit (n : ℕ) (hn : 2 ≤ n) :
    dbqiteEntanglingCount n true ≤ dbqiteEntanglingCount n false := by
  rw [dbqite_entangling_count_midCircuit n hn,
    dbqite_entangling_count_noMidCircuit n hn]
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  linarith

/-- **Independent check of `6 n − 6` from Eq. (16).**  The 1-D Heisenberg
chain on `n` qubits has three two-local Pauli-pair terms (`XX`, `YY`, `ZZ`) on
each of its `n - 1` bonds, and every two-local term is two CNOTs (§3.1, p. 4),
so one measurement-free Hamiltonian-simulation layer uses `6 n − 6` entangling
gates — the same figure as the measurement-free reflection compilation.

Paper: §3.1 p. 4 (two CNOTs per two-local term) and Eq. (16), p. 6. -/
theorem heisenberg_trotter_entangling_count (n : ℕ) (hn : 1 ≤ n) :
    heisenbergTrotterEntangling n = 6 * n - 6 := by
  unfold heisenbergTrotterEntangling heisenbergTermCount heisenbergBondCount
    twoLocalTermEntanglingCount
  omega

/-- **Consistency of the two `6 n − 6` readings.**  For `n ≥ 2`, the
measurement-free reflection ledger and the Eq. (16) Hamiltonian-layer ledger
agree exactly.

Paper: §3.1, pp. 4–6, Eq. (16). -/
theorem dbqite_noMidCircuit_eq_heisenberg (n : ℕ) (hn : 2 ≤ n) :
    dbqiteEntanglingCount n false = (heisenbergTrotterEntangling n : ℚ) := by
  rw [dbqite_entangling_count_noMidCircuit n hn,
    heisenberg_trotter_entangling_count n (by omega)]
  have h6 : ((6 * n - 6 : ℕ) : ℚ) = 6 * (n : ℚ) - 6 := by
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * n)]
    push_cast
    ring
  rw [h6]

end Qatlib.Papers.RiemannQITE25.MainResults.GateCount
