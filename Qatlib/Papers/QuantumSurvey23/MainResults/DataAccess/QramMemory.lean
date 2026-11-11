/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c004 — QRAM qubit cost: `O(N)` hardware versus `O(log N)` data qubits

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 9.1 (arXiv source lines 8149–8151).

Source conclusion: a QRAM addresses `N` classical data entries with only
`O(log N)` *data* qubits, but the memory hardware itself needs `O(N)` physical
qubits (and, in passive/ion-trap implementations, comparable depth).  So the
qubit saving is in the registers, not in the device.

Formalization notes:
* `dataQubits N = log₂ N + 1` — the address register size;
* `qramQubits N = N` — the physical memory cells.

The load-bearing facts are `data_qubits_le_linear` (`log₂ N + 1 ≤ N`) and
`qram_qubits_exponential_in_data` (`2^(dataQubits N - 1) ≤ qramQubits N`): the
hardware is exponential in the number of data qubits.  Together they express
"`O(N)` qubits versus `O(log N)` data qubits" without inventing a gate model.

Reusable dependency (Dev bind `EffectiveAccess.AccessImpl`,
`TableAccess.LookupCompile`): `QuantumAlgorithm.Concepts.EffectiveAccess.AccessImpl`
models the address/register split; the bucket-brigade QRAM compilation is
`QuantumAlgorithm.Concepts.TableAccess.LookupCompile`.  This module records the
qubit-count assessment only.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.DataAccess

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Number of qubits in the address register of an `N`-entry QRAM. -/
def dataQubits (N : ℕ) : ℕ := Nat.log2 N + 1

/-- Number of physical memory qubits of an `N`-entry QRAM. -/
def qramQubits (N : ℕ) : ℕ := N

/-- **c004a (Section 9.1).** The data/address register is logarithmic:
`log₂ N + 1 ≤ N` for every `N ≥ 1`. -/
theorem data_qubits_le_linear (N : ℕ) (hN : 1 ≤ N) : dataQubits N ≤ N := by
  unfold dataQubits
  have h : Nat.log2 N < N := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_self 2 (by omega)
  omega

/-- **c004b (Section 9.1).** The physical QRAM is exponential in the
number of data qubits: with `k = dataQubits N` address qubits there are
`N ≥ 2^(k-1)` memory cells, and the hardware needs `N = qramQubits N` qubits. -/
theorem qram_qubits_exponential_in_data (N : ℕ) (hN : 1 ≤ N) :
    2 ^ (dataQubits N - 1) ≤ qramQubits N := by
  unfold dataQubits qramQubits
  have hsub : Nat.log2 N + 1 - 1 = Nat.log2 N := by simp
  rw [hsub, Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 (by omega)

/-- **c004 (Section 9.1), combined assessment.** The data register is at
most linear in `N`, while the physical QRAM is at least exponential in the data
register — the survey's "`O(N)` qubits vs. `O(log N)` data qubits". -/
theorem qram_memory_tradeoff (N : ℕ) (hN : 1 ≤ N) :
    dataQubits N ≤ qramQubits N ∧
    2 ^ (dataQubits N - 1) ≤ qramQubits N := by
  refine ⟨?_, qram_qubits_exponential_in_data N hN⟩
  exact le_trans (data_qubits_le_linear N hN) (le_refl N)

end Qatlib.Papers.QuantumSurvey23.MainResults.DataAccess
