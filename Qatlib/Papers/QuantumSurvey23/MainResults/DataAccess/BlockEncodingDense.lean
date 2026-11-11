/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c005 — Dense-matrix block encoding: ancilla/depth trade-off

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 17.3 (arXiv source lines 13788–13792).

Source conclusion: block encoding a dense `N × N` matrix needs either
`O(log N)` ancillas at `O(N²)` depth, or `O(N²)` ancillas at `polylog(N)` depth;
in either case the circuit has `Ω(N²)` size and `O(N)` T gates.

Formalization notes: the cost functions
* `shallowDepth N = log₂ N + 1`, `shallowAncilla N = N²` (few ancillas, deep),
* `deepAncillaMin N = log₂ N + 1`, `deepDepth N = N²` (many ancillas, shallow),
* `circuitSize N = N²`, `tGates N = N`.

The substantive arithmetic here is the addressing bound
`N ≤ 2^(log₂ N + 1)`: at least `log₂ N` depth levels are needed to address `N`
entries, so "polylog depth" cannot be pushed below `log N`.  The trade-off is
recorded as an exact pair of (depth, ancilla) profiles with the same total
`N²` circuit size.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.DataAccess

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Number of data entries addressable by `k` qubits: `2^k`. -/
def addressable (k : ℕ) : ℕ := 2 ^ k

/-- Depth of the polylog-depth block encoding of a dense `N × N` matrix. -/
def shallowDepth (N : ℕ) : ℕ := Nat.log2 N + 1

/-- Ancilla count of the polylog-depth block encoding: `N²` ancillas. -/
def shallowAncilla (N : ℕ) : ℕ := N * N

/-- Ancilla count of the low-ancilla block encoding: `log₂ N + 1`. -/
def lowAncilla (N : ℕ) : ℕ := Nat.log2 N + 1

/-- Depth of the low-ancilla block encoding: `N²`. -/
def lowDepth (N : ℕ) : ℕ := N * N

/-- Circuit size lower bound for a dense `N × N` block encoding: `N²`. -/
def circuitSize (N : ℕ) : ℕ := N * N

/-- T-gate count of the dense block encoding: linear in `N`. -/
def tGates (N : ℕ) : ℕ := N

/-- **c005a (Section 17.3).** Polylog depth still requires enough levels to
address `N` entries: `N ≤ 2^(shallowDepth N)`. -/
theorem shallow_depth_addresses (N : ℕ) : N ≤ addressable (shallowDepth N) := by
  unfold addressable shallowDepth
  have h : N < 2 ^ (Nat.log 2 N).succ :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  rw [← Nat.log2_eq_log_two] at h
  simpa [Nat.succ_eq_add_one] using le_of_lt h

/-- **c005b (Section 17.3).** The two block-encoding profiles of a dense
`N × N` matrix: `(log₂ N + 1)` depth with `N²` ancillas, or `(log₂ N + 1)`
ancillas with `N²` depth.  Both have `N²` circuit size and `N` T gates, and the
polylog profile's depth is at most the linear T-gate count. -/
theorem dense_block_encoding_tradeoff (N : ℕ) (hN : 1 ≤ N) :
    shallowDepth N = lowAncilla N ∧
    shallowAncilla N = circuitSize N ∧
    lowDepth N = circuitSize N ∧
    shallowDepth N ≤ tGates N ∧
    tGates N ≤ circuitSize N := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · -- `log₂ N + 1 ≤ N`
    unfold shallowDepth tGates
    have h : Nat.log2 N < N := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_self 2 (by omega)
    omega
  · unfold tGates circuitSize
    have h : N * 1 ≤ N * N := Nat.mul_le_mul_left N hN
    simpa using h

end Qatlib.Papers.QuantumSurvey23.MainResults.DataAccess
