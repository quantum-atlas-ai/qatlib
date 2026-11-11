/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Gate and ancilla cost of the XOR-Reduction oracle

Paper: arXiv:1512.00859v2 (29 Aug 2016), Sec. III, final paragraph (p. 12–13):
"the suggested implementation of the quantum oracle requires ⌈log M′⌉ ancilla
qubits, while the total number of gates is bounded by O(n²) since (I) has k
blocks with O(n) gates each, (II) has M′ blocks with O(1) gates each and (III)
has M′ blocks with O(log₂ M′) gates each."

The four modules of the oracle (source Figure 3 and the text that follows
Eq. (7)) are modelled by their worst-case gate counts:

* (I) builds the `n`-qubit XORSAT assignment from the `k`-qubit index; each of
  the `k` blocks touches at most `n` wires, hence at most `k·n` C-NOT/X gates;
* (II) evaluates the `M′` linear parity clauses, one gate per clause;
* (III) counts the unsatisfied clauses, using `⌈log₂ M′⌉` ancilla bits and
  `⌈log₂ M′⌉` gates per clause, hence `M′·⌈log₂ M′⌉` gates;
* (IV) is the single multi-qubit phase gate.

Since the register size is `k = n - M′ ≤ n` and `M′ ≤ n`, the total is bounded
by `4 n²`. The ancilla count is `Nat.clog 2 M′`, the integer ceiling of
`log₂ M′`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ExactSat15.MainResults.OracleGateCount

/-- Module (I): `k` blocks, each acting on at most `n` wires. -/
def moduleIGates (k n : ℕ) : ℕ := k * n

/-- Module (II): `M′` parity-clause blocks with one gate each. -/
def moduleIIGates (M' : ℕ) : ℕ := M'

/-- Module (III): `M′` counting blocks with `⌈log₂ M′⌉` gates each. -/
def moduleIIIGates (M' : ℕ) : ℕ := M' * Nat.clog 2 M'

/-- Module (IV): a single multi-qubit phase gate. -/
def moduleIVGates : ℕ := 1

/-- Total number of oracle gates: modules (I)–(IV) (source p. 12). -/
def oracleGateCount (k n M' : ℕ) : ℕ :=
  moduleIGates k n + moduleIIGates M' + moduleIIIGates M' + moduleIVGates

/-- Number of ancilla qubits, `⌈log₂ M′⌉` (source p. 12). -/
def oracleAncillas (M' : ℕ) : ℕ := Nat.clog 2 M'

/-- For every positive `m`, `m ≤ 2^m`. -/
theorem self_le_two_pow : ∀ m : ℕ, m ≤ 2 ^ m
  | 0 => by simp
  | m + 1 => by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have ih : m ≤ 2 ^ m := self_le_two_pow m
      rw [Nat.pow_succ]
      omega

/-- The ceiling logarithm is at most its argument for `m ≥ 1`. -/
theorem clog_two_le_self {m : ℕ} (hm : 1 ≤ m) : Nat.clog 2 m ≤ m := by
  rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  exact self_le_two_pow m

/-- **Oracle resource bound** (source p. 12): `⌈log₂ M′⌉` ancillas and at most
`4 n²` gates, where `k = n - M′ ≤ n` and `M′ ≤ n`.  In particular the oracle is
polynomial in both space and gate count. -/
theorem oracle_resources (k n M' : ℕ) (hk : k ≤ n) (hM : M' ≤ n) (hMpos : 1 ≤ M') :
    oracleAncillas M' = Nat.clog 2 M' ∧
    oracleGateCount k n M' ≤ 4 * n ^ 2 := by
  refine ⟨rfl, ?_⟩
  have hclog : Nat.clog 2 M' ≤ M' := clog_two_le_self hMpos
  have h1 : k * n ≤ n * n := Nat.mul_le_mul_right n hk
  have h2 : M' * Nat.clog 2 M' ≤ M' * M' := Nat.mul_le_mul_left M' hclog
  have h3 : M' * M' ≤ n * n := Nat.mul_self_le_mul_self hM
  have hn1 : 1 ≤ n := le_trans hMpos hM
  unfold oracleGateCount moduleIGates moduleIIGates moduleIIIGates moduleIVGates
  -- `2 n² + n + 1 ≤ 4 n²` for `n ≥ 1`.
  nlinarith [h1, h2, h3, hn1, sq_nonneg (n : ℤ)]

/-- The ancilla register is also polynomial in `n`, since `⌈log₂ M′⌉ ≤ M′ ≤ n`. -/
theorem oracleAncillas_le (n M' : ℕ) (hM : M' ≤ n) (hMpos : 1 ≤ M') :
    oracleAncillas M' ≤ n :=
  le_trans (clog_two_le_self hMpos) hM

end Qatlib.Papers.ExactSat15.MainResults.OracleGateCount
