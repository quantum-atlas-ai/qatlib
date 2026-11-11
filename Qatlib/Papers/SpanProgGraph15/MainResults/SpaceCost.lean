/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgGraph15.MainResults.SourceSpanPrograms

set_option backward.isDefEq.respectTransparency false

/-!
# Space cost: `O(log n)` qubits (§1, p. 2)

Fixed source: arXiv:1510.07825v1 (27 Oct 2015), A. Āriņš,
*Span-program-based quantum algorithms for graph bipartiteness and connectivity*.

The paper's fourth main claim (§1, p. 2) is that both algorithms need only
`O(log n)` qubits of quantum memory, because the span programs `P₁` and `P₂`
live in vector spaces of dimension `2n² + 1` and `n² − 1` respectively
(§3, p. 3 and §4, p. 5), so their state can be stored in a register of
`⌈log₂(dim)⌉ = O(log n)` qubits.

This module makes that statement quantitative:

* `qubitCost d = Nat.clog 2 d` is the number of qubits needed to index a
  `d`-dimensional Hilbert space;
* `bip_qubitCost_le` : `qubitCost (2n² + 1) ≤ 2 log₂ n + 3`;
* `conn_qubitCost_le` : `qubitCost (n² − 1) ≤ 2 log₂ n + 2`;
* `bip_qubits_O_log` and `conn_qubits_O_log` package these as linear bounds in
  `log₂ n + 1`, i.e. `O(log n)`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open Finset

namespace Qatlib.Papers.SpanProgGraph15.MainResults

/-- The number of qubits needed to index a `d`-dimensional Hilbert space,
`⌈log₂ d⌉` (`Nat.clog 2 d`). -/
def qubitCost (d : ℕ) : ℕ := Nat.clog 2 d

/-- `P₁`'s ambient space `2n² + 1` needs at most `2 log₂ n + 3` qubits for
`n ≥ 1` (dimension of `P₁`, §3, p. 3). -/
theorem bip_qubitCost_le {n : ℕ} (hn : 1 ≤ n) :
    qubitCost (2 * n ^ 2 + 1) ≤ 2 * Nat.log2 n + 3 := by
  rw [qubitCost, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  have hp : n < 2 ^ (Nat.log2 n + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    rw [Nat.log2_eq_log_two]
    simpa using h
  have hp2 : n ^ 2 < 2 ^ (2 * Nat.log2 n + 2) := by
    have h : n ^ 2 < (2 ^ (Nat.log2 n + 1)) ^ 2 :=
      Nat.pow_lt_pow_left hp (by norm_num)
    rwa [← pow_mul, show (Nat.log2 n + 1) * 2 = 2 * Nat.log2 n + 2 by ring] at h
  have h2 : n ^ 2 + 1 ≤ 2 ^ (2 * Nat.log2 n + 2) := by
    simpa using Nat.succ_le_of_lt hp2
  have h3 : 2 * (n ^ 2 + 1) ≤ 2 ^ (2 * Nat.log2 n + 3) := by
    calc 2 * (n ^ 2 + 1) ≤ 2 * 2 ^ (2 * Nat.log2 n + 2) := Nat.mul_le_mul_left 2 h2
      _ = 2 ^ (2 * Nat.log2 n + 3) := by
          rw [show 2 * Nat.log2 n + 3 = 2 * Nat.log2 n + 2 + 1 by omega, pow_succ]
          ring
  have h4 : 2 * n ^ 2 + 1 ≤ 2 * (n ^ 2 + 1) := by omega
  exact le_trans h4 h3

/-- `P₂`'s ambient space `n² − 1` needs at most `2 log₂ n + 2` qubits for
`n ≥ 1` (dimension of `P₂`, §4, p. 5). -/
theorem conn_qubitCost_le {n : ℕ} (hn : 1 ≤ n) :
    qubitCost (n ^ 2 - 1) ≤ 2 * Nat.log2 n + 2 := by
  rw [qubitCost, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  have hp : n < 2 ^ (Nat.log2 n + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    rw [Nat.log2_eq_log_two]
    simpa using h
  have hp2 : n ^ 2 < 2 ^ (2 * Nat.log2 n + 2) := by
    have h : n ^ 2 < (2 ^ (Nat.log2 n + 1)) ^ 2 :=
      Nat.pow_lt_pow_left hp (by norm_num)
    rwa [← pow_mul, show (Nat.log2 n + 1) * 2 = 2 * Nat.log2 n + 2 by ring] at h
  exact le_trans (Nat.sub_le _ _) (Nat.le_of_lt hp2)

/-- Both algorithms need only `O(log n)` qubits: `qubitCost` of the dimension
of `P₁` is linearly bounded in `log₂ n + 1` (§1, p. 2). -/
theorem bip_qubits_O_log :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → qubitCost (2 * n ^ 2 + 1) ≤ C * (Nat.log2 n + 1) := by
  refine ⟨4, fun n hn => ?_⟩
  refine le_trans (bip_qubitCost_le hn) ?_
  omega

/-- Both algorithms need only `O(log n)` qubits: `qubitCost` of the dimension
of `P₂` is linearly bounded in `log₂ n + 1` (§1, p. 2). -/
theorem conn_qubits_O_log :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → qubitCost (n ^ 2 - 1) ≤ C * (Nat.log2 n + 1) := by
  refine ⟨3, fun n hn => ?_⟩
  refine le_trans (conn_qubitCost_le hn) ?_
  omega

/-- The dimension of `P₁` is `2n²+1` (§3, p. 3), restated for the space cost. -/
theorem bip_space_dim (n : ℕ) : Fintype.card (BipBasis n) = 2 * n ^ 2 + 1 :=
  card_bipBasis n

/-- The dimension of `P₂` is `n²−1` (§4, p. 5), restated for the space cost. -/
theorem conn_space_dim {n : ℕ} (hn : 1 ≤ n) : Fintype.card (ConnBasis n) = n ^ 2 - 1 :=
  card_connBasis n hn

end Qatlib.Papers.SpanProgGraph15.MainResults
