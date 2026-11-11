/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QInspired25.MainResults.Simulation.CoordinatorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum communication protocols — Propositions 18, 19 and Theorem 20 (pp. 13--14)

Fixed source: arXiv:2402.15686v3, §5.2 (pp. 13--14).

* **Proposition 18.** For `A` of the Alice--Bob form (15), one use of `O_A`, `O_R` or `O_C`
  costs `O(log(mn))` qubits of communication.  The paper's explicit counts are
  `2 log(mn)` for `O_A` (state out and back) and `2(2 log m + log n)` for `O_C`.
* **Proposition 19.** Two `(α_i, 1, 0)`-block-encodings of `A^{(i)}` can be combined into an
  `(√(α₁² + α₂²), 2, 0)`-block-encoding of `A` using `O(log(mn))` qubits.
* **Theorem 20.** A quantum algorithm of the form (7) or (9) with `O(T)` oracle
  uses/block-encodings gives a quantum protocol with `O(T log(mn))` qubits.

The formalisation records the *cost arithmetic* of the two propositions exactly as stated
(the constants `2` and `2(2 log m + log n)`) and the amplification factor `√(α₁²+α₂²)` of
the block-encoding composition.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Quantum

open Qatlib.Papers.QInspired25.MainResults.Model
open Qatlib.Papers.QInspired25.MainResults.Simulation

/-! ## §1. Proposition 18: one oracle use costs `O(log(mn))` qubits -/

/-- Qubits exchanged for one use of `O_A` or `O_R`: the state travels to Bob and back
(`2 log(mn)`, Proposition 18, p. 14). -/
def perEntryCommBits (m n : ℕ) : ℕ := 2 * logBits (m * n)

/-- Qubits exchanged for one use of `O_C` (`2(2 log m + log n)`, Proposition 18, p. 14). -/
def perColumnCommBits (m n : ℕ) : ℕ := 2 * (2 * logBits m + logBits n)

/-- One entry query costs `2 log(mn)` bits by definition. -/
theorem perEntryCommBits_eq (m n : ℕ) : perEntryCommBits m n = 2 * logBits (m * n) := rfl

/-- **Proposition 18, `O_A` cost (p. 14).**  `2 log(mn) ≤ 6 log(qmn)`: a single entry query
costs `O(log(mn))` qubits. -/
theorem perEntryCommBits_le_six (m n q : ℕ) (hm : 0 < m) (hn : 0 < n) (hq : 0 < q) :
    perEntryCommBits m n ≤ 6 * logBits (q * m * n) := by
  have hL : 1 ≤ logBits (q * m * n) := by
    have h := one_le_logBits_mul (a := q) (b := m * n) hq (Nat.mul_pos hm hn)
    simpa [Nat.mul_assoc] using h
  have hmnL : logBits (m * n) ≤ logBits (q * m * n) := by
    apply logBits_mono
    calc m * n = 1 * (m * n) := (one_mul _).symm
      _ ≤ q * (m * n) := Nat.mul_le_mul_right _ hq
      _ = q * m * n := by ring
  unfold perEntryCommBits
  omega

/-- **Proposition 18, `O_C` cost (p. 14).**  `2(2 log m + log n) ≤ 6 log(qmn)`: a single
column query also costs `O(log(mn))` qubits — this is the paper's observation that `O_C`
needs `2(2 log m + log n)` bits, still `O(log(mn))`. -/
theorem perColumnCommBits_le_six (m n q : ℕ) (hm : 0 < m) (hn : 0 < n) (hq : 0 < q) :
    perColumnCommBits m n ≤ 6 * logBits (q * m * n) := by
  have hL : 1 ≤ logBits (q * m * n) := by
    have h := one_le_logBits_mul (a := q) (b := m * n) hq (Nat.mul_pos hm hn)
    simpa [Nat.mul_assoc] using h
  have hmL : logBits m ≤ logBits (q * m * n) := by
    apply logBits_mono
    calc m = 1 * m := (one_mul m).symm
      _ ≤ q * m := Nat.mul_le_mul_right m hq
      _ ≤ q * m * n := Nat.le_mul_of_pos_right (q * m) hn
  have hnL : logBits n ≤ logBits (q * m * n) := by
    apply logBits_mono
    calc n = 1 * n := (one_mul n).symm
      _ ≤ m * n := Nat.mul_le_mul_right n hm
      _ ≤ q * m * n := by
          calc m * n ≤ q * (m * n) := Nat.le_mul_of_pos_left (m * n) hq
            _ = q * m * n := by ring
  unfold perColumnCommBits
  omega

/-- **Proposition 18, `k` players (p. 14).**  With `k` players and a coordinator, one
coordinated oracle use costs `O(k log(mn))`. -/
theorem perPlayerCommBits_le (k m n q : ℕ) (hm : 0 < m) (hn : 0 < n) (hq : 0 < q) :
    k * perEntryCommBits m n ≤ 6 * k * logBits (q * m * n) := by
  have h := perEntryCommBits_le_six m n q hm hn hq
  calc k * perEntryCommBits m n ≤ k * (6 * logBits (q * m * n)) :=
        Nat.mul_le_mul_left k h
    _ = 6 * k * logBits (q * m * n) := by ring

/-! ## §2. Proposition 19: composing block-encodings -/

/-- The block-encoding parameter `√(α₁² + α₂²)` obtained by composing two
`(α_i, 1, 0)`-block-encodings (Proposition 19, p. 14). -/
def blockEncParam (α₁ α₂ : ℝ) : ℝ := Real.sqrt (α₁ ^ 2 + α₂ ^ 2)

/-- The composed block-encoding parameter is nonnegative. -/
theorem blockEncParam_nonneg (α₁ α₂ : ℝ) : 0 ≤ blockEncParam α₁ α₂ :=
  Real.sqrt_nonneg _

/-- **Proposition 19, amplification factor (p. 14).**  `(√(α₁²+α₂²))² = α₁² + α₂²`. -/
theorem blockEncParam_sq (α₁ α₂ : ℝ) : blockEncParam α₁ α₂ ^ 2 = α₁ ^ 2 + α₂ ^ 2 := by
  unfold blockEncParam
  rw [Real.sq_sqrt (by positivity)]

/-- **Proposition 19, dominance (p. 14).**  Each individual block-encoding parameter is
dominated: `α₁ ≤ √(α₁² + α₂²)` for `α₁ ≥ 0` — the composed encoding has parameter `2` in
the paper (`(α_i, 1, 0)` composed gives `(·, 2, 0)`). -/
theorem blockEncParam_ge_left {α₁ α₂ : ℝ} (h : 0 ≤ α₁) : α₁ ≤ blockEncParam α₁ α₂ := by
  unfold blockEncParam
  calc α₁ = Real.sqrt (α₁ ^ 2) := (Real.sqrt_sq h).symm
    _ ≤ Real.sqrt (α₁ ^ 2 + α₂ ^ 2) := by
        rw [Real.sqrt_le_sqrt_iff (by positivity)]
        nlinarith [sq_nonneg α₂, Real.sq_sqrt (x := α₁ ^ 2) (by positivity)]

/-- Qubits for one use of the composed block-encoding (`O(log(mn))`, Proposition 19). -/
def blockEncCommBits (m n : ℕ) : ℕ := 2 * logBits (m * n)

/-- One composed block-encoding query costs at most `6 log(qmn)` bits. -/
theorem blockEncCommBits_le_six (m n q : ℕ) (hm : 0 < m) (hn : 0 < n) (hq : 0 < q) :
    blockEncCommBits m n ≤ 6 * logBits (q * m * n) := by
  unfold blockEncCommBits
  exact perEntryCommBits_le_six m n q hm hn hq

/-! ## §3. Theorem 20: `T` oracle uses give `O(T log(mn))`-qubit protocols -/

/-- Total qubits for `T` uses of one of the oracles/block-encodings in a quantum protocol
(Theorem 20, p. 14). -/
def quantumProtocolBits (T m n : ℕ) : ℕ := T * perEntryCommBits m n

/-- **Theorem 20 (p. 14).**  A quantum algorithm with `O(T)` oracle uses gives a protocol
with `2T log(mn) ≤ 6T log(qmn)` qubits, i.e. complexity `O(T log(mn))`. -/
theorem quantumProtocolBits_le_six (T m n q : ℕ) (hm : 0 < m) (hn : 0 < n) (hq : 0 < q) :
    quantumProtocolBits T m n ≤ 6 * T * logBits (q * m * n) := by
  unfold quantumProtocolBits
  calc T * perEntryCommBits m n ≤ T * (6 * logBits (q * m * n)) :=
        Nat.mul_le_mul_left T (perEntryCommBits_le_six m n q hm hn hq)
    _ = 6 * T * logBits (q * m * n) := by ring

/-- **Theorem 20, lower-bound transfer (p. 14).**  If a task needs communication `hard`
and a quantum algorithm with `T` oracle calls yields a protocol whose communication is at
most `C · (quantum protocol bits)`, then `hard ≤ 6C·T·log(qmn)`: the quantum query/block
encoding complexity is at least `Ω(hard / log(mn))`. -/
theorem quantum_lower_of_comm_bound (hard C : ℝ) (T m n q : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hq : 0 < q) (hC : 0 ≤ C)
    (h : hard ≤ C * (quantumProtocolBits T m n : ℝ)) :
    hard ≤ C * (6 * (T : ℝ) * (logBits (q * m * n) : ℝ)) := by
  have hb := quantumProtocolBits_le_six T m n q hm hn hq
  have hb' : ((quantumProtocolBits T m n : ℕ) : ℝ) ≤ 6 * (T : ℝ) * (logBits (q * m * n) : ℝ) := by
    exact_mod_cast hb
  calc hard ≤ C * (quantumProtocolBits T m n : ℝ) := h
    _ ≤ C * (6 * (T : ℝ) * (logBits (q * m * n) : ℝ)) :=
        mul_le_mul_of_nonneg_left hb' hC

end Qatlib.Papers.QInspired25.MainResults.Quantum
