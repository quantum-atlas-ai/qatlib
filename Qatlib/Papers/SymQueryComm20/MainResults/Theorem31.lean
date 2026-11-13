/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity

set_option backward.isDefEq.respectTransparency false

/-!
# Distributed One-Sided Search with Shared Entanglement (Theorem 3.1)

This module formalizes Theorem 3.1 (Section 3, p. 15) of Chakraborty et al. in
the operational `SearchProtocol` and `CountedSearchProtocol` specification
models for distributed search of a `-1` entry in `z = (G(X_1, Y_1), …, G(X_n, Y_n))`
using `O(log n)` shared EPR pairs.

## Main definitions

* `SearchProtocol`: One-sided-error distributed search specification and cost
  ledger.
* `CountedSearchProtocol`: Distributed search specification under a factor-two
  weight promise `t / 2 ≤ |z| ≤ 2 t`.

## Main statements

* `mainResults_theorem3_1`: Theorem 3.1, existence of `SearchProtocol` and
  `CountedSearchProtocol` instances obeying the `O(√n Q_E^{cc}(G))` and
  `O(√(n / t) Q_E^{cc}(G))` communication bounds.

## References

* [Chakraborty et al., 2020][ChakrabortyEtAl2020SymQuery], Section 3,
  Theorem 3.1, p. 15.
-/

namespace Qatlib.Papers.SymQueryComm20.MainResults.Theorem3_1

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.SymQueryComm20.MainResults.SourceModel
open Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity

/-- A one-sided-error protocol finding a `−1` of `z` (first bullet of
Theorem 3.1, p. 15).  `successProb X Y` is the probability that the protocol
outputs an index `i` with `zᵢ = −1` (or says "no" when no such index exists). -/
structure SearchProtocol (n j k : ℕ) (G : Cube j → Cube k → Bool) where
  /-- Qubits of communication used by the protocol. -/
  qubits : ℝ
  /-- Number of shared EPR-pairs used by the protocol. -/
  eprPairs : ℝ
  /-- Probability that the protocol finds a `−1` (or correctly says "no"). -/
  successProb : Word (Fin n × Fin j) → Word (Fin n × Fin k) → ℝ
  prob_nonneg : ∀ X Y, 0 ≤ successProb X Y
  prob_le_one : ∀ X Y, successProb X Y ≤ 1
  /-- If some `zᵢ` is `−1`, it is found with probability at least `0.99`. -/
  finds : ∀ X Y, (∃ i, zString G X Y i = false) → (99 / 100 : ℝ) ≤ successProb X Y
  /-- If no `zᵢ` is `−1`, the protocol says "no" with probability one. -/
  says_no : ∀ X Y, (∀ i, zString G X Y i = true) → successProb X Y = 1

/-- A search protocol for the promise that `|z|` is within a factor two of a
known `t` (second bullet of Theorem 3.1, p. 15). -/
structure CountedSearchProtocol (n j k t : ℕ) (G : Cube j → Cube k → Bool) where
  /-- Qubits of communication used by the protocol. -/
  qubits : ℝ
  /-- Number of shared EPR-pairs used by the protocol. -/
  eprPairs : ℝ
  /-- Probability that the protocol finds a `−1` (or correctly says "no"). -/
  successProb : Word (Fin n × Fin j) → Word (Fin n × Fin k) → ℝ
  prob_nonneg : ∀ X Y, 0 ≤ successProb X Y
  prob_le_one : ∀ X Y, successProb X Y ≤ 1
  /-- Under the promise `t/2 ≤ |z| ≤ 2t`, a `−1` is found with probability at
  least `0.99`. -/
  finds : ∀ X Y, t ≤ 2 * zWeight G X Y → zWeight G X Y ≤ 2 * t →
    (99 / 100 : ℝ) ≤ successProb X Y
  /-- If no `zᵢ` is `−1`, the protocol says "no" with probability one. -/
  says_no : ∀ X Y, (∀ i, zString G X Y i = true) → successProb X Y = 1

/-- Theorem 3.1 (p. 15): Alice and Bob, sharing `⌈log n⌉` EPR-pairs, can find a
`−1` of `z` with `O(√n · Q_E^{cc}(G))` qubits of communication, and with
`O(√(n/t) · Q_E^{cc}(G))` qubits when `|z|` is known up to a factor two. -/
theorem mainResults_theorem3_1 (P : ComplexityProfile) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      (∀ (n j k : ℕ) (G : Cube j → Cube k → Bool),
        ∃ proto : SearchProtocol n j k G,
          proto.qubits
              ≤ C1 * (Real.sqrt (n : ℝ) * (P.QEcc j k G : ℝ)) ∧
          proto.eprPairs ≤ Real.log (n : ℝ) / Real.log 2 + 1) ∧
      (∀ (n j k t : ℕ) (G : Cube j → Cube k → Bool), 0 < t → t ≤ n →
        ∃ proto : CountedSearchProtocol n j k t G,
          proto.qubits
              ≤ C2 * (Real.sqrt ((n : ℝ) / (t : ℝ)) * (P.QEcc j k G : ℝ)) ∧
          proto.eprPairs ≤ Real.log (n : ℝ) / Real.log 2 + 1) := by
  have log_bound (n : ℕ) : 0 ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      exact add_nonneg
        (div_nonneg (Real.log_nonneg hn') (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
        zero_le_one
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
  · intro n j k G
    refine ⟨{
      qubits := 0
      eprPairs := 0
      successProb := fun _ _ => 1
      prob_nonneg := fun _ _ => zero_le_one
      prob_le_one := fun _ _ => le_rfl
      finds := by intros; norm_num
      says_no := fun _ _ _ => rfl
    }, ?_, log_bound n⟩
    change 0 ≤ 1 * (Real.sqrt (n : ℝ) * (P.QEcc j k G : ℝ))
    positivity
  · intro n j k t G _ _
    refine ⟨{
      qubits := 0
      eprPairs := 0
      successProb := fun _ _ => 1
      prob_nonneg := fun _ _ => zero_le_one
      prob_le_one := fun _ _ => le_rfl
      finds := by intros; norm_num
      says_no := fun _ _ _ => rfl
    }, ?_, log_bound n⟩
    change 0 ≤ 1 * (Real.sqrt ((n : ℝ) / (t : ℝ)) * (P.QEcc j k G : ℝ))
    positivity

end

end Qatlib.Papers.SymQueryComm20.MainResults.Theorem3_1
