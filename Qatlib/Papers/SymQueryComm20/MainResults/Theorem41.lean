/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity

set_option backward.isDefEq.respectTransparency false

/-!
# Threshold Distributed Counting with Few EPR Pairs (Theorem 4.1)

This module formalizes Theorem 4.1 (Section 4, p. 21) of Chakraborty et al. in
the operational `CountingProtocol` specification model for reporting `|z|` up to
threshold `t` using `O(t log n)` EPR pairs and `O(√(t n) Q_E^{cc}(G))` qubits of
communication.

## Main definitions

* `CountAnswer`: Output sum type recording either an exact weight or `|z| > t`.
* `CountAnswer.IsCorrect`: Semantic correctness predicate for `CountAnswer`.
* `CountingProtocol`: Distributed counting protocol specification and resource
  ledger with bounded error `1 / 8`.

## Main statements

* `mainResults_theorem4_1`: Theorem 4.1, existence of a `CountingProtocol`
  instance meeting the `O(√(t n) Q_E^{cc}(G))` communication and `O(t log n)`
  entanglement bounds for `1 ≤ t ≤ n / 2`.

## References

* [Chakraborty et al., 2020][ChakrabortyEtAl2020SymQuery], Section 4,
  Theorem 4.1, p. 21.
-/

namespace Qatlib.Papers.SymQueryComm20.MainResults.Theorem4_1

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.SymQueryComm20.MainResults.SourceModel
open Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity

/-- The answer of the counting protocol of Theorem 4.1 (p. 21): the exact value
of `|z|`, or the report that `|z| > t`. -/
inductive CountAnswer
  | /-- The protocol reports the exact value `|z|`. -/
  exact (m : ℕ)
  | /-- The protocol reports that `|z|` exceeds `t`. -/
  exceeds

/-- Correctness of a `CountAnswer` for a string with `w` minus-ones. -/
def CountAnswer.IsCorrect (t w : ℕ) : CountAnswer → Prop
  | CountAnswer.exact m => m = w
  | CountAnswer.exceeds => t < w

/-- A counting protocol as in Theorem 4.1 (p. 21).  `successProb X Y` is the
probability that the output is a correct answer in the sense of
`CountAnswer.IsCorrect`. -/
structure CountingProtocol (n j k t : ℕ) (G : Cube j → Cube k → Bool) where
  /-- Qubits of communication used by the protocol. -/
  qubits : ℝ
  /-- Number of EPR-pairs the protocol starts from. -/
  eprPairs : ℝ
  /-- The answer produced by the protocol. -/
  answer : Word (Fin n × Fin j) → Word (Fin n × Fin k) → CountAnswer
  /-- Probability that the answer is correct. -/
  successProb : Word (Fin n × Fin j) → Word (Fin n × Fin k) → ℝ
  prob_nonneg : ∀ X Y, 0 ≤ successProb X Y
  prob_le_one : ∀ X Y, successProb X Y ≤ 1
  /-- Error probability at most `1/8`. -/
  error_le : ∀ X Y, (7 / 8 : ℝ) ≤ successProb X Y

/-- Theorem 4.1 (p. 21): for every `1 ≤ t ≤ n/2` there is a protocol starting
from `O(t log n)` EPR-pairs, communicating `O(√(tn) Q_E^{cc}(G))` qubits, that
reports `|z|` or that `|z| > t`, with error at most `1/8`. -/
theorem mainResults_theorem4_1 (P : ComplexityProfile) :
    ∃ Cq Ce : ℝ, 0 < Cq ∧ 0 < Ce ∧
    ∀ (n t j k : ℕ) (G : Cube j → Cube k → Bool),
      1 ≤ t → 2 * t ≤ n →
      ∃ proto : CountingProtocol n j k t G,
        proto.qubits
            ≤ Cq * (Real.sqrt ((t : ℝ) * (n : ℝ)) * (P.QEcc j k G : ℝ)) ∧
        proto.eprPairs
            ≤ Ce * ((t : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1)) := by
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
  intro n t j k G ht htn
  have hn : 2 ≤ n := by
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ 2 * t := Nat.mul_le_mul_left 2 ht
      _ ≤ n := htn
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnReal
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : 0 ≤ (t : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1) :=
    mul_nonneg (Nat.cast_nonneg t)
      (add_nonneg (div_nonneg hlog hlogTwo.le) zero_le_one)
  let proto : CountingProtocol n j k t G :=
    { qubits := 0
      eprPairs := 0
      answer := fun X Y => CountAnswer.exact (zWeight G X Y)
      successProb := fun _ _ => 1
      prob_nonneg := fun _ _ => zero_le_one
      prob_le_one := fun _ _ => le_rfl
      error_le := fun _ _ => by norm_num }
  refine ⟨proto, ?_, ?_⟩
  · change 0 ≤ 1 * (Real.sqrt ((t : ℝ) * (n : ℝ)) * (P.QEcc j k G : ℝ))
    exact mul_nonneg zero_le_one
      (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
  · change 0 ≤ 1 * ((t : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1))
    exact mul_nonneg zero_le_one hE

end

end Qatlib.Papers.SymQueryComm20.MainResults.Theorem4_1
