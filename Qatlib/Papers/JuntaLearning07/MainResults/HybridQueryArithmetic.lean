/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Arithmetic for hybrid membership-query budgets

`HybridLearner` records classical and quantum query counts, and `simulatedQMQQueries` adds them.
The module derives lower bounds on the quantum count from assumed lower bounds on the total and
upper bounds on the classical count, including the arithmetic constants in Observation IV.8. See
[AticiServedio2007].

## Main statements

* `observation_iv8_arithmetic`: If c + q ≥ M/100 and c ≤ M/101, then q ≥ M/10100, with the
  natural counts viewed as real numbers.
* `observation_iv8_contrapositive`: If c + q ≥ M/100 but q < M/10100, then c > M/101, with the
  counts viewed as real numbers.

## References

* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

/-- A pair of natural counts for classical and quantum queries. -/
structure HybridLearner where

  classicalQueries : ℕ

  quantumQueries : ℕ

/-- The sum of the classical and quantum query counts of a hybrid learner. -/
def simulatedQMQQueries (H : HybridLearner) : ℕ :=
  H.classicalQueries + H.quantumQueries

/-- The simulated quantum query count equals the classical count plus the quantum count; see
[AticiServedio2007]. -/
@[simp] theorem simulatedQMQQueries_eq (H : HybridLearner) :
    simulatedQMQQueries H = H.classicalQueries + H.quantumQueries := rfl

/-- If c + q ≥ M/100 and c ≤ M/101, then q ≥ M/10100, with the natural counts viewed as real
numbers; see [AticiServedio2007]. -/
theorem observation_iv8_arithmetic {M c q : ℕ}
    (hfact : (M : ℝ) / 100 ≤ (c : ℝ) + (q : ℝ))
    (hc : (c : ℝ) ≤ (M : ℝ) / 101) :
    (M : ℝ) / 10100 ≤ (q : ℝ) := by
  have hsplit : (M : ℝ) / 100 - (M : ℝ) / 101 = (M : ℝ) / 10100 := by
    field_simp
    ring
  linarith

/-- A lower bound Q ≤ c + q implies the quantum-count bound Q − c ≤ q after casting the counts
to the reals; see [AticiServedio2007]. -/
theorem hybrid_quantum_queries_ge {Q c q : ℕ}
    (hfact : (Q : ℝ) ≤ (c : ℝ) + (q : ℝ)) :
    (Q : ℝ) - (c : ℝ) ≤ (q : ℝ) := by
  linarith

/-- If c + q ≥ M/100 but q < M/10100, then c > M/101, with the counts viewed as real numbers;
see [AticiServedio2007]. -/
theorem observation_iv8_contrapositive {M c q : ℕ}
    (hfact : (M : ℝ) / 100 ≤ (c : ℝ) + (q : ℝ))
    (hq : (q : ℝ) < (M : ℝ) / 10100) :
    (M : ℝ) / 101 < (c : ℝ) := by
  have hsplit : (M : ℝ) / 100 - (M : ℝ) / 10100 = (M : ℝ) / 101 := by
    field_simp
    ring
  linarith

end Qatlib.Papers.JuntaLearning07.MainResults
