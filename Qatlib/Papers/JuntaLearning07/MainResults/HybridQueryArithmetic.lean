/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

structure HybridLearner where

  classicalQueries : ℕ

  quantumQueries : ℕ

def simulatedQMQQueries (H : HybridLearner) : ℕ :=
  H.classicalQueries + H.quantumQueries

@[simp] theorem simulatedQMQQueries_eq (H : HybridLearner) :
    simulatedQMQQueries H = H.classicalQueries + H.quantumQueries := rfl

theorem observation_iv8_arithmetic {M c q : ℕ}
    (hfact : (M : ℝ) / 100 ≤ (c : ℝ) + (q : ℝ))
    (hc : (c : ℝ) ≤ (M : ℝ) / 101) :
    (M : ℝ) / 10100 ≤ (q : ℝ) := by
  have hsplit : (M : ℝ) / 100 - (M : ℝ) / 101 = (M : ℝ) / 10100 := by
    field_simp
    ring
  linarith

theorem hybrid_quantum_queries_ge {Q c q : ℕ}
    (hfact : (Q : ℝ) ≤ (c : ℝ) + (q : ℝ)) :
    (Q : ℝ) - (c : ℝ) ≤ (q : ℝ) := by
  linarith

theorem observation_iv8_contrapositive {M c q : ℕ}
    (hfact : (M : ℝ) / 100 ≤ (c : ℝ) + (q : ℝ))
    (hq : (q : ℝ) < (M : ℝ) / 10100) :
    (M : ℝ) / 101 < (c : ℝ) := by
  have hsplit : (M : ℝ) / 100 - (M : ℝ) / 10100 = (M : ℝ) / 101 := by
    field_simp
    ring
  linarith

end Qatlib.Papers.JuntaLearning07.MainResults
