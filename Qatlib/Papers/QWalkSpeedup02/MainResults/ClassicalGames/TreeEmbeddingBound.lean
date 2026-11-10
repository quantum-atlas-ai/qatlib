/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpeedup02.MainResults.Common.FiniteProbability
import Qatlib.Papers.QWalkSpeedup02.MainResults.Common.RpowArith
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QWalkSpeedup02.MainResults.ClassicalGames.TreeEmbeddingBound

open Qatlib.Papers.QWalkSpeedup02.MainResults.Common.FiniteProbability
open Qatlib.Papers.QWalkSpeedup02.MainResults.Common.RpowArith

lemma lemma8_term1 (n t : ℕ) (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 6))
    (ht0 : (0 : ℝ) ≤ (t : ℝ)) :
    (t : ℝ) ^ 2 * (2 : ℝ) ^ (-((n : ℝ) / 2)) ≤ (2 : ℝ) ^ (-((n : ℝ) / 6)) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) / 2)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hsq : (t : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((n : ℝ) / 6)) ^ 2 :=
    pow_le_pow_left₀ ht0 ht 2
  calc (t : ℝ) ^ 2 * (2 : ℝ) ^ (-((n : ℝ) / 2))
      ≤ ((2 : ℝ) ^ ((n : ℝ) / 6)) ^ 2 * (2 : ℝ) ^ (-((n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hsq h2.le
    _ = (2 : ℝ) ^ ((n : ℝ) / 3) * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
        rw [sq_two_rpow_sixth]
    _ = (2 : ℝ) ^ ((n : ℝ) / 3 + -((n : ℝ) / 2)) := by rw [two_rpow_add]
    _ = (2 : ℝ) ^ (-((n : ℝ) / 6)) := by
        rw [show (n : ℝ) / 3 + -((n : ℝ) / 2) = -((n : ℝ) / 6) by ring]

lemma lemma8_term2 (n t : ℕ) (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 6))
    (ht0 : (0 : ℝ) ≤ (t : ℝ)) :
    (t : ℝ) ^ 2 * (2 : ℝ) ^ (1 - (n : ℝ) / 2) ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) / 6)) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 - (n : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hsq : (t : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((n : ℝ) / 6)) ^ 2 :=
    pow_le_pow_left₀ ht0 ht 2
  calc (t : ℝ) ^ 2 * (2 : ℝ) ^ (1 - (n : ℝ) / 2)
      ≤ ((2 : ℝ) ^ ((n : ℝ) / 6)) ^ 2 * (2 : ℝ) ^ (1 - (n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hsq h2.le
    _ = (2 : ℝ) ^ ((n : ℝ) / 3) * (2 : ℝ) ^ (1 - (n : ℝ) / 2) := by
        rw [sq_two_rpow_sixth]
    _ = (2 : ℝ) ^ ((n : ℝ) / 3 + (1 - (n : ℝ) / 2)) := by rw [two_rpow_add]
    _ = (2 : ℝ) ^ (1 + -((n : ℝ) / 6)) := by
        rw [show (n : ℝ) / 3 + (1 - (n : ℝ) / 2) = 1 + -((n : ℝ) / 6) by ring]
    _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) / 6)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = 2 * (2 : ℝ) ^ (-((n : ℝ) / 6)) := by rw [Real.rpow_one]

theorem lemma8_tree_embedding_bound
    {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (n t : ℕ) (_hn : 1 ≤ n)
    (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 6))
    (win : Ω → Prop) [DecidablePred win]
    (hbound : P.eventMass win ≤
      (t : ℝ) ^ 2 * (2 : ℝ) ^ (-((n : ℝ) / 2)) +
        (t : ℝ) ^ 2 * (2 : ℝ) ^ (1 - (n : ℝ) / 2)) :
    P.eventMass win ≤ 3 * (2 : ℝ) ^ (-((n : ℝ) / 6)) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have h1 := lemma8_term1 n t ht ht0
  have h2 := lemma8_term2 n t ht ht0
  linarith

end Qatlib.Papers.QWalkSpeedup02.MainResults.ClassicalGames.TreeEmbeddingBound
