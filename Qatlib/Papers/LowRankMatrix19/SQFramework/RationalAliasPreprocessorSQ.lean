/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SqEstimation.AliasPreprocess
import Qatlib.Papers.LowRankMatrix19.SQFramework.SqClosureEstimation

/-!
# Rational alias preprocessing for sample/query access

This module connects the rational alias-table distribution with the real-valued law `aliasLaw`.
It packages distribution correctness, linear preprocessing and space accounting, constant-cost
draws, and the RAM implementation into `AliasFrontier` for the sample/query setting of
[ChiaEtAl2022].

## Main statements

* `frontier1`: Constructs the alias-table correctness and resource-accounting record.
* `ramPreprocess_sqLaw`: Identifies the output law of RAM preprocessing with the normalized
  input weights.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SqEstimation.AliasPreprocess

set_option autoImplicit false
namespace Qatlib.Papers.LowRankMatrix19.SQFramework
open Qatlib.Papers.LowRankMatrix19.SQFramework.ConstructionStageB.StageBSQCLOSUREESTIMATION
open scoped BigOperators

/-- For positive total input weight, casting the alias table's rational output probability to
the reals gives the corresponding probability in `aliasLaw`. -/
theorem aliasTable_dist_real {n : ℕ} (u : Fin n → ℕ) (hU : 0 < aliasTotal u) (k : Fin n) :
    ((aliasDist (aliasTable u) (aliasTotal u) k : ℚ) : ℝ)
      = (aliasLaw u (aliasTotal u) hU rfl).prob k := by
  change ((aliasDist (aliasTable u) (aliasWeightTotal u) k : ℚ) : ℝ) = _
  rw [aliasTable_dist u hU k, aliasLaw_prob u (aliasTotal u) hU rfl k]
  push_cast
  rfl

/-- The alias preprocessing RAM budget `n + 2 * n`. -/
def aliasPreprocessRam (n : ℕ) : ℕ := n + 2 * n

/-- The alias preprocessing RAM budget equals `3 * n`. -/
theorem aliasPreprocessRam_eq (n : ℕ) : aliasPreprocessRam n = 3 * n := by
  simp only [aliasPreprocessRam]; omega

/-- The alias preprocessing RAM budget is at most `3 * n`. -/
theorem alias_preprocess_ram_le (n : ℕ) : aliasPreprocessRam n ≤ 3 * n := by
  simp only [aliasPreprocessRam]; omega

/-- The table's initialization cost plus twice its number of preprocessing steps is bounded by
`aliasPreprocessRam n`. -/
theorem aliasTable_preprocess_ram {n : ℕ} (u : Fin n → ℕ) :
    n + 2 * (aliasTable u).steps ≤ aliasPreprocessRam n := by
  have := aliasTable_steps_le u
  simp only [aliasPreprocessRam]
  omega

/-- Preprocessing the alias table and performing `q` draws costs at most `3 * n + q` in the
stated RAM accounting. -/
theorem aliasTable_total_ram {n : ℕ} (u : Fin n → ℕ) (q : ℕ) :
    n + 2 * (aliasTable u).steps + q * aliasDrawCost ≤ 3 * n + q := by
  have := aliasTable_steps_le u
  rw [alias_draw_cost]
  omega

/-- The number of pending entries in the preprocessed alias table is at most the input size `n`. -/
theorem aliasTable_auxSpace_le {n : ℕ} (u : Fin n → ℕ) : pendCount (aliasTable u) ≤ n := by
  have := aliasTable_pend_eq u
  omega

/-- The sum of three length-`n` storage components equals three times `aliasSpaceCost n`. -/
theorem alias_space_eq (n : ℕ) : n + n + n = 3 * aliasSpaceCost n := by
  rw [alias_space_cost]; omega

/-- The RAM preprocessing budget is at most the cost of `q` draws exactly when `3 * n ≤ q`. -/
theorem alias_amortize_iff (n q : ℕ) :
    (aliasPreprocessRam n ≤ q * aliasDrawCost) ↔ (3 * n ≤ q) := by
  simp only [aliasPreprocessRam, alias_draw_cost]
  omega

/-- A record of positive total weight, completed preprocessing, exact distribution and weight
accounting, and the stated step, RAM, space, and amortization bounds for an alias table. -/
structure AliasFrontier (n : ℕ) (u : Fin n → ℕ) where
  hU : 0 < aliasTotal u
  built : (aliasTable u).small = []
  steps_le : (aliasTable u).steps ≤ n
  pend_eq : pendCount (aliasTable u) + (aliasTable u).steps = n
  dequeue_le : 2 * (aliasTable u).steps ≤ 2 * n
  accounting : ∀ k : Fin n, (aliasTable u).qN k + ∑ i ∈ Finset.univ.filter
      (fun i => i ≠ k ∧ (aliasTable u).al i = k),
      (aliasTotal u - (aliasTable u).qN i) = n * u k
  dist_eq : ∀ k : Fin n,
      aliasDist (aliasTable u) (aliasTotal u) k = ((u k : ℕ) : ℚ) / aliasTotal u
  dist_aliasLaw : ∀ k : Fin n, ((aliasDist (aliasTable u) (aliasTotal u) k : ℚ) : ℝ)
      = (aliasLaw u (aliasTotal u) hU rfl).prob k
  ram_le : n + 2 * (aliasTable u).steps ≤ aliasPreprocessRam n
  total_le : ∀ q : ℕ, n + 2 * (aliasTable u).steps + q * aliasDrawCost ≤ 3 * n + q
  auxSpace_le : pendCount (aliasTable u) ≤ n
  space_eq : n + n + n = 3 * aliasSpaceCost n
  amortize_iff : ∀ q : ℕ, (aliasPreprocessRam n ≤ q * aliasDrawCost) ↔ (3 * n ≤ q)

/-- For any natural-weight vector with positive total weight, the constructed alias table
satisfies all correctness and resource bounds in `AliasFrontier`. -/
theorem frontier1 {n : ℕ} (u : Fin n → ℕ) (hU : 0 < aliasTotal u) : AliasFrontier n u where
  hU := hU
  built := aliasTable_small_empty u
  steps_le := aliasTable_steps_le u
  pend_eq := aliasTable_pend_eq u
  dequeue_le := Nat.mul_le_mul_left 2 (aliasTable_steps_le u)
  accounting := aliasTable_accounting u
  dist_eq := aliasTable_dist u hU
  dist_aliasLaw := aliasTable_dist_real u hU
  ram_le := aliasTable_preprocess_ram u
  total_le := aliasTable_total_ram u
  auxSpace_le := aliasTable_auxSpace_le u
  space_eq := alias_space_eq n
  amortize_iff := alias_amortize_iff n

/-- For positive total input weight, the probability of output `some k` after RAM alias
preprocessing equals the normalized input-weight probability in `aliasLaw`. -/
theorem ramPreprocess_sqLaw {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n)
    (hU : 0 < aliasWeightTotal (wordRead input)) (k : Fin n) :
    (ramDrawLaw (ramPreprocess input m) (positive_input_size input hU) hU).prob (some k) =
      (aliasLaw (wordRead input) (aliasWeightTotal (wordRead input)) hU rfl).prob k := by
  rw [ramDrawLaw_preprocessed, aliasLaw_prob]

end Qatlib.Papers.LowRankMatrix19.SQFramework
