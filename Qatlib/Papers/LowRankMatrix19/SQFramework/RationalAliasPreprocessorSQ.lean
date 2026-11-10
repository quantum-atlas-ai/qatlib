/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SqEstimation.AliasPreprocess
import Qatlib.Papers.LowRankMatrix19.SQFramework.SqClosureEstimation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.SqEstimation.AliasPreprocess

set_option autoImplicit false
namespace Qatlib.Papers.LowRankMatrix19.SQFramework
open Qatlib.Papers.LowRankMatrix19.SQFramework.ConstructionStageB.StageBSQCLOSUREESTIMATION
open scoped BigOperators

theorem aliasTable_dist_real {n : ℕ} (u : Fin n → ℕ) (hU : 0 < aliasTotal u) (k : Fin n) :
    ((aliasDist (aliasTable u) (aliasTotal u) k : ℚ) : ℝ)
      = (aliasLaw u (aliasTotal u) hU rfl).prob k := by
  change ((aliasDist (aliasTable u) (aliasWeightTotal u) k : ℚ) : ℝ) = _
  rw [aliasTable_dist u hU k, aliasLaw_prob u (aliasTotal u) hU rfl k]
  push_cast
  rfl

def aliasPreprocessRam (n : ℕ) : ℕ := n + 2 * n

theorem aliasPreprocessRam_eq (n : ℕ) : aliasPreprocessRam n = 3 * n := by
  simp only [aliasPreprocessRam]; omega

theorem alias_preprocess_ram_le (n : ℕ) : aliasPreprocessRam n ≤ 3 * n := by
  simp only [aliasPreprocessRam]; omega

theorem aliasTable_preprocess_ram {n : ℕ} (u : Fin n → ℕ) :
    n + 2 * (aliasTable u).steps ≤ aliasPreprocessRam n := by
  have := aliasTable_steps_le u
  simp only [aliasPreprocessRam]
  omega

theorem aliasTable_total_ram {n : ℕ} (u : Fin n → ℕ) (q : ℕ) :
    n + 2 * (aliasTable u).steps + q * aliasDrawCost ≤ 3 * n + q := by
  have := aliasTable_steps_le u
  rw [alias_draw_cost]
  omega

theorem aliasTable_auxSpace_le {n : ℕ} (u : Fin n → ℕ) : pendCount (aliasTable u) ≤ n := by
  have := aliasTable_pend_eq u
  omega

theorem alias_space_eq (n : ℕ) : n + n + n = 3 * aliasSpaceCost n := by
  rw [alias_space_cost]; omega

theorem alias_amortize_iff (n q : ℕ) :
    (aliasPreprocessRam n ≤ q * aliasDrawCost) ↔ (3 * n ≤ q) := by
  simp only [aliasPreprocessRam, alias_draw_cost]
  omega

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

theorem ramPreprocess_sqLaw {n : ℕ} (input : WordArray n ℕ) (m : AliasRAM n)
    (hU : 0 < aliasWeightTotal (wordRead input)) (k : Fin n) :
    (ramDrawLaw (ramPreprocess input m) (positive_input_size input hU) hU).prob (some k) =
      (aliasLaw (wordRead input) (aliasWeightTotal (wordRead input)) hU rfl).prob k := by
  rw [ramDrawLaw_preprocessed, aliasLaw_prob]

end Qatlib.Papers.LowRankMatrix19.SQFramework
