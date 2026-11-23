module

import Qatlib.Papers.LearnGraphDis12.LearningFlows.SymmetricStage
import Qatlib.Papers.LearnGraphDis12.MainResults.FaultFreeBranch
import Qatlib.Papers.LearnGraphDis12.MainResults.FixedErrorQueryCost
import Qatlib.Papers.LearnGraphDis12.MainResults.IntegerStageSize
import Mathlib.Tactic.NormNum

/-! # Ordinary-module consumers of the learning-graph bounds -/

open Qatlib.Papers.LearnGraphDis12.LearningFlows
open Qatlib.Papers.LearnGraphDis12.MainResults
open Qatlib.Papers.LearnGraphDis12.MainResults.QueryCost
open scoped BigOperators

/-- Two inputs use different transitions. A single weight balances the costs of
both, with two arc occurrences per transition. -/
example :
    ∃ w : ℝ, 0 < w ∧
      ‖(WithLp.toLp 2 fun _ : Fin 2 × Fin 2 => Real.sqrt w :
        EuclideanSpace ℝ (Fin 2 × Fin 2))‖ ^ 2 = 2 * Real.sqrt 2 ∧
      ∀ x : Fin 2,
        ‖(WithLp.toLp 2 fun a : Fin 2 × Fin 2 =>
          (if a.1 = x then 1 else 0) / Real.sqrt w :
          EuclideanSpace ℝ (Fin 2 × Fin 2))‖ ^ 2 = 2 * Real.sqrt 2 := by
  let p (x t : Fin 2) : ℝ := if t = x then 1 else 0
  have hunit (x : Fin 2) : ∑ t, p x t = 1 := by
    simp [p, Finset.sum_ite_eq']
  have hsym (x t : Fin 2) : p x t = 0 ∨ p x t = 1 := by
    by_cases h : t = x <;> simp [p, h]
  obtain ⟨τ, w, _, hw, _, _, hnegative, hpositive⟩ :=
    symmetric_stage_balanced_cost 2 (by decide) p 1 (by norm_num) hunit hsym
  have hτ : τ = 2 := by
    have hcard := symmetric_flow_support_card (p 0) 1 (hunit 0) (hsym 0)
    rw [mul_one] at hcard
    simp [(hpositive 0).1, hcard]
  subst τ
  exact ⟨w, hw, hnegative, fun x => (hpositive x).2⟩

/-- A setup size is available even at the smallest admitted graph size and the
largest possible independence number there. -/
example : ∃ r : ℕ, 1 ≤ r ∧ r + 2 ≤ 4 ∧
    (r : ℝ) + 4 / Real.sqrt r ≤ 8 * (4 : ℝ) ^ (1 / 6 : ℝ) := by
  have h := exists_integer_stage_size 4 4 (by decide) (by decide) (by decide)
  have hsqrt_four : Real.sqrt 4 = 2 := by
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1
    norm_num
  norm_num [hsqrt_four] at h ⊢
  exact h

/-- An exact query count of zero cannot distinguish a repeated pair from a
distinct pair at error one third. -/
example : ¬ QueryCostAtMostWithError (kDistinctness 2 2 2) (1 / 3) 0 := by
  intro hbudget
  have hx : kDistinctness 2 2 2 id = false := by
    simp only [kDistinctness, decide_eq_false_iff_not]
    rintro ⟨S, hS, a, ha⟩
    have hfull : S = Finset.univ := S.eq_univ_of_card (by simpa using hS)
    have hbad : (0 : Fin 2) = 1 :=
      (ha 0 (by simp [hfull])).trans (ha 1 (by simp [hfull])).symm
    exact (by decide : (0 : Fin 2) ≠ 1) hbad
  have hy : kDistinctness 2 2 2 (fun _ => 0) = true := by
    simp only [kDistinctness, decide_eq_true_eq]
    exact ⟨Finset.univ, by simp, 0, fun _ _ => rfl⟩
  have h := one_le_query_budget_of_opposite_outputs hx hy (by norm_num) hbudget
  norm_num at h

/-- One faulty candidate is discarded and the unique clean child contributes
the nonzero parent value. -/
example :
    let y : Fin 3 → Fin 2 := fun i => if i = 2 then 1 else 0
    let rep : ℕ → Fin 3 := fun i => if i = 1 then 1 else 2
    (∑ D ∈ ({1, 2} : Finset ℕ).powerset.filter Finset.Nonempty,
      if ∀ j ∈ D, y (rep j) ≠ 0 then (-1 : ℝ) ^ (1 + D.card) * 3 else 0) = 3 := by
  classical
  dsimp only
  let y : Fin 3 → Fin 2 := fun i => if i = 2 then 1 else 0
  let rep : ℕ → Fin 3 := fun i => if i = 1 then 1 else 2
  have hinj : Set.InjOn rep (↑({1, 2} : Finset ℕ) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all [rep]
  have hneg : kDistinctness 3 3 2 y = false := by
    simp only [kDistinctness, decide_eq_false_iff_not]
    rintro ⟨S, hS, a, ha⟩
    have hfull : S = Finset.univ := S.eq_univ_of_card (by simpa using hS)
    have hbad := (ha 0 (by simp [hfull])).trans (ha 2 (by simp [hfull])).symm
    simp [y] at hbad
  have h := fault_filtered_child_sum (k := 3) (ℓ := 0) (s := 2)
    (by decide) (by decide) y 0 {0} {1, 2} rep (by decide) (by decide) hinj
    (by simp [rep]) (by simp [y])
    (letter_count_le_of_k_distinctness_eq_false (by decide) y hneg 0) 3 0
  simpa [y, rep] using h
