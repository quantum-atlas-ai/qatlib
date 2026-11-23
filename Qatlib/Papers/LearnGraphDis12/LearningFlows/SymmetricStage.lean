/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

/-!
# Symmetric stages of a learning graph

[Belovs2012], Theorem 6 of the [fixed preprint](https://arxiv.org/abs/1205.1534v2).
For a unit flow with a common nonzero value on used transitions, assign the same
positive weight to every arc. Each transition contributes one arc occurrence per
loaded variable. The two stage costs are squared Euclidean norms on these
occurrences. The construction works for a stage whose transition paths are given;
it does not construct the paper's learning graphs or compile a query algorithm.
-/

open scoped BigOperators

namespace Qatlib.Papers.LearnGraphDis12.LearningFlows

open Classical in
/-- The number of used transitions of a symmetric unit flow is the reciprocal of
its common positive current. -/
theorem symmetric_flow_support_card {T : Type*} [Fintype T]
    (p : T → ℝ) (q : ℝ) (hunit : ∑ t, p t = 1)
    (hsym : ∀ t, p t = 0 ∨ p t = q) :
    ((Finset.univ.filter fun t => p t ≠ 0).card : ℝ) * q = 1 := by
  classical
  calc
    _ = ∑ t ∈ Finset.univ.filter (fun t => p t ≠ 0), q := by simp
    _ = ∑ t ∈ Finset.univ.filter (fun t => p t ≠ 0), p t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact ((hsym t).resolve_left (Finset.mem_filter.mp ht).2).symm
    _ = 1 := by simpa only [Finset.sum_filter_ne_zero] using hunit

open Classical in
/-- For a nonempty family of unit flows with a common positive current, a single
weight balances both Euclidean stage costs for every input. The speciality is the
ratio of all transitions to those used, and the shared cost is the stage length
times the square root of the speciality. -/
theorem symmetric_stage_balanced_cost {X T : Type*} [Nonempty X]
    [Fintype T] (L : ℕ) (hL : 0 < L)
    (p : X → T → ℝ) (q : ℝ) (hq : 0 < q)
    (hunit : ∀ x, ∑ t, p x t = 1) (hsym : ∀ x t, p x t = 0 ∨ p x t = q) :
    ∃ τ w : ℝ, 0 < τ ∧ 0 < w ∧ w = q / Real.sqrt τ ∧
      0 < (L : ℝ) * Real.sqrt τ ∧
      ‖(WithLp.toLp 2 fun _ : T × Fin L => Real.sqrt w :
        EuclideanSpace ℝ (T × Fin L))‖ ^ 2 = L * Real.sqrt τ ∧
      ∀ x, τ = Fintype.card T / ((Finset.univ.filter fun t => p x t ≠ 0).card : ℝ) ∧
        ‖(WithLp.toLp 2 fun a : T × Fin L => p x a.1 / Real.sqrt w :
          EuclideanSpace ℝ (T × Fin L))‖ ^ 2 = L * Real.sqrt τ := by
  classical
  have hT : 0 < Fintype.card T := by
    by_contra! h
    have : IsEmpty T := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    simpa using hunit (Classical.choice ‹Nonempty X›)
  let τ : ℝ := Fintype.card T * q
  have hτ : 0 < τ := mul_pos (Nat.cast_pos.mpr hT) hq
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  let w : ℝ := q / Real.sqrt τ
  have hw : 0 < w := div_pos hq hsτ
  refine ⟨τ, w, hτ, hw, rfl, mul_pos (Nat.cast_pos.mpr hL) hsτ, ?_, ?_⟩
  · rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Real.sq_sqrt hw.le, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, nsmul_eq_mul]
    dsimp [w]
    field_simp [hsτ.ne']
    rw [Real.sq_sqrt hτ.le]
  · intro x
    constructor
    · have hcard := symmetric_flow_support_card (p x) q (hunit x) (hsym x)
      have hcard₀ : ((Finset.univ.filter fun t => p x t ≠ 0).card : ℝ) ≠ 0 := by
        intro hzero
        simp [hzero] at hcard
      apply (eq_div_iff hcard₀).2
      dsimp [τ]
      rw [mul_assoc, mul_comm q, hcard, mul_one]
    · rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
      simp only [div_pow, Real.sq_sqrt hw.le, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsum : ∑ t, p x t ^ 2 = q := by
        calc
          _ = ∑ t, q * p x t := by
            apply Finset.sum_congr rfl
            intro t _
            rcases hsym x t with h | h <;> rw [h] <;> ring
          _ = q := by rw [← Finset.mul_sum, hunit x, mul_one]
      rw [← Finset.mul_sum, ← Finset.sum_div, hsum]
      congr 1
      dsimp [w]
      field_simp [hq.ne', hsτ.ne']

end Qatlib.Papers.LearnGraphDis12.LearningFlows
