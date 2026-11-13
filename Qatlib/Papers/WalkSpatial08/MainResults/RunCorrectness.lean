/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WalkSpatial08.MainResults.RunDynamics
import Qatlib.Papers.WalkSpatial08.MainResults.RunRates

/-!
# Success weights for balanced lattice schedules

This module defines the model success weight and a schedule carrying iteration, setup, and
time-accounting data. At the balanced control parameter, it bounds the phase increment and the
rounded iteration angle, yielding a constant lower bound on the success weight and an eventual
balanced schedule.

The controlled spatial-search setting is described in [Tulsi2008].

## Main statements

* `modelSuccessWeight_ge`: success weight at least `1 / 66` for side length at least sixteen.
* `balanced_schedule_bound`: schedules with the prescribed step count and constant success
  weight.

## References

* [Tulsi, 2008][Tulsi2008]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.WalkSpatial08.MainResults

/-- The balanced final-overlap square multiplied by the squared sine of the accumulated model
phase after `it` iterations. -/
def modelSuccessWeight (n it : ℕ) : ℝ :=
  finalOverlapSq n (deltaStar n) *
    Real.sin (((it : ℝ) * alphaDelta n (deltaStar n))) ^ 2

/-- A lattice model schedule containing iteration and setup counts and a time account whose
total steps equal twice the iterations plus setup. -/
structure LatticeBudgetSchedule (n : ℕ) where

  iterations : ℕ

  setup : ℕ

  account : TimeAccount

  steps_eq : account.steps = 2 * iterations + setup

/-- The existence of a lattice schedule with total steps at most `T` and model success weight at
least `p`. -/
def ModelBudgetWithin (n : ℕ) (T p : ℝ) : Prop :=
  ∃ alg : LatticeBudgetSchedule n,
    (alg.account.steps : ℝ) ≤ T ∧ p ≤ modelSuccessWeight n alg.iterations

/-- For lattice side length at least sixteen, the balanced model phase increment is positive. -/
theorem alphaDeltaStar_pos {n : ℕ} (hn : 16 ≤ n) :
    0 < alphaDelta n (deltaStar n) := by
  have hnpos : 0 < n := by omega
  have hlog : 1 ≤ logLattice n := logLattice_ge_one_of_ge_16 hn
  have hlow := alphaDeltaStar_lower hnpos hlog
  have hNpos : 0 < (latticeSize n : ℝ) := by exact_mod_cast latticeSize_pos hnpos
  have hLpos := logLattice_pos hlog
  have hsqrt : 0 < Real.sqrt ((latticeSize n : ℝ) * logLattice n) :=
    Real.sqrt_pos.mpr (mul_pos hNpos hLpos)
  have hpos : 0 < (2 / 3) * (1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n)) := by
    have : 0 < 1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n) :=
      one_div_pos.mpr hsqrt
    nlinarith
  linarith [hlow, hpos]

/-- For lattice side length at least sixteen, the balanced model phase increment is at most one
quarter. -/
theorem alphaDeltaStar_le_quarter {n : ℕ} (hn : 16 ≤ n) :
    alphaDelta n (deltaStar n) ≤ 1 / 4 := by
  have hnpos : 0 < n := by omega
  have hlog : 1 ≤ logLattice n := logLattice_ge_one_of_ge_16 hn
  have hsqrt5 : 2 ≤ Real.sqrt (5 * logLattice n - 1) := by
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]
    apply Real.sqrt_le_sqrt
    linarith [logLattice_pos hlog]
  have hsqrtN : 4 ≤ Real.sqrt (latticeSize n : ℝ) := by
    rw [sqrt_latticeSize]
    have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 4 ≤ n)
    exact h4
  have hden : 8 ≤ Real.sqrt (latticeSize n : ℝ) * Real.sqrt (5 * logLattice n - 1) := by
    have hA := Real.sqrt_nonneg (latticeSize n : ℝ)
    have := mul_le_mul hsqrtN hsqrt5 (by norm_num : (0 : ℝ) ≤ 2) hA
    linarith [this]
  rw [alphaDeltaStar_eq hnpos hlog, show (1 : ℝ) / 4 = 2 / 8 by norm_num]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden

/-- For side length at least sixteen, rounding `π / (4 * alphaDelta n (deltaStar n))` upward
gives an accumulated phase with squared sine at least one half. See [Main result: O(sqrt(N
log N)) two-dimensional spatial search][Tulsi2008]. -/
theorem iterations_sin_sq_ge {n : ℕ} (hn : 16 ≤ n) :
    1 / 2 ≤ Real.sin (((Nat.ceil (Real.pi / (4 * alphaDelta n (deltaStar n))) : ℕ) : ℝ)
      * alphaDelta n (deltaStar n)) ^ 2 := by
  have hαpos : 0 < alphaDelta n (deltaStar n) := alphaDeltaStar_pos hn
  have hαle : alphaDelta n (deltaStar n) ≤ 1 / 4 := alphaDeltaStar_le_quarter hn
  set α := alphaDelta n (deltaStar n) with hαdef
  set x : ℝ := Real.pi / (4 * α) with hxdef
  have hxpos : 0 ≤ x := by
    rw [hxdef]
    exact le_of_lt (div_pos Real.pi_pos (by nlinarith))
  have hlo : x ≤ ((Nat.ceil x : ℕ) : ℝ) := Nat.le_ceil x
  have hhi : ((Nat.ceil x : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos
  have hxα : x * α = Real.pi / 4 := by
    rw [hxdef]
    field_simp [hαpos.ne']
  have hx1α : (x + 1) * α = Real.pi / 4 + α := by
    rw [hxdef]
    field_simp [hαpos.ne']
  have h1 : Real.pi / 4 ≤ ((Nat.ceil x : ℕ) : ℝ) * α := by
    have hmul := mul_le_mul_of_nonneg_right hlo hαpos.le
    linarith [hmul, hxα]
  have h2 : ((Nat.ceil x : ℕ) : ℝ) * α ≤ Real.pi / 2 := by
    have hlt := mul_lt_mul_of_pos_right hhi hαpos
    have hpi : Real.pi / 4 + α ≤ Real.pi / 2 := by
      nlinarith [hαle, Real.pi_gt_three]
    linarith [hlt, hx1α, hpi]
  exact sin_sq_ge_half h1 h2

/-- For side length at least sixteen, the rounded balanced iteration count has model success
weight at least `1 / 66`. -/
theorem modelSuccessWeight_ge {n : ℕ} (hn : 16 ≤ n) :
    1 / 66 ≤ modelSuccessWeight n (Nat.ceil (Real.pi / (4 * alphaDelta n (deltaStar n)))) := by
  unfold modelSuccessWeight
  have hF : 1 / 33 ≤ finalOverlapSq n (deltaStar n) := finalOverlapSq_ge hn
  have hs : 1 / 2 ≤
      Real.sin (((Nat.ceil (Real.pi / (4 * alphaDelta n (deltaStar n))) : ℕ) : ℝ)
        * alphaDelta n (deltaStar n)) ^ 2 := iterations_sin_sq_ge hn
  have hFpos : 0 < finalOverlapSq n (deltaStar n) := by
    unfold finalOverlapSq
    apply one_div_pos.mpr
    have hmul : 0 ≤ 8 * Real.cos (deltaStar n) ^ 2 * sumInvGap n :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sumInvGap_nonneg n)
    linarith
  have hspos : 0 ≤
      Real.sin (((Nat.ceil (Real.pi / (4 * alphaDelta n (deltaStar n))) : ℕ) : ℝ)
        * alphaDelta n (deltaStar n)) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul hF hs (by norm_num : (0 : ℝ) ≤ 1 / 2) hFpos.le
  have hval : (1 : ℝ) / 33 * (1 / 2) = 1 / 66 := by norm_num
  linarith [hmul, hval]

/-- For all sufficiently large side lengths, there is a schedule with exactly
`controlledWalkTimeSteps n` steps and a uniform positive lower bound on model success
weight. See [Main result: O(sqrt(N log N)) two-dimensional spatial search][Tulsi2008]. -/
theorem balanced_schedule_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ alg : LatticeBudgetSchedule n,
        alg.account.steps = controlledWalkTimeSteps n ∧
          c ≤ modelSuccessWeight n alg.iterations := by
  refine ⟨1 / 66, by norm_num, 16, ?_⟩
  intro n hn
  refine ⟨{ iterations := Nat.ceil (Real.pi / (4 * alphaDelta n (deltaStar n)))
            setup := Nat.ceil (Real.sqrt (latticeSize n : ℝ))
            account :=
              ⟨controlledWalkTimeSteps n, 0, controlledWalkTimeSteps n, by simp⟩
            steps_eq := ?_ }, rfl, modelSuccessWeight_ge hn⟩
  unfold controlledWalkTimeSteps
  ring

end Qatlib.Papers.WalkSpatial08.MainResults
