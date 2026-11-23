/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.DistinctLB26.MainResults.Execution.FourierReadout

@[expose] public section

/-!
# Success probabilities from physical input-query executions

The correctness relation is fixed before the algorithm. Both its pointwise
success and its uniform success are Born probabilities of the actual executed
program. The joint Fourier-register model gives precisely their uniform
average; it supplies no independent output or success field.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Papers.DistinctLB26.MainResults.Execution

variable {n q : ℕ} [NeZero q] {W : Type*} [Fintype W]

/-- The actual Born success probability on one computational input. -/
def physicalSuccess (correct : Label n q → Work n q W → Prop)
    (prog : List (Instr n q W)) (φ : Local n q W) (x : Label n q) : ℝ := by
  classical
  exact ∑ a : Work n q W, if correct x a then ‖inputRun x prog φ a‖ ^ 2 else 0

/-- Uniform average of success on the actual computational inputs. -/
def averageSuccess (correct : Label n q → Work n q W → Prop)
    (prog : List (Instr n q W)) (φ : Local n q W) : ℝ :=
  (Fintype.card (Label n q) : ℝ)⁻¹ * ∑ x : Label n q, physicalSuccess correct prog φ x

/-- The same success event measured on the executed joint input-work state. -/
def jointSuccess (correct : Label n q → Work n q W → Prop)
    (prog : List (Instr n q W)) (φ : Local n q W) : ℝ := by
  classical
  exact ∑ z : Label n q × Work n q W,
    if correct z.1 z.2 then ‖readout (execute prog (zeroInput φ)) z‖ ^ 2 else 0

/-- Every joint computational amplitude has its actual uniform input weight. -/
theorem readout_born (prog : List (Instr n q W)) (φ : Local n q W)
    (x : Label n q) (a : Work n q W) :
    ‖readout (execute prog (zeroInput φ)) (x, a)‖ ^ 2 =
      (Fintype.card (Label n q) : ℝ)⁻¹ * ‖inputRun x prog φ a‖ ^ 2 := by
  rw [readout_execute, norm_mul, mul_pow]
  change ‖fourierScale (Label n q)‖ ^ 2 * _ = _
  rw [Qatlib.Concepts.WalkFind.UniformThree.norm_fourierScale_sq]

/-- Joint-register success is exactly the uniform average of physical algorithm success. -/
theorem joint_average (correct : Label n q → Work n q W → Prop)
    (prog : List (Instr n q W)) (φ : Local n q W) :
    jointSuccess correct prog φ = averageSuccess correct prog φ := by
  classical
  unfold jointSuccess averageSuccess physicalSuccess
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : correct x a
  · simp only [h, ite_true]
    exact readout_born prog φ x a
  · simp only [h, ite_false, mul_zero]

/-- Every normalized physical execution has success probability in the unit interval. -/
theorem physical_bounds (correct : Label n q → Work n q W → Prop)
    (prog : List (Instr n q W)) (φ : Local n q W) (hφ : ‖φ‖ = 1) (x : Label n q) :
    0 ≤ physicalSuccess correct prog φ x ∧ physicalSuccess correct prog φ x ≤ 1 := by
  classical
  constructor
  · exact Finset.sum_nonneg fun a _ => by split_ifs <;> positivity
  · calc
      physicalSuccess correct prog φ x ≤ ∑ a : Work n q W, ‖inputRun x prog φ a‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs <;> simp
      _ = 1 := by rw [← EuclideanSpace.norm_sq_eq, inputRun_norm, hφ]; norm_num

/-- The derived uniform Born success is a genuine probability for every normalized work state. -/
theorem joint_bounds (correct : Label n q → Work n q W → Prop)
    (prog : List (Instr n q W)) (φ : Local n q W) (hφ : ‖φ‖ = 1) :
    0 ≤ jointSuccess correct prog φ ∧ jointSuccess correct prog φ ≤ 1 := by
  rw [joint_average]
  constructor
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun x _ => (physical_bounds correct prog φ hφ x).1)
  · calc
      averageSuccess correct prog φ ≤
          (Fintype.card (Label n q) : ℝ)⁻¹ * ∑ _x : Label n q, (1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x _ => (physical_bounds correct prog φ hφ x).2)
          (by positivity)
      _ = 1 := by simp

end Qatlib.Papers.DistinctLB26.MainResults.Execution
