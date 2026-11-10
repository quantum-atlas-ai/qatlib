/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroGibbsOverlapContracts
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChebyshevProductIdentityMont
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChiSqOverlapSubgoalMont

open Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false

theorem montanaro_raw_gibbs_sum_identity (Ω : Type) [Fintype Ω]
    (H : Ω → ℕ) (β₁ β₂ : ℝ) :
    chiSqGibbsSum H β₁ β₂ = partitionFn H (2*β₂-β₁)/partitionFn H β₂^2 := by
  change (∑ x, Real.exp (-(β₂*(H x : ℝ)))^2 / Real.exp (-(β₁*(H x : ℝ)))) /
    partitionFn H β₂^2 = (∑ x, Real.exp (-((2*β₂-β₁)*(H x : ℝ)))) / partitionFn H β₂^2
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [pow_two, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

theorem montanaroChiSqScheduleOverlapSubgoal_false : ¬ MontanaroChiSqScheduleOverlapSubgoal := by
  intro h
  have hh := (h Bool (fun _ => 0) 0 0 1 (by norm_num)
    (by norm_num [partitionFn, Fintype.sum_bool])
    (by norm_num [partitionFn, Fintype.sum_bool]) (by norm_num)
    (by norm_num [partitionFn, Fintype.sum_bool])).1
  norm_num [chiSqGibbsSum, partitionFn, Fintype.sum_bool] at hh

private noncomputable def scheduleGibbs {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β : ℝ)
    (hZ : 0 < partitionFn H β) : FinDist Ω where
  prob x := Real.exp (-(β*(H x : ℝ)))/partitionFn H β
  nonneg x := div_nonneg (Real.exp_nonneg _) (le_of_lt hZ)
  sum_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt hZ)

private theorem scheduleGibbs_overlap {Ω : Type} [Fintype Ω]
    (H : Ω → ℕ) (β₁ β₂ : ℝ) (hZ₁ : 0 < partitionFn H β₁) (hZ₂ : 0 < partitionFn H β₂) :
    (∑ x, (scheduleGibbs H β₂ hZ₂).prob x *
      Real.sqrt ((scheduleGibbs H β₁ hZ₁).prob x / (scheduleGibbs H β₂ hZ₂).prob x)) =
      gibbsOverlap H β₁ β₂ := by
  rw [gibbsOverlap, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  let a := (scheduleGibbs H β₂ hZ₂).prob x
  let b := (scheduleGibbs H β₁ hZ₁).prob x
  have ha : 0 < a := div_pos (Real.exp_pos _) hZ₂
  have hb : 0 < b := div_pos (Real.exp_pos _) hZ₁
  change a * Real.sqrt (b/a) = _
  have hs : a * Real.sqrt (b/a) = Real.sqrt (a*b) := by
    calc
      _ = Real.sqrt (a^2)*Real.sqrt (b/a) := by rw [Real.sqrt_sq (le_of_lt ha)]
      _ = Real.sqrt (a^2*(b/a)) := (Real.sqrt_mul (sq_nonneg a) _).symm
      _ = _ := by congr 1; field_simp
  rw [hs]
  have hp : a*b = (Real.exp (-(β₂*(H x : ℝ)))*Real.exp (-(β₁*(H x : ℝ)))) /
      (partitionFn H β₁*partitionFn H β₂) := by dsimp [a, b, scheduleGibbs]; ring
  rw [hp, Real.sqrt_div (by positivity)]
  congr 1
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (Real.exp_nonneg _)).2
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private theorem scheduleGibbs_chi {Ω : Type} [Fintype Ω]
    (H : Ω → ℕ) (β₁ β₂ : ℝ) (hZ₁ : 0 < partitionFn H β₁) (hZ₂ : 0 < partitionFn H β₂) :
    chiSqDist (scheduleGibbs H β₂ hZ₂) (scheduleGibbs H β₁ hZ₁) + 1 =
      partitionFn H β₁ * chiSqGibbsSum H β₁ β₂ := by
  simp only [chiSqDist, sub_add_cancel, chiSqGibbsSum, scheduleGibbs]
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [ne_of_gt hZ₁, ne_of_gt hZ₂, ne_of_gt (Real.exp_pos (-(β₁*(H x : ℝ))))]

theorem montanaro_schedule_overlap_bound (Ω : Type) [Fintype Ω]
    (H : Ω → ℕ) (β₁ β₂ B : ℝ) (_hβ : β₁ ≤ β₂)
    (hZ₁ : 0 < partitionFn H β₁) (hZ₂ : 0 < partitionFn H β₂) (_hB : 0 < B)
    (hs : partitionFn H β₁*partitionFn H (2*β₂-β₁) ≤ B*partitionFn H β₂^2) :
    1/B ≤ gibbsOverlap H β₁ β₂^2 := by
  let ν := scheduleGibbs H β₂ hZ₂
  let π := scheduleGibbs H β₁ hZ₁
  have hν (x : Ω) : 0 < ν.prob x := div_pos (Real.exp_pos _) hZ₂
  have hπ (x : Ω) : 0 < π.prob x := div_pos (Real.exp_pos _) hZ₁
  have hj := montanaroChiSqOverlapSubgoal Ω ν π hπ hν
  rw [scheduleGibbs_overlap] at hj
  have hchi : chiSqDist ν π + 1 ≤ B := by
    rw [scheduleGibbs_chi, montanaro_raw_gibbs_sum_identity, ← mul_div_assoc]
    exact (div_le_iff₀ (sq_pos_of_pos hZ₂)).2 hs
  have hχ0 : 0 < chiSqDist ν π + 1 := by
    rw [scheduleGibbs_chi, montanaro_raw_gibbs_sum_identity]
    have hz : 0 < partitionFn H (2*β₂-β₁) := by
      have hne : (Finset.univ : Finset Ω).Nonempty := by
        by_contra h
        have hh := ν.sum_one
        rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hh
        norm_num at hh
      exact Finset.sum_pos (fun x _ => Real.exp_pos _) hne
    exact mul_pos hZ₁ (div_pos hz (sq_pos_of_pos hZ₂))
  have hr : 0 < Real.sqrt (chiSqDist ν π+1) := Real.sqrt_pos.2 hχ0
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 1/Real.sqrt (chiSqDist ν π+1)) hj
  rw [← pow_two, div_pow, one_pow, Real.sq_sqrt (le_of_lt hχ0)] at hsq
  have hi : 1/B ≤ 1/(chiSqDist ν π+1) := one_div_le_one_div_of_le hχ0 hchi
  simpa only [pow_two] using hi.trans hsq

end Qatlib.Concepts.EstimatorLaws.TvStability
