/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false

open scoped BigOperators

noncomputable section

open Finset

namespace Qatlib.Papers.QSearchAdvice09.MainResults

def harmSum (n : ℕ) : ℝ := ∑ k ∈ range n, 1 / ((k : ℝ) + 1)

theorem harmSum_nonneg (n : ℕ) : 0 ≤ harmSum n := by
  unfold harmSum
  refine sum_nonneg ?_
  intro k _
  positivity

theorem harmSum_succ (n : ℕ) : harmSum (n + 1) = harmSum n + 1 / ((n : ℝ) + 1) := by
  unfold harmSum
  rw [sum_range_succ]

theorem log_ratio_le_inv {k : ℕ} (hk : 0 < k) :
    Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpos : (0 : ℝ) < ((k : ℝ) + 1) / (k : ℝ) := by positivity
  have h1 : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (by positivity) (ne_of_gt hk0)] at h1
  have h2 : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
    field_simp
    ring
  linarith

theorem log_succ_le_harm (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ harmSum n := by
  induction n with
  | zero => simp [harmSum]
  | succ n ih =>
    rw [harmSum_succ]
    have h := log_ratio_le_inv (Nat.succ_pos n)
    push_cast at h ⊢
    linarith

theorem harm_le_one_add_log (n : ℕ) : harmSum n ≤ 1 + Real.log (n : ℝ) := by
  induction n with
  | zero => simp [harmSum]
  | succ n ih =>
    rw [harmSum_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num [harmSum]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hx : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := by positivity
      have h := Real.one_sub_inv_le_log_of_pos hx
      rw [Real.log_div (by positivity) (ne_of_gt hn0)] at h
      have h2 : 1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹ = 1 / ((n : ℝ) + 1) := by
        field_simp
        ring
      rw [h2] at h
      push_cast at h ⊢
      linarith

theorem harmSum_isTheta :
    Asymptotics.IsTheta Filter.atTop harmSum (fun n : ℕ => Real.log (n : ℝ)) := by
  constructor
  · refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [Filter.eventually_atTop.2 ⟨3, fun n hn => hn⟩] with n hn
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogpos : 0 ≤ Real.log ((n : ℝ)) :=
      le_of_lt (Real.log_pos (by linarith))
    rw [Real.norm_of_nonneg (harmSum_nonneg n), Real.norm_of_nonneg hlogpos]
    have h := harm_le_one_add_log n
    have h3 : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).2 (le_of_lt Real.exp_one_lt_three)
    have hmono : Real.log 3 ≤ Real.log ((n : ℝ)) := Real.log_le_log (by norm_num) hnR
    linarith
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogpos : 0 ≤ Real.log ((n : ℝ)) :=
      le_of_lt (Real.log_pos (by linarith))
    rw [Real.norm_of_nonneg hlogpos, Real.norm_of_nonneg (harmSum_nonneg n)]
    have h := log_succ_le_harm n
    have hmono : Real.log ((n : ℝ)) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (x := (n : ℝ)) (y := (n : ℝ) + 1) (by linarith) (by linarith)
    linarith

end Qatlib.Papers.QSearchAdvice09.MainResults
