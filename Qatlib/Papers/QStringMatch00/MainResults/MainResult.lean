/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
import Qatlib.Papers.QStringMatch00.MainResults.Corollary1
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QStringMatch00.MainResults.MainResult

def blockCount (n m : ℕ) : ℝ := 2 * (n : ℝ) / m + 1

def outerOracleCalls (n m : ℕ) : ℝ :=
  4800 * ((29 / 2) * Real.sqrt (blockCount n m)) *
    (Real.log (64 * ((29 / 2) * Real.sqrt (blockCount n m))) + 1)

def blockOracleCost (m : ℕ) (A : ℝ) : ℝ := A * Real.sqrt m * (Real.log m + 1)

def preprocessCost (m : ℕ) (P : ℝ) : ℝ := P * Real.sqrt m * (Real.log m + 1) ^ 2

def mainCost (n m : ℕ) (A P : ℝ) : ℝ :=
  outerOracleCalls n m * blockOracleCost m A + preprocessCost m P

def shapeBound (n m : ℕ) : ℝ :=
  (Real.sqrt n + Real.sqrt m) * (Real.log ((n : ℝ) / m + 2) + 1) * Real.log (m + 2)
    + Real.sqrt m * Real.log (m + 2) ^ 2

lemma sqrt_blockCount_le (n m : ℕ) (hm : 0 < m) :
    Real.sqrt (blockCount n m) ≤ 2 * (Real.sqrt ((n : ℝ) / m) + 1) := by
  have hx : (0 : ℝ) ≤ (n : ℝ) / m := by positivity
  have hB : blockCount n m ≤ ((2 : ℝ) * (Real.sqrt ((n : ℝ) / m) + 1)) ^ 2 := by
    unfold blockCount
    have h2x : 2 * (n : ℝ) / m = 2 * ((n : ℝ) / m) := by rw [mul_div_assoc]
    have hs := Real.sq_sqrt hx
    have hsn := Real.sqrt_nonneg ((n : ℝ) / m)
    nlinarith [h2x, hs, hsn]
  calc Real.sqrt (blockCount n m)
      ≤ Real.sqrt (((2 : ℝ) * (Real.sqrt ((n : ℝ) / m) + 1)) ^ 2) :=
        Real.sqrt_le_sqrt hB
    _ = 2 * (Real.sqrt ((n : ℝ) / m) + 1) := Real.sqrt_sq (by positivity)

lemma log_outer_le (n m : ℕ) (hm : 0 < m) :
    Real.log (64 * ((29 / 2) * Real.sqrt (blockCount n m))) + 1 ≤
      1856 * (Real.log ((n : ℝ) / m + 2) + 1) := by
  have hx : (0 : ℝ) ≤ (n : ℝ) / m := by positivity
  have hsqrt := sqrt_blockCount_le n m hm

  have hxle : Real.sqrt ((n : ℝ) / m) + 1 ≤ (n : ℝ) / m + 2 := by
    have hs := Real.sq_sqrt hx
    have hsn := Real.sqrt_nonneg ((n : ℝ) / m)
    nlinarith [hs, hsn, sq_nonneg (Real.sqrt ((n : ℝ) / m) - 1)]

  have hstep : 64 * ((29 / 2) * Real.sqrt (blockCount n m)) ≤
      1856 * ((n : ℝ) / m + 2) := by
    have h1 : 928 * Real.sqrt (blockCount n m) ≤
        928 * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) :=
      mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    have h2 : 928 * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) ≤
        1856 * ((n : ℝ) / m + 2) := by nlinarith [hxle]
    have he : 64 * ((29 / 2) * Real.sqrt (blockCount n m)) =
        928 * Real.sqrt (blockCount n m) := by ring
    rw [he]
    linarith

  have hB1 : (1 : ℝ) ≤ blockCount n m := by
    unfold blockCount
    have h2x : 2 * (n : ℝ) / m = 2 * ((n : ℝ) / m) := by rw [mul_div_assoc]
    have hx : (0 : ℝ) ≤ (n : ℝ) / m := by positivity
    rw [h2x]
    linarith [hx]
  have hsqrtB1 : (1 : ℝ) ≤ Real.sqrt (blockCount n m) := Real.one_le_sqrt.mpr hB1
  have hposL : (0 : ℝ) < 64 * ((29 / 2) * Real.sqrt (blockCount n m)) := by
    nlinarith [hsqrtB1]
  have hposR : (0 : ℝ) < 1856 * ((n : ℝ) / m + 2) := by positivity
  have hlog := (Real.log_le_log_iff hposL hposR).mpr hstep
  rw [Real.log_mul (by norm_num : (1856 : ℝ) ≠ 0)
    (by positivity : ((n : ℝ) / m + 2) ≠ 0)] at hlog
  have h1856 : Real.log (1856 : ℝ) ≤ 1855 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1856)
    linarith
  have hL0 : 0 ≤ Real.log ((n : ℝ) / m + 2) := Real.log_nonneg (by linarith)
  linarith

lemma log_succ_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m : ℝ) + 1 ≤ 2 * Real.log ((m : ℝ) + 2) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm2 : (3 : ℝ) ≤ (m : ℝ) + 2 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [← Real.log_exp 1]
    apply Real.log_lt_log (Real.exp_pos 1)
    linarith [Real.exp_one_lt_d9]
  have hlogm2_ge1 : (1 : ℝ) ≤ Real.log ((m : ℝ) + 2) :=
    le_trans hlog3.le ((Real.log_le_log_iff (by norm_num : (0 : ℝ) < 3)
      (by positivity)).mpr hm2)
  have hlogm_le : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 2) :=
    (Real.log_le_log_iff hmR (by positivity)).mpr (by linarith)
  linarith

lemma blockOracleCost_le (m : ℕ) (hm : 1 ≤ m) (A : ℝ) (hA : 0 ≤ A) :
    blockOracleCost m A ≤ 2 * A * Real.sqrt m * Real.log ((m : ℝ) + 2) := by
  unfold blockOracleCost
  have hlog : Real.log (m : ℝ) + 1 ≤ 2 * Real.log ((m : ℝ) + 2) := log_succ_le m hm
  have hsqrt : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hprod := mul_le_mul_of_nonneg_left hlog (mul_nonneg hA hsqrt)
  nlinarith [hprod]

lemma preprocessCost_le (m : ℕ) (hm : 1 ≤ m) (P : ℝ) (hP : 0 ≤ P) :
    preprocessCost m P ≤ 4 * P * Real.sqrt m * Real.log ((m : ℝ) + 2) ^ 2 := by
  unfold preprocessCost
  have hlog : Real.log (m : ℝ) + 1 ≤ 2 * Real.log ((m : ℝ) + 2) := log_succ_le m hm
  have hlog0 : (0 : ℝ) ≤ Real.log (m : ℝ) + 1 := by
    have : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    linarith
  have hsq : (Real.log (m : ℝ) + 1) ^ 2 ≤ (2 * Real.log ((m : ℝ) + 2)) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  have hsqrt : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hprod := mul_le_mul_of_nonneg_left hsq (mul_nonneg hP hsqrt)
  nlinarith [hprod]

theorem main_result_cost
    (n m : ℕ) (hm : 1 ≤ m) (_hmn : m ≤ n) (A P : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    mainCost n m A P ≤ (4800 * 29 * 1856 * 2 * A + 4 * P + 1) * shapeBound n m := by
  have hm0 : 0 < m := by omega
  have hx0 : (0 : ℝ) ≤ (n : ℝ) / m := by positivity
  have hL0 : 0 ≤ Real.log ((n : ℝ) / m + 2) + 1 := by
    have : 0 ≤ Real.log ((n : ℝ) / m + 2) := Real.log_nonneg (by linarith)
    linarith
  have hlogm2 : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hsqm : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hsqn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _

  have houter : outerOracleCalls n m ≤
      4800 * (29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) *
        (1856 * (Real.log ((n : ℝ) / m + 2) + 1)) := by
    have h1 := sqrt_blockCount_le n m hm0
    have h2 := log_outer_le n m hm0
    have hP1 : (0 : ℝ) ≤ (29 / 2) * Real.sqrt (blockCount n m) := by positivity
    have hP2 : (0 : ℝ) ≤ Real.log (64 * ((29 / 2) * Real.sqrt (blockCount n m))) + 1 := by
      have hb1 : (1 : ℝ) ≤ blockCount n m := by
        unfold blockCount
        have h2x : 2 * (n : ℝ) / m = 2 * ((n : ℝ) / m) := by rw [mul_div_assoc]
        have hx : (0 : ℝ) ≤ (n : ℝ) / m := by positivity
        rw [h2x]
        linarith [hx]
      have hsb1 : (1 : ℝ) ≤ Real.sqrt (blockCount n m) := Real.one_le_sqrt.mpr hb1
      have : (1 : ℝ) ≤ 64 * ((29 / 2) * Real.sqrt (blockCount n m)) := by
        nlinarith [hsb1]
      have := Real.log_nonneg this
      linarith
    have hQ1 : (0 : ℝ) ≤ (29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) := by positivity
    have hQ2 : (0 : ℝ) ≤ 1856 * (Real.log ((n : ℝ) / m + 2) + 1) := by nlinarith [hL0]
    have hP1' : (29 / 2) * Real.sqrt (blockCount n m) ≤
        (29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hprod : (29 / 2) * Real.sqrt (blockCount n m) *
          (Real.log (64 * ((29 / 2) * Real.sqrt (blockCount n m))) + 1) ≤
        ((29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1))) *
          (1856 * (Real.log ((n : ℝ) / m + 2) + 1)) :=
      mul_le_mul hP1' h2 hP2 hQ1
    calc outerOracleCalls n m
        = 4800 * ((29 / 2) * Real.sqrt (blockCount n m) *
            (Real.log (64 * ((29 / 2) * Real.sqrt (blockCount n m))) + 1)) := by
          unfold outerOracleCalls; ring
      _ ≤ 4800 * (((29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1))) *
            (1856 * (Real.log ((n : ℝ) / m + 2) + 1))) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 4800 * (29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) *
            (1856 * (Real.log ((n : ℝ) / m + 2) + 1)) := by ring

  have hblock := blockOracleCost_le m hm A hA
  have hpre := preprocessCost_le m hm P hP
  have hblock0 : 0 ≤ blockOracleCost m A := by
    unfold blockOracleCost
    have hlm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    exact mul_nonneg (mul_nonneg hA hsqm) (by linarith)
  have hO0 : 0 ≤ 4800 * (29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) *
      (1856 * (Real.log ((n : ℝ) / m + 2) + 1)) := by
    have h1 : 0 ≤ 4800 * (29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) := by positivity
    have h2 : 0 ≤ 1856 * (Real.log ((n : ℝ) / m + 2) + 1) := by nlinarith [hL0]
    exact mul_nonneg h1 h2

  have hxm : Real.sqrt ((n : ℝ) / m) * Real.sqrt m = Real.sqrt n := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hUeq : (Real.sqrt ((n : ℝ) / m) + 1) * Real.sqrt m = Real.sqrt n + Real.sqrt m := by
    rw [add_mul, one_mul, hxm]
  have hOC : (4800 * (29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) *
        (1856 * (Real.log ((n : ℝ) / m + 2) + 1))) *
        (2 * A * Real.sqrt m * Real.log ((m : ℝ) + 2)) =
      (4800 * 29 * 1856 * 2 * A) *
        ((Real.sqrt n + Real.sqrt m) * (Real.log ((n : ℝ) / m + 2) + 1) *
          Real.log ((m : ℝ) + 2)) := by
    rw [← hUeq]
    ring
  have hU0 : 0 ≤ (Real.sqrt n + Real.sqrt m) * (Real.log ((n : ℝ) / m + 2) + 1) *
      Real.log ((m : ℝ) + 2) :=
    mul_nonneg (mul_nonneg (add_nonneg hsqn hsqm) hL0) hlogm2
  have hV0 : 0 ≤ Real.sqrt m * Real.log ((m : ℝ) + 2) ^ 2 :=
    mul_nonneg hsqm (sq_nonneg _)
  have hstep1 : outerOracleCalls n m * blockOracleCost m A ≤
      (4800 * (29 / 2) * (2 * (Real.sqrt ((n : ℝ) / m) + 1)) *
        (1856 * (Real.log ((n : ℝ) / m + 2) + 1))) *
        (2 * A * Real.sqrt m * Real.log ((m : ℝ) + 2)) :=
    mul_le_mul houter hblock hblock0 hO0
  have hstep2 : outerOracleCalls n m * blockOracleCost m A ≤
      (4800 * 29 * 1856 * 2 * A) *
        ((Real.sqrt n + Real.sqrt m) * (Real.log ((n : ℝ) / m + 2) + 1) *
          Real.log ((m : ℝ) + 2)) := by
    rw [hOC] at hstep1
    exact hstep1
  have hcA : (4800 * 29 * 1856 * 2 * A) ≤ (4800 * 29 * 1856 * 2 * A + 4 * P + 1) := by
    linarith [hP]
  have h4P : 4 * P ≤ (4800 * 29 * 1856 * 2 * A + 4 * P + 1) := by linarith
  unfold mainCost shapeBound
  rw [mul_add]
  have h1 := mul_le_mul_of_nonneg_right hcA hU0
  have h2 := mul_le_mul_of_nonneg_right h4P hV0
  linarith [hstep2, hpre, h1, h2]

theorem main_result_success :
    ((3 / 4 : ℝ) ^ 2 > 1 / 2) ∧ ((3 / 4 : ℝ) > 1 / 2) := by
  constructor <;> norm_num

theorem main_cost_success_bounds
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (A P : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    0 ≤ mainCost n m A P ∧
      mainCost n m A P ≤ (4800 * 29 * 1856 * 2 * A + 4 * P + 1) * shapeBound n m ∧
      ((3 / 4 : ℝ) ^ 2 > 1 / 2 ∧ (3 / 4 : ℝ) > 1 / 2) := by
  refine ⟨?_, main_result_cost n m hm hmn A P hA hP, main_result_success⟩
  have hb1 : (1 : ℝ) ≤ blockCount n m := by
    unfold blockCount
    have h2x : 2 * (n : ℝ) / m = 2 * ((n : ℝ) / m) := by rw [mul_div_assoc]
    have hx : (0 : ℝ) ≤ (n : ℝ) / m := by positivity
    rw [h2x]
    linarith [hx]
  have hsb1 : (0 : ℝ) ≤ Real.sqrt (blockCount n m) := Real.sqrt_nonneg _
  have hinner : (0 : ℝ) ≤ (29 / 2) * Real.sqrt (blockCount n m) :=
    mul_nonneg (by norm_num) hsb1
  have hlogB : (0 : ℝ) ≤ Real.log (64 * ((29 / 2) * Real.sqrt (blockCount n m))) + 1 := by
    have hpos : (1 : ℝ) ≤ 64 * ((29 / 2) * Real.sqrt (blockCount n m)) := by
      have h1 : (1 : ℝ) ≤ Real.sqrt (blockCount n m) := Real.one_le_sqrt.mpr hb1
      nlinarith [h1]
    have := Real.log_nonneg hpos
    linarith
  have hlogm : (0 : ℝ) ≤ Real.log (m : ℝ) + 1 := by
    have : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    linarith
  have hsqm : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hOuter : 0 ≤ outerOracleCalls n m := by
    unfold outerOracleCalls
    exact mul_nonneg (mul_nonneg (by norm_num) hinner) hlogB
  have hBlock : 0 ≤ blockOracleCost m A := by
    unfold blockOracleCost
    exact mul_nonneg (mul_nonneg hA hsqm) hlogm
  have hPre : 0 ≤ preprocessCost m P := by
    unfold preprocessCost
    exact mul_nonneg (mul_nonneg hP hsqm) (sq_nonneg _)
  show 0 ≤ mainCost n m A P
  rw [show mainCost n m A P = outerOracleCalls n m * blockOracleCost m A + preprocessCost m P from rfl]
  exact add_nonneg (mul_nonneg hOuter hBlock) hPre

open Qatlib.Papers.QStringMatch00.MainResults.Corollary1 in

theorem outer_calls_via_corollary1 (n m N : ℕ) (hm : 1 ≤ m) (hN1 : 1 ≤ N)
    (hN : (N : ℝ) ≤ blockCount n m) :
    ∃ r : ℕ, 0 < (29 / 2) * Real.sqrt (N : ℝ) ∧
      (2 * (r : ℝ) + 1) * (8 * ((29 / 2) * Real.sqrt (N : ℝ))) ≤
        outerOracleCalls n m := by
  classical
  have hNpos : 0 < N := by omega
  let A : Finset (Fin N) := {⟨0, hNpos⟩}
  have hAcard : A.card = 1 := by simp [A]
  obtain ⟨r, hQ0, _hunif, _hfail, hcost, _hsucc⟩ :=
    corollary1_search N 1 hNpos le_rfl hN1 A hAcard
  refine ⟨r, ?_, ?_⟩
  · simpa using! hQ0
  · set QN : ℝ := (29 / 2) * Real.sqrt (N : ℝ) with hQNdef
    set Qb : ℝ := (29 / 2) * Real.sqrt (blockCount n m) with hQbdef
    have hcost' : (2 * (r : ℝ) + 1) * (8 * QN) ≤
        4800 * QN * (Real.log (64 * QN) + 1) := by
      simpa [hQNdef] using! hcost
    have hbc0 : (0 : ℝ) ≤ blockCount n m := by
      unfold blockCount
      have hx : (0 : ℝ) ≤ (n : ℝ) / m := by positivity
      have h2x : 2 * (n : ℝ) / m = 2 * ((n : ℝ) / m) := by rw [mul_div_assoc]
      rw [h2x]; linarith
    have hle : QN ≤ Qb := by
      rw [hQNdef, hQbdef]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hN) (by norm_num)
    have hsN1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hN1)
    have hQN1 : (1 : ℝ) ≤ QN := by
      rw [hQNdef]; nlinarith
    have hQN0 : (0 : ℝ) ≤ QN := by linarith
    have hQb0 : (0 : ℝ) ≤ Qb := le_trans hQN0 hle
    have hposN : (0 : ℝ) < 64 * QN := by nlinarith
    have hposB : (0 : ℝ) < 64 * Qb := by nlinarith
    have hL : Real.log (64 * QN) + 1 ≤ Real.log (64 * Qb) + 1 := by
      have h64 : 64 * QN ≤ 64 * Qb := by nlinarith
      have := Real.log_le_log hposN h64
      linarith
    have hL0 : (0 : ℝ) ≤ Real.log (64 * QN) + 1 := by
      have : 0 ≤ Real.log (64 * QN) := Real.log_nonneg (by linarith)
      linarith
    have hstep : 4800 * QN * (Real.log (64 * QN) + 1) ≤
        4800 * Qb * (Real.log (64 * Qb) + 1) := by
      have h1 : 4800 * QN ≤ 4800 * Qb := by nlinarith
      exact mul_le_mul h1 hL hL0 (by positivity)
    have houter : outerOracleCalls n m =
        4800 * Qb * (Real.log (64 * Qb) + 1) := by
      rw [outerOracleCalls, hQbdef]
    rw [houter]
    exact le_trans hcost' hstep

end Qatlib.Papers.QStringMatch00.MainResults.MainResult
