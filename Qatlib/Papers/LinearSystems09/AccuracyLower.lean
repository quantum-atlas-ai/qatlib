/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinearSystems09.AccuracyLower

open Qatlib.Foundations.PureStateMath

noncomputable def estimationRuntime (α β : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (β * (n : ℝ))

theorem source_theorem6_exact_counting_lower_bound (α β : ℝ)
    (hcounting : ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ^ (n : ℝ) ≤ estimationRuntime α β n) :
    1 ≤ α + β := by
  rw [Filter.eventually_atTop] at hcounting
  obtain ⟨N, hN⟩ := hcounting
  set n : ℕ := max N 1 with hn
  have hNn : N ≤ n := le_max_left N 1
  have hn1 : 1 ≤ n := le_max_right N 1
  have hb := hN n hNn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hcomb : (2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (β * (n : ℝ))
      = (2 : ℝ) ^ ((α + β) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [estimationRuntime, hcomb] at hb
  have hmono : (n : ℝ) ≤ (α + β) * (n : ℝ) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hb
  have hmul : (n : ℝ) * 1 ≤ (n : ℝ) * (α + β) := by
    nlinarith [hmono]
  nlinarith [hmul, hnpos]

noncomputable def countingProbability (n C : ℕ) : ℝ := (C : ℝ) / (2 : ℝ) ^ n

noncomputable def exactCountingPrecision (n : ℕ) : ℝ := 1 / (2 : ℝ) ^ (2 * n)

theorem countingProbability_separation {n C D : ℕ} (hC : C ≤ 2 ^ n)
    (hD : D ≤ 2 ^ n) (hne : C ≠ D) :
    (1 : ℝ) / (2 : ℝ) ^ n ≤
      |countingProbability n C - countingProbability n D| := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hCD : (1 : ℝ) ≤ |(C : ℝ) - (D : ℝ)| := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h1 : (C : ℝ) + 1 ≤ (D : ℝ) := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (D : ℝ) - (C : ℝ))]
      linarith
    · have h1 : (D : ℝ) + 1 ≤ (C : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (C : ℝ) - (D : ℝ))]
      linarith
  have hdiff : countingProbability n C - countingProbability n D
      = ((C : ℝ) - (D : ℝ)) / (2 : ℝ) ^ n := by
    unfold countingProbability
    ring
  rw [hdiff, abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_right hCD hden.le

theorem exact_count_unique {n : ℕ} (hn : 2 ≤ n) {C D : ℕ} (hC : C ≤ 2 ^ n)
    (hD : D ≤ 2 ^ n) (p : ℝ)
    (hpC : |p - countingProbability n C| ≤ exactCountingPrecision n)
    (hpD : |p - countingProbability n D| ≤ exactCountingPrecision n) :
    C = D := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  by_contra hne
  have hsep := countingProbability_separation hC hD hne
  have htri : |countingProbability n C - countingProbability n D| ≤
      2 * exactCountingPrecision n := by
    have h1 : |countingProbability n C - countingProbability n D|
        = |(countingProbability n C - p) + (p - countingProbability n D)| := by
      congr 1
      ring
    rw [h1]
    calc |(countingProbability n C - p) + (p - countingProbability n D)|
        ≤ |countingProbability n C - p| + |p - countingProbability n D| := abs_add_le _ _
      _ ≤ exactCountingPrecision n + exactCountingPrecision n := by
          have h1 : |countingProbability n C - p| ≤ exactCountingPrecision n := by
            rw [abs_sub_comm]
            exact hpC
          linarith
      _ = 2 * exactCountingPrecision n := by ring
  have hprec : 2 * exactCountingPrecision n < (1 : ℝ) / (2 : ℝ) ^ n := by
    have h2n : (2 : ℝ) < (2 : ℝ) ^ n := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
        _ < (2 : ℝ) ^ n := pow_lt_pow_right₀ (by norm_num) (by omega)
    unfold exactCountingPrecision
    rw [show (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ n * (2 : ℝ) ^ n by
      rw [← pow_add]
      congr 1
      omega]
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) hden]
    nlinarith [hden, h2n, mul_pos hden (by linarith : (0 : ℝ) < (2 : ℝ) ^ n - 2)]
  linarith

theorem exact_counting_precision_log (n : ℕ) :
    Real.log (1 / exactCountingPrecision n) = 2 * (n : ℝ) * Real.log 2 := by
  unfold exactCountingPrecision
  rw [one_div_one_div, Real.log_pow]
  push_cast
  ring

theorem exact_counting_precision_log_neg (n : ℕ) :
    Real.log (exactCountingPrecision n) = -(2 * (n : ℝ) * Real.log 2) := by
  have h : exactCountingPrecision n = (1 / exactCountingPrecision n)⁻¹ := by
    rw [one_div, inv_inv]
  rw [h, Real.log_inv, exact_counting_precision_log]

structure MatrixInversionEstimationInstance (N : ℕ) where

  A : Matrix (Fin N) (Fin N) ℂ

  herm : A.IsHermitian

  b : QState (Fin N)

  conditionBound : ℝ

  conditionBound_pos : 0 < conditionBound

end Qatlib.Papers.LinearSystems09.AccuracyLower
