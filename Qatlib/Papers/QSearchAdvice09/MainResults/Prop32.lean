/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.QSearchAdvice09.MainResults.AmplifyCost
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Finset

namespace Qatlib.Papers.QSearchAdvice09.MainResults

def algThreeK : ℝ := 1162 / 1000

theorem algThreeK_bounds : 1 < algThreeK ∧ algThreeK < 4 / 3 := by
  constructor <;> norm_num [algThreeK]

theorem floor_pow_le (k : ℝ) (hk : 0 ≤ k) (i : ℕ) :
    ((⌊k ^ i⌋₊ : ℕ) : ℝ) ≤ k ^ i :=
  Nat.floor_le (pow_nonneg hk i)

theorem three_mul_le_pow_add_one (j : ℕ) :
    3 * (j : ℝ) * (algThreeK - 1) ≤ algThreeK ^ j + 1 := by
  have hk1 : (1 : ℝ) ≤ algThreeK := (algThreeK_bounds).1.le
  rcases le_or_gt j 8 with hj | hj
  · interval_cases j <;> norm_num [algThreeK]
  · have key : ∀ n : ℕ, 8 ≤ n → 3 * (n : ℝ) * (algThreeK - 1) ≤ algThreeK ^ n + 1 := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => norm_num [algThreeK]
      | succ n hn ih =>
        have hkn : (3 : ℝ) ≤ algThreeK ^ n := by
          have hmono : algThreeK ^ 8 ≤ algThreeK ^ n := pow_le_pow_right₀ hk1 hn
          have h8v : (3 : ℝ) ≤ algThreeK ^ 8 := by norm_num [algThreeK]
          linarith
        have hD : 0 < algThreeK - 1 := by norm_num [algThreeK]
        have hpow : 0 ≤ algThreeK ^ n := pow_nonneg (by linarith) n
        rw [pow_succ]
        push_cast
        nlinarith [ih, hD, hpow, hkn]
    exact key j (by omega)

theorem roundCost_le (j : ℕ) :
    roundCost algThreeK j ≤ algThreeK ^ j / (algThreeK - 1) := by
  have hk1 : (1 : ℝ) < algThreeK := (algThreeK_bounds).1
  have hk0 : (0 : ℝ) ≤ algThreeK := le_of_lt (by linarith : (0 : ℝ) < algThreeK)
  have hD : 0 < algThreeK - 1 := by linarith
  have hle : roundCost algThreeK j ≤ ∑ i ∈ range j, (algThreeK ^ i + 3) / 2 := by
    unfold roundCost
    apply sum_le_sum
    intro i _
    have h := floor_pow_le algThreeK hk0 i
    linarith
  have hsum : ∑ i ∈ range j, (algThreeK ^ i + 3) / 2
      = ((algThreeK ^ j - 1) / (algThreeK - 1) + 3 * (j : ℝ)) / 2 := by
    have hsplit : ∑ i ∈ range j, (algThreeK ^ i + 3) / 2
        = ((∑ i ∈ range j, algThreeK ^ i) + ∑ _i ∈ range j, (3 : ℝ)) / 2 := by
      rw [← sum_div, sum_add_distrib]
    rw [hsplit, geom_range algThreeK (ne_of_gt hk1), sum_const, card_range,
      nsmul_eq_mul]
    ring
  have hmain : ((algThreeK ^ j - 1) / (algThreeK - 1) + 3 * (j : ℝ)) / 2
      ≤ algThreeK ^ j / (algThreeK - 1) := by
    have hkey := three_mul_le_pow_add_one j
    have hpow : 0 ≤ algThreeK ^ j := pow_nonneg hk0 j
    field_simp
    nlinarith [hkey, hpow, hD]
  linarith [hle, hsum, hmain]

theorem first_success_sum_le_one (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i)
    (hP1 : ∀ i, P i ≤ 1) (n : ℕ) :
    ∑ j ∈ range n, (∏ i ∈ range j, (1 - P i)) * P j ≤ 1 := by
  have htel : ∀ n : ℕ,
      1 - ∏ i ∈ range n, (1 - P i) = ∑ j ∈ range n, (∏ i ∈ range j, (1 - P i)) * P j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [prod_range_succ, sum_range_succ, ← ih]
      ring
  rw [← htel]
  have hprod_le : ∏ i ∈ range n, (1 - P i) ≤ 1 := by
    refine Finset.prod_le_one₀ ?_ ?_
    · intro i _
      linarith [hP0 i, hP1 i]
    · intro i _
      linarith [hP0 i]
  have hprod_nonneg : 0 ≤ ∏ i ∈ range n, (1 - P i) := by
    refine Finset.prod_nonneg ?_
    intro i _
    linarith [hP1 i]
  linarith

theorem worstCaseSum_le (n J : ℕ) (hJ : algThreeK ^ J ≤ Real.sqrt (n : ℝ)) :
    ∑ j ∈ range (J + 1), roundCost algThreeK (j + 1)
      ≤ algThreeK ^ 2 / (algThreeK - 1) ^ 2 * Real.sqrt (n : ℝ) := by
  have hk1 : (1 : ℝ) < algThreeK := (algThreeK_bounds).1
  have hk0 : (0 : ℝ) ≤ algThreeK := le_of_lt (by linarith : (0 : ℝ) < algThreeK)
  have hD : 0 < algThreeK - 1 := by linarith
  have hbound : ∑ j ∈ range (J + 1), roundCost algThreeK (j + 1)
      ≤ ∑ j ∈ range (J + 1), algThreeK ^ (j + 1) / (algThreeK - 1) := by
    apply sum_le_sum
    intro j _
    exact roundCost_le (j + 1)
  have hgeo : ∑ j ∈ range (J + 1), algThreeK ^ (j + 1) / (algThreeK - 1)
      = algThreeK / (algThreeK - 1) *
          ∑ i ∈ range (J + 1), algThreeK ^ i := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  have hgeom := geom_range algThreeK (ne_of_gt hk1) (J + 1)
  have hsum_eq : ∑ i ∈ range (J + 1), algThreeK ^ i
      = (algThreeK ^ (J + 1) - 1) / (algThreeK - 1) := hgeom
  have hkey : ∑ j ∈ range (J + 1), algThreeK ^ (j + 1) / (algThreeK - 1)
      ≤ algThreeK ^ 2 / (algThreeK - 1) ^ 2 * Real.sqrt (n : ℝ) := by
    rw [hgeo, hsum_eq]
    have hsq : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hkJ : algThreeK ^ (J + 1) ≤ algThreeK * Real.sqrt (n : ℝ) := by
      rw [pow_succ]
      calc algThreeK ^ J * algThreeK = algThreeK * algThreeK ^ J := by ring
        _ ≤ algThreeK * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_left hJ hk0
    have hnum : (algThreeK ^ (J + 1) - 1) / (algThreeK - 1) ≤ algThreeK ^ (J + 1) / (algThreeK - 1) := by
      apply div_le_div_of_nonneg_right _ hD.le
      linarith [pow_pos (by linarith : (0:ℝ) < algThreeK) (J + 1)]
    have hmulpos : 0 ≤ algThreeK / (algThreeK - 1) := by positivity
    calc algThreeK / (algThreeK - 1) * ((algThreeK ^ (J + 1) - 1) / (algThreeK - 1))
        ≤ algThreeK / (algThreeK - 1) * (algThreeK ^ (J + 1) / (algThreeK - 1)) := by
          apply mul_le_mul_of_nonneg_left hnum hmulpos
      _ = algThreeK * algThreeK ^ (J + 1) / (algThreeK - 1) ^ 2 := by
          field_simp
      _ ≤ algThreeK * (algThreeK * Real.sqrt (n : ℝ)) / (algThreeK - 1) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hkJ hk0
      _ = algThreeK ^ 2 / (algThreeK - 1) ^ 2 * Real.sqrt (n : ℝ) := by
          field_simp
  linarith

theorem worstCase_const53 (n J : ℕ) (hJ : algThreeK ^ J ≤ Real.sqrt (n : ℝ)) :
    ∑ j ∈ range (J + 1), roundCost algThreeK (j + 1) + Real.pi / 4 * Real.sqrt (n : ℝ)
      ≤ 53 * Real.sqrt (n : ℝ) := by
  have hsum := worstCaseSum_le n J hJ
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hcoef : algThreeK ^ 2 / (algThreeK - 1) ^ 2 + Real.pi / 4 ≤ 53 := by
    have hp : Real.pi / 4 ≤ 0.7854 := by nlinarith [Real.pi_lt_d4]
    have hk : algThreeK ^ 2 / (algThreeK - 1) ^ 2 ≤ 51.45 := by norm_num [algThreeK]
    linarith
  calc ∑ j ∈ range (J + 1), roundCost algThreeK (j + 1) + Real.pi / 4 * Real.sqrt (n : ℝ)
      ≤ algThreeK ^ 2 / (algThreeK - 1) ^ 2 * Real.sqrt (n : ℝ)
          + Real.pi / 4 * Real.sqrt (n : ℝ) := by linarith
    _ = (algThreeK ^ 2 / (algThreeK - 1) ^ 2 + Real.pi / 4) * Real.sqrt (n : ℝ) := by ring
    _ ≤ 53 * Real.sqrt (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right hcoef hs

theorem firstBranch_const83 :
    algThreeK / (algThreeK - 1)
        + 4 * algThreeK ^ 2 / ((algThreeK - 1) * (4 - 3 * algThreeK))
        + 4 * algThreeK / (3 * (algThreeK - 1)) + Real.pi / 3 ≤ 83 := by
  have hp : Real.pi / 3 ≤ 1.0472 := by nlinarith [Real.pi_lt_d4]
  have hk : algThreeK / (algThreeK - 1)
        + 4 * algThreeK ^ 2 / ((algThreeK - 1) * (4 - 3 * algThreeK))
        + 4 * algThreeK / (3 * (algThreeK - 1)) ≤ 81.9 := by
    norm_num [algThreeK]
  linarith

theorem threeQuarter_const :
    3 / ((algThreeK - 1) * (4 - algThreeK))
        + algThreeK / (algThreeK - 1) + 2 + Real.pi / 4 ≤ 16.5 := by
  have hp : Real.pi / 4 ≤ 0.7854 := by nlinarith [Real.pi_lt_d4]
  have hk : 3 / ((algThreeK - 1) * (4 - algThreeK))
        + algThreeK / (algThreeK - 1) + 2 ≤ 15.71 := by
    norm_num [algThreeK]
  linarith

end Qatlib.Papers.QSearchAdvice09.MainResults
