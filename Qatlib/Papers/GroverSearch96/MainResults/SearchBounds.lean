/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalAfas
import Qatlib.Concepts.SearchStopping.KnownCount.SummarySearchOptimalityAfas
import Qatlib.Concepts.SearchStopping.KnownCount.Section6LowerBoundSubgoalAfas
import Qatlib.Concepts.SearchStopping.KnownCount.PreparedSearch
import Mathlib.Analysis.Real.Pi.Bounds
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.GroverSearch96.MainResults

open Matrix
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.QueryWordCore.QueryMachinery

theorem budget_rewrite (n : ℕ) :
    Real.pi / (4 * Real.sqrt ((1 : ℝ) / Fintype.card (Reg n))) =
      Real.pi / 4 * Real.sqrt (2 ^ n : ℝ) := by
  have hcard : ((Fintype.card (Reg n) : ℝ)) = (2 : ℝ) ^ n := by
    rw [card_reg, Nat.cast_pow]
    norm_num
  have hs : Real.sqrt ((1 : ℝ) / ((2 : ℝ) ^ n)) =
      1 / Real.sqrt ((2 : ℝ) ^ n) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  rw [hcard, hs]
  have hne : Real.sqrt ((2 : ℝ) ^ n) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp

theorem section3_algorithm (n : ℕ) (hn : 1 ≤ n) :
    ∃ k : ℕ, (k : ℝ) ≤ Real.pi / 4 * Real.sqrt (2 ^ n : ℝ) ∧
      FixedSpaceQueryUpperBound (MarkOracle (I := Reg n)) (fun w => {w}) (1 / 2) k := by
  have hN : 2 ≤ Fintype.card (Reg n) := by
    rw [card_reg]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hupper, hbudget⟩ := section3QueryBoundSubgoal (Reg n) hN
  refine ⟨k, ?_, hupper⟩
  rw [budget_rewrite] at hbudget
  exact hbudget

theorem section3_prepared_algorithm (n : ℕ) (hn : 1 ≤ n) :
    ∃ j : ℕ, (j : ℝ) ≤ Real.pi / 4 * Real.sqrt (2 ^ n : ℝ) ∧
      FixedSpaceQueryUpperBound
        (fun A : KnownMarkedSets (Reg n) 1 => SetOracle A.val)
        (fun A => A.val) (1 / 2) j := by
  have hcard : Fintype.card (Reg n) = 2 ^ n := card_reg n
  have hNr : (0 : ℝ) < (Fintype.card (Reg n) : ℝ) := by positivity
  have hcard_gt : 1 < Fintype.card (Reg n) := by
    rw [hcard]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 * 1 ≤ Fintype.card (Reg n) := by omega
  let j : ℕ := groverIterations (knownCountAngle ((1 : ℝ) / Fintype.card (Reg n)))
  refine ⟨j, ?_, ?_⟩
  · have hbudget : (j : ℝ) ≤
        Real.pi / (4 * Real.sqrt ((1 : ℝ) / Fintype.card (Reg n))) := by
      dsimp only [j]
      simpa using knownCount_query_budget (I := Reg n) (m := 1) (by norm_num) hcard_gt
    rw [budget_rewrite] at hbudget
    exact hbudget
  · dsimp only [j]
    simpa using preparedGrover_knownCount_query_upper (n := n) (m := 1)
      (by norm_num) (by simpa using h2)

theorem summary_twoSided (n : ℕ) (hn : 1 ≤ n) :
    SingleTargetSearchClaim (Reg n) ∧
      FixedSpaceQueryLowerBound (MarkOracle (I := Reg n)) (fun w => {w}) (1 / 2)
        (Nat.floor (Real.sin (Real.pi / 8) * Real.sqrt (2 ^ n : ℝ))) := by
  have hN : 2 ≤ Fintype.card (Reg n) := by
    rw [card_reg]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨hupper, hlower⟩ := summarySearchOptimality (Reg n) hN
  refine ⟨hupper, ?_⟩
  simpa [card_reg, Nat.cast_pow] using hlower

theorem summary_constant_factor :
    Real.pi / (4 * Real.sin (Real.pi / 8)) < (21 / 10 : ℝ) := by
  have hsqrt2 : Real.sqrt 2 < 23 / 16 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 23 / 16)]
    norm_num
  have hsin : (3 / 8 : ℝ) < Real.sin (Real.pi / 8) := by
    have hlt : (3 / 4 : ℝ) < Real.sqrt (2 - Real.sqrt 2) := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      nlinarith
    rw [Real.sin_pi_div_eight]
    linarith
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpos : 0 < Real.sin (Real.pi / 8) := by linarith
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * Real.sin (Real.pi / 8))]
  nlinarith

theorem section6_lowerBound (n : ℕ) :
    FixedSpaceQueryLowerBound (MarkOracle (I := Reg n)) (fun w => {w}) (1 / 2)
      (Nat.floor (Real.sin (Real.pi / 8) * Real.sqrt (2 ^ n : ℝ))) := by
  have h := section6LowerBoundSubgoal (Reg n)
  simpa [card_reg, Nat.cast_pow] using h

end Qatlib.Papers.GroverSearch96.MainResults
