/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Theorem3CorrectedAfas
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh
import Mathlib.Analysis.Real.Pi.Bounds
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.GroverSearch96.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount

theorem gain_formula (n : ℕ) (k l : ℝ) :
    distinguishedAfter (2 ^ n) (-k) l - k =
      -(2 * k / (2 ^ n : ℝ)) + 2 * (1 - 1 / (2 ^ n : ℝ)) * l := by
  have hN : ((2 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  unfold distinguishedAfter
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring

theorem theorem3_markedRegister (n : ℕ) (hn : 3 ≤ n) (w : Reg n) (k l : ℝ)
    (hk0 : 0 < k) (hk : k < 1 / Real.sqrt 2) (hl : 0 < l)
    (hnorm : Normalized (MarkedVector ({w} : Finset (Reg n)) (k : ℂ) (l : ℂ))) :
    1 / (2 * Real.sqrt (2 ^ n : ℝ)) < distinguishedAfter (2 ^ n) (-k) l - k ∧
      0 < ordinaryAfter (2 ^ n) (-k) l := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmass : twoAmplitudeMass (2 ^ n) k l = 1 := by
    have h := (normalized_markedVector_iff ({w} : Finset (Reg n)) (k : ℂ) (l : ℂ)).mp hnorm
    rw [Finset.card_singleton] at h
    rw [card_reg, Nat.cast_pow] at h
    unfold twoAmplitudeMass
    simpa [Complex.normSq_ofReal, pow_two] using h
  have h := theorem3Corrected (2 ^ n) h8 k l hk0 hk hl hmass
  simpa [Nat.cast_pow] using h

theorem section4_success_iterations (n : ℕ) (hn : 2 ≤ n) (w : Reg n) :
    ∃ j : ℕ, (j : ℝ) < Real.sqrt (2 * (2 : ℝ) ^ n) ∧
      1 / 2 < MeasureProb (GroverState ({w} : Finset (Reg n)) j) {w} := by
  have hcard : Fintype.card (Reg n) = 2 ^ n := card_reg n
  have hNr : (0 : ℝ) < (Fintype.card (Reg n) : ℝ) := by positivity
  have hcard_gt : 1 < Fintype.card (Reg n) := by
    rw [hcard]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  let j : ℕ := groverIterations (knownCountAngle ((1 : ℝ) / Fintype.card (Reg n)))
  have hbudget : (j : ℝ) ≤
      Real.pi / (4 * Real.sqrt ((1 : ℝ) / Fintype.card (Reg n))) := by
    dsimp only [j]
    simpa using knownCount_query_budget (I := Reg n) (m := 1) (by norm_num) hcard_gt
  have hrewrite : Real.pi / (4 * Real.sqrt ((1 : ℝ) / Fintype.card (Reg n))) =
      Real.pi / 4 * Real.sqrt (Fintype.card (Reg n) : ℝ) := by
    have hs : Real.sqrt ((1 : ℝ) / (Fintype.card (Reg n) : ℝ)) =
        1 / Real.sqrt (Fintype.card (Reg n) : ℝ) := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    rw [hs]
    have hne : Real.sqrt (Fintype.card (Reg n) : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
    field_simp
  have hle : (j : ℝ) ≤
      Real.pi / 4 * Real.sqrt (Fintype.card (Reg n) : ℝ) := by
    rw [hrewrite] at hbudget
    exact hbudget
  have hpi4 : Real.pi / 4 < 1 := by
    have h := Real.pi_lt_d2
    linarith
  have hlt_sqrt : (j : ℝ) < Real.sqrt (Fintype.card (Reg n) : ℝ) := by
    have hpos : 0 < Real.sqrt (Fintype.card (Reg n) : ℝ) := Real.sqrt_pos.2 hNr
    calc (j : ℝ) ≤ Real.pi / 4 * Real.sqrt (Fintype.card (Reg n) : ℝ) := hle
      _ < 1 * Real.sqrt (Fintype.card (Reg n) : ℝ) := by nlinarith
      _ = Real.sqrt (Fintype.card (Reg n) : ℝ) := one_mul _
  have hlt : (j : ℝ) < Real.sqrt (2 * (2 : ℝ) ^ n) := by
    have h2 : Real.sqrt (Fintype.card (Reg n) : ℝ) <
        Real.sqrt (2 * (Fintype.card (Reg n) : ℝ)) :=
      Real.sqrt_lt_sqrt hNr.le (by linarith)
    rw [hcard, Nat.cast_pow] at h2
    exact lt_trans hlt_sqrt (by simpa [Nat.cast_pow] using h2)
  have hN4 : 4 ≤ Fintype.card (Reg n) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hsuccess : 1 - (1 : ℝ) / (Fintype.card (Reg n) : ℝ) ≤
      MeasureProb (GroverState ({w} : Finset (Reg n)) j) {w} := by
    dsimp only [j]
    simpa using knownCount_success (I := Reg n) Fintype.card_pos ({w} : Finset (Reg n))
      (m := 1) (by simp) (by norm_num) hcard_gt
  have hhalf : (1 : ℝ) / 2 < 1 - (1 : ℝ) / (Fintype.card (Reg n) : ℝ) := by
    have hq : (1 : ℝ) / (Fintype.card (Reg n) : ℝ) ≤ 1 / 4 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      exact_mod_cast hN4
    linarith
  exact ⟨j, hlt, lt_of_lt_of_le hhalf hsuccess⟩

end Qatlib.Papers.GroverSearch96.MainResults
