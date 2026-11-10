/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

namespace Qatlib.Papers.JonesPoly06.MainResults

def signX : Fin 4 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => -1
  | 3 => -1

def signY : Fin 4 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 3 => -1

theorem signX_val (i : Fin 4) : signX i = 1 ∨ signX i = -1 := by
  fin_cases i <;> simp [signX]

theorem signY_val (i : Fin 4) : signY i = 1 ∨ signY i = -1 := by
  fin_cases i <;> simp [signY]

def signLaw (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1) : FinDist (Fin 4) where
  prob i := ((1 + signX i * z.re) * (1 + signY i * z.im)) / 4
  nonneg i := by
    have hxle : z.re ≤ 1 := by nlinarith [hz, sq_nonneg z.im, sq_nonneg (z.re - 1)]
    have hxge : -1 ≤ z.re := by nlinarith [hz, sq_nonneg z.im, sq_nonneg (z.re + 1)]
    have hyle : z.im ≤ 1 := by nlinarith [hz, sq_nonneg z.re, sq_nonneg (z.im - 1)]
    have hyge : -1 ≤ z.im := by nlinarith [hz, sq_nonneg z.re, sq_nonneg (z.im + 1)]
    have h1 : (0 : ℝ) ≤ 1 + signX i * z.re := by
      rcases signX_val i with h | h <;> rw [h] <;> nlinarith
    have h2 : (0 : ℝ) ≤ 1 + signY i * z.im := by
      rcases signY_val i with h | h <;> rw [h] <;> nlinarith
    positivity
  sum_one := by
    simp [Fin.sum_univ_four, signX, signY]
    ring

theorem signLaw_expectX (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1) :
    (signLaw z hz).expect signX = z.re := by
  simp only [FinDist.expect, signLaw, Fin.sum_univ_four, signX, signY]
  ring

theorem signLaw_expectY (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1) :
    (signLaw z hz).expect signY = z.im := by
  simp only [FinDist.expect, signLaw, Fin.sum_univ_four, signX, signY]
  ring

theorem SourceLemma61 (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1) :
    ∃ p : FinDist (Fin 4),
      p.expect signX = z.re ∧ p.expect signY = z.im ∧
      (∀ i, signX i = 1 ∨ signX i = -1) ∧
      (∀ i, signY i = 1 ∨ signY i = -1) :=
  ⟨signLaw z hz, signLaw_expectX z hz, signLaw_expectY z hz, signX_val, signY_val⟩

theorem samples_suffice (δ : ℝ) (hδ : 0 < δ) (M : ℕ)
    (hM : 8 * Real.log 16 / δ ^ 2 ≤ (M : ℝ)) :
    4 * Real.exp (-((M : ℝ) * δ ^ 2 / 8)) ≤ 1 / 4 := by
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have h1 : Real.log 16 ≤ (M : ℝ) * δ ^ 2 / 8 := by
    have h2 : 8 * Real.log 16 ≤ (M : ℝ) * δ ^ 2 := by
      rw [div_le_iff₀ hδ2] at hM
      linarith
    linarith
  have hexp : Real.exp (-((M : ℝ) * δ ^ 2 / 8)) ≤ (1 / 16 : ℝ) := by
    have h2 : Real.exp (-((M : ℝ) * δ ^ 2 / 8)) ≤ Real.exp (-(Real.log 16)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (-(Real.log 16)) = (1 / 16 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
      norm_num
    linarith
  nlinarith [hexp]

end Qatlib.Papers.JonesPoly06.MainResults
