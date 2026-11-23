/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Qatlib.Papers.PhaseEst07.MainResults.ShorOptimal
import Qatlib.Papers.QWalkGraphs00.MainResults.Times

/-!
# Sampling and phase-estimation boundary cases

The singleton identity walk satisfies the sampling premise with zero error at length one.
The standard periodic variance enters both optimality theorems with its original coefficients.
-/

namespace QatlibTests.PaperAuditRegression

open Qatlib.Papers.QWalkGraphs00.MainResults.Core
open Qatlib.Papers.QWalkGraphs00.MainResults.Times
open scoped BigOperators Matrix

private abbrev Site := Unit × Unit

private def singletonWalk : Matrix Site Site ℂ := 1

private def singletonReference (_ : Site → ℂ) (_ : Unit) : ℝ := 1

example : singletonWalk.conjTranspose * singletonWalk = 1 := by
  simp [singletonWalk]

example : IsMixingTime singletonWalk singletonReference 0 1 ∧
    IsFillingTime singletonWalk singletonReference 0 1 ∧
    IsDispersionTime singletonWalk singletonReference 0 1 := by
  apply theorem_3_12 singletonWalk singletonReference 0 1 (by simp [singletonReference])
    Nat.zero_lt_one
  intro T hT p X
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  have hpoint (t : ℕ) (v : Unit) : nodeProb singletonWalk (walkBasisState p) t v = 1 := by
    obtain ⟨⟨⟩, ⟨⟩⟩ := p
    cases v
    simp [nodeProb, singletonWalk, walkBasisState]
  have havg (v : Unit) : avgNodeProb singletonWalk (walkBasisState p) T v = 1 := by
    simp [avgNodeProb, hpoint, hTne]
  simp [singletonReference, avgSetProb, havg]

open Qatlib.Papers.PhaseEst07.MainResults.OptimalPOVM
open Qatlib.Papers.PhaseEst07.MainResults.ShorOptimal

private def varianceCoefficients (l : ℕ) : ℝ :=
  if l = 0 then -2 else if l = 1 then 2 else 0

private theorem varianceCoefficients_nonneg (l : ℕ) (hl : 1 ≤ l) : 0 ≤ varianceCoefficients l := by
  have hne : l ≠ 0 := by omega
  simp only [varianceCoefficients, ite_eq_right hne]
  split_ifs <;> norm_num

private noncomputable def balancedAmplitude (_ : Fin 2) : ℝ := 1 / Real.sqrt 2

private theorem balancedAmplitude_pos (j : Fin 2) : 0 < balancedAmplitude j := by
  unfold balancedAmplitude
  positivity

example (χ : Fin 2 → Fin 2 → ℝ) (hχ : ∀ h k, |χ h k| ≤ 1) :
    sourceHolevoCost varianceCoefficients balancedAmplitude sourceUnitChi ≤
      sourceHolevoCost varianceCoefficients balancedAmplitude χ :=
  (source_holevo_cost_optimal (by decide) varianceCoefficients varianceCoefficients_nonneg
    balancedAmplitude balancedAmplitude_pos χ hχ).1

example : sourceHolevoCost varianceCoefficients balancedAmplitude sourceUnitChi = 1 := by
  rw [(source_shor_qft_measurement_optimal (by decide) varianceCoefficients
    varianceCoefficients_nonneg balancedAmplitude balancedAmplitude_pos).2.2]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  norm_num [varianceCoefficients, balancedAmplitude, sourceDist, Fin.sum_univ_two]
  field_simp
  linarith

end QatlibTests.PaperAuditRegression
