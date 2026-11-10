/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.CostModels.TCountBudget
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MonteCarloInt20.CostModels.Corrected

def jumpIndexWidth (sampleBits termBits : ℕ) : ℕ :=
  sampleBits + termBits + 1 + if termBits = 0 then 1 else 0

theorem jumpIndexWidth_positive_terms (s d : ℕ) (hd : 0 < d) :
    jumpIndexWidth s d = s+d+1 := by simp [jumpIndexWidth, Nat.ne_of_gt hd]

theorem jumpIndexWidth_single_term (s : ℕ) : jumpIndexWidth s 0 = s+2 := by
  simp [jumpIndexWidth]

def nonselfFee (rngBits : ℕ) : ℕ := 70*rngBits^2

theorem reported_self_update_fee (n : ℕ) : Reported.tcountSelfUpdate n = 2*nonselfFee n := by
  simp [Reported.tcountSelfUpdate, nonselfFee]
  ring

def jumpFee (s d n : ℕ) : ℕ := 2*jumpIndexWidth s d*nonselfFee n

def newFee (s d n p r : ℕ) : ℕ :=
  2*jumpFee s d n + 2*Reported.tcountConversion p r

theorem newFee_formula (s d n p r : ℕ) (hd : 0 < d) :
    newFee s d n p r = 280*(s+d+1)*n^2+210*p^2+56*p*r := by
  simp only [newFee, jumpFee, jumpIndexWidth_positive_terms s d hd,
    nonselfFee, Reported.tcountConversion]
  ring

theorem corrected_example : newFee 20 20 64 16 109 = 47173504 := by
  norm_num [newFee, jumpFee, jumpIndexWidth, nonselfFee, Reported.tcountConversion]

def exampleMultiplier : ℝ := (newFee 20 20 64 16 109 : ℝ) / (Reported.tcountPrevTypical : ℝ)

theorem exampleMultiplier_exact : exampleMultiplier = 52649/809 := by
  rw [exampleMultiplier, corrected_example, Reported.tcount_prev_typical]
  norm_num

theorem exampleMultiplier_bounds : 65 < exampleMultiplier ∧ exampleMultiplier < 66 := by
  rw [exampleMultiplier_exact]
  norm_num

def totalRatio (scale relativeError dimensions : ℝ) : ℝ :=
  exampleMultiplier * ((scale*relativeError)⁻¹/dimensions)

theorem total_example : totalRatio (1/100) (1/100) (2^20) = 32905625/53018624 := by
  rw [totalRatio, exampleMultiplier_exact]
  norm_num

theorem total_example_below_one : totalRatio (1/100) (1/100) (2^20) < 1 := by
  rw [total_example]
  norm_num

end Qatlib.Papers.MonteCarloInt20.CostModels.Corrected
