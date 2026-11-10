/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.HamNANDTree07.MainResults.AlgorithmGuarantee

def runwayLength (γ : ℝ) (N : ℕ) : ℝ := γ * Real.sqrt N

def runTime (γ : ℝ) (N : ℕ) : ℝ := runwayLength γ N / 2

def decideRight (foundOnRight : Bool) : Bool := foundOnRight

def failureProb (pZero pOne : ℝ) : Bool → ℝ
  | false => pZero
  | true => 1 - pOne

theorem runTime_eq (γ : ℝ) (N : ℕ) :
    runTime γ N = γ * Real.sqrt N / 2 ∧ runTime γ N = (γ / 2) * Real.sqrt N := by
  unfold runTime runwayLength
  constructor <;> ring

theorem runTime_nonneg (γ : ℝ) (N : ℕ) (hγ : 0 ≤ γ) : 0 ≤ runTime γ N := by
  unfold runTime runwayLength
  positivity

theorem runTime_le_scaled_sqrt (γ : ℝ) (N : ℕ) (hγ : 0 ≤ γ) :
    runTime γ N ≤ (γ / 2) * Real.sqrt N := by
  rw [(runTime_eq γ N).2]

theorem failureProb_le (pZero pOne η : ℝ)
    (hZero : pZero ≤ η) (hOne : 1 - pOne ≤ η) :
    failureProb pZero pOne false ≤ η ∧ failureProb pZero pOne true ≤ η :=
  ⟨hZero, hOne⟩

theorem exists_gamma_for_small_error (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ γ : ℝ, 1 ≤ γ ∧ C / Real.sqrt γ < ε := by
  refine ⟨max 1 ((C / ε) ^ 2 + 1), le_max_left _ _, ?_⟩
  have hγ1 : (1 : ℝ) ≤ max 1 ((C / ε) ^ 2 + 1) := le_max_left _ _
  have hγpos : (0 : ℝ) < max 1 ((C / ε) ^ 2 + 1) := lt_of_lt_of_le zero_lt_one hγ1
  have hbig : (C / ε) ^ 2 < max 1 ((C / ε) ^ 2 + 1) := by
    have := le_max_right (1 : ℝ) ((C / ε) ^ 2 + 1)
    nlinarith
  have hx_nonneg : (0 : ℝ) ≤ C / ε := by positivity
  have hsqrt : C / ε < Real.sqrt (max 1 ((C / ε) ^ 2 + 1)) := by
    rw [Real.lt_sqrt hx_nonneg]
    exact hbig
  rw [div_lt_iff₀ (Real.sqrt_pos.mpr hγpos)]
  have hmul : C < Real.sqrt (max 1 ((C / ε) ^ 2 + 1)) * ε :=
    (div_lt_iff₀ hε).mp hsqrt
  nlinarith [hmul]

theorem hamiltonian_nand_tree_algorithm_guarantee
    (N : ℕ) (hN : 1 ≤ N) (γ C η : ℝ) (hγ : 1 ≤ γ)
    (hη : η ≤ C / Real.sqrt γ) (hC : 0 ≤ C)
    (pZero pOne : ℝ) (hZero : pZero ≤ η) (hOne : 1 - pOne ≤ η) :
    ∃ tRun : ℝ,
      tRun = γ * Real.sqrt N / 2 ∧
      0 ≤ tRun ∧
      failureProb pZero pOne false ≤ C / Real.sqrt γ ∧
      failureProb pZero pOne true ≤ C / Real.sqrt γ := by
  refine ⟨runTime γ N, (runTime_eq γ N).1, runTime_nonneg γ N (by linarith), ?_, ?_⟩
  · exact le_trans (failureProb_le pZero pOne η hZero hOne).1 hη
  · exact le_trans (failureProb_le pZero pOne η hZero hOne).2 hη

end Qatlib.Papers.HamNANDTree07.MainResults.AlgorithmGuarantee
