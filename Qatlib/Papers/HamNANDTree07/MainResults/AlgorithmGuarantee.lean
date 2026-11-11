/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Conditional Hamiltonian NAND-tree runtime guarantee

This module defines the runway length `runwayLength`, runtime `runTime`, and the two
input-dependent error expressions `failureProb`. Given bounds on the supplied outcome
probabilities, `hamiltonian_nand_tree_algorithm_guarantee` packages runtime γ√N/2 and error at
most C/√γ; `exists_gamma_for_small_error` shows how increasing γ makes this error bound
arbitrarily small. See [FarhiGoldstoneGutmann2008] for the Hamiltonian NAND-tree setting.

## Main statements

* `hamiltonian_nand_tree_algorithm_guarantee`: For N ≥ 1 and γ ≥ 1, the supplied
  outcome-probability bounds and η ≤ C / √γ with C ≥ 0 yield a nonnegative runtime γ√N / 2 and
  errors at most C / √γ for both inputs.
* `exists_gamma_for_small_error`: For C > 0 and ε > 0, there exists γ ≥ 1 such that C / √γ < ε.

## References

* [Farhi et al., 2008][FarhiGoldstoneGutmann2008]
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.HamNANDTree07.MainResults.AlgorithmGuarantee

/-- The runway length γ√N for the Hamiltonian NAND-tree runtime estimate. -/
def runwayLength (γ : ℝ) (N : ℕ) : ℝ := γ * Real.sqrt N

/-- The runtime equal to half of `runwayLength γ N`. -/
def runTime (γ : ℝ) (N : ℕ) : ℝ := runwayLength γ N / 2

/-- The Boolean decision rule returning the observation `foundOnRight`. -/
def decideRight (foundOnRight : Bool) : Bool := foundOnRight

/-- The input-dependent error expression, equal to pZero on false and 1 − pOne on true. -/
def failureProb (pZero pOne : ℝ) : Bool → ℝ
  | false => pZero
  | true => 1 - pOne

/-- The runtime equals both γ√N / 2 and (γ / 2)√N. -/
theorem runTime_eq (γ : ℝ) (N : ℕ) :
    runTime γ N = γ * Real.sqrt N / 2 ∧ runTime γ N = (γ / 2) * Real.sqrt N := by
  unfold runTime runwayLength
  constructor <;> ring

/-- The runtime is nonnegative whenever γ is nonnegative. -/
theorem runTime_nonneg (γ : ℝ) (N : ℕ) (hγ : 0 ≤ γ) : 0 ≤ runTime γ N := by
  unfold runTime runwayLength
  positivity

/-- For γ ≥ 0, the runtime is at most (γ / 2)√N. -/
theorem runTime_le_scaled_sqrt (γ : ℝ) (N : ℕ) (hγ : 0 ≤ γ) :
    runTime γ N ≤ (γ / 2) * Real.sqrt N := by
  rw [(runTime_eq γ N).2]

/-- Bounds both input-dependent error expressions by η from pZero ≤ η and 1 − pOne ≤ η. -/
theorem failureProb_le (pZero pOne η : ℝ)
    (hZero : pZero ≤ η) (hOne : 1 - pOne ≤ η) :
    failureProb pZero pOne false ≤ η ∧ failureProb pZero pOne true ≤ η :=
  ⟨hZero, hOne⟩

/-- For C > 0 and ε > 0, there exists γ ≥ 1 such that C / √γ < ε. See
[FarhiGoldstoneGutmann2008]. -/
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

/-- For N ≥ 1 and γ ≥ 1, the supplied outcome-probability bounds and η ≤ C / √γ with C ≥ 0 yield
a nonnegative runtime γ√N / 2 and errors at most C / √γ for both inputs. See
[FarhiGoldstoneGutmann2008]. -/
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
