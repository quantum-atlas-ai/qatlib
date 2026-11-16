/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QDynamics10.MainResults.SourceModel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


/-! # Closed adaptive-step algebra, with source algorithm boundaries

The six historical closed results are retained as elementary ceiling,
resource and triangle-inequality statements. The last statement requires
integrator/roundoff bounds and the step count as inputs; it constructs no
Hamiltonian simulation or adaptive partition. Fixed actual source v2.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QDynamics10.MainResults.StepAlgebra
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Papers.QDynamics10.MainResults

/-- Preserved closed rg_ge_leading algebra; no source simulator is certified. -/
theorem rgLeading (k d : ℕ) (Υbar K Δt ε : ℝ)
    (hΥbar : 0 ≤ Υbar) (hΔt : 0 ≤ Δt) :
    Nat.ceil (adaptiveLeadingTerm k d Υbar Δt ε) ≤ adaptiveStepBound k d Υbar K Δt ε := by
  unfold adaptiveStepBound
  apply Nat.ceil_mono
  have : 0 ≤ 3 * K ^ 2 * Υbar * Δt + 1 := by positivity
  linarith

/-- Preserved closed adaptiveLeadingTerm_le_costCeilArg algebra; no source simulator is certified. -/
theorem leadingCost (k d : ℕ) (Υbar K Δt ε : ℝ)
    (hε : 0 < ε) (hΥbar : 0 ≤ Υbar) (hΔt : 0 ≤ Δt) :
    adaptiveLeadingTerm k d Υbar Δt ε + 3 * K ^ 2 * Υbar * Δt + 1
      ≤ adaptiveCostCeilArg k d Υbar K Δt ε := by
  have hs : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) := by positivity
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have hden : (ε / 4) ^ (1 / (2 * (k : ℝ))) ≤ ε ^ (1 / (2 * (k : ℝ))) :=
    Real.rpow_le_rpow hε4.le (by linarith) hs
  have hbase : (0 : ℝ) ≤
      ((24 : ℝ) * ((d : ℝ) ^ 2) * ((k : ℝ) * ((5 : ℝ) / 3) ^ (k - 1)) * Υbar * Δt)
        ^ (1 + 1 / ((2 : ℝ) * (k : ℝ))) :=
    Real.rpow_nonneg (by positivity) _
  have hAle : adaptiveLeadingTerm k d Υbar Δt ε
      ≤ ((24 : ℝ) * ((d : ℝ) ^ 2) * ((k : ℝ) * ((5 : ℝ) / 3) ^ (k - 1)) * Υbar * Δt)
          ^ (1 + 1 / ((2 : ℝ) * (k : ℝ))) / (ε / 4) ^ (1 / (2 * (k : ℝ))) := by
    unfold adaptiveLeadingTerm
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hε _) (Real.rpow_pos_of_pos hε4 _)]
    exact mul_le_mul_of_nonneg_left hden hbase
  unfold adaptiveCostCeilArg
  linarith

/-- Preserved closed queryCost_le_of_r_le_rg algebra; no source simulator is certified. -/
theorem queryCount (C M d k : ℕ) (Υbar K Δt ε : ℝ) (r : ℕ)
    (hε : 0 < ε) (hΥbar : 0 ≤ Υbar) (hΔt : 0 ≤ Δt)
    (hr : r ≤ adaptiveStepBound k d Υbar K Δt ε) :
    stepExponentials M d k * C * r
      ≤ adaptiveQueryCostBound C M d k Υbar K Δt ε := by
  have hceil := leadingCost k d Υbar K Δt ε hε hΥbar hΔt
  have hrs : r ≤ Nat.ceil (adaptiveCostCeilArg k d Υbar K Δt ε) :=
    le_trans hr (Nat.ceil_mono hceil)
  unfold adaptiveQueryCostBound
  exact Nat.mul_le_mul_left (stepExponentials M d k * C) hrs

/-- Preserved closed theorem8_error algebra; no source simulator is certified. -/
theorem errorSum {I : Type} [Fintype I] [DecidableEq I]
    (Uexact Umid Usim : Matrix I I ℂ) {ε : ℝ}
    (hRound : ‖Uexact - Umid‖ ≤ ε / 2) (hInteg : ‖Umid - Usim‖ ≤ ε / 2) :
    SimulatedWithinError Uexact Usim ε :=
  simulatedWithinError_of_two_halves Uexact Umid Usim hRound hInteg

/-- Preserved closed r_le_rg_of_eq58 algebra; no source simulator is certified. -/
theorem stepsCeil (k d : ℕ) (Υbar K Δt ε : ℝ) (r : ℕ)
    (h58 : (r : ℝ) ≤ adaptiveLeadingTerm k d Υbar Δt ε + 3 * K ^ 2 * Υbar * Δt + 1) :
    r ≤ adaptiveStepBound k d Υbar K Δt ε := by
  unfold adaptiveStepBound
  exact_mod_cast le_trans h58 (Nat.le_ceil _)

/-- Preserved closed theorem8 algebra; no source simulator is certified. -/
theorem conditionalAll {I : Type} [Fintype I] [DecidableEq I]
    (Uexact Umid Usim : Matrix I I ℂ) (C M d k NT : ℕ)
    (Υbar K Δt ε : ℝ) (r : ℕ)
    (hε : 0 < ε) (hΥbar : 0 ≤ Υbar) (hΔt : 0 ≤ Δt)
    (hd : 1 ≤ d) (hC : 1 ≤ C)
    (hRound : ‖Uexact - Umid‖ ≤ ε / 2)
    (hLemma7 : ‖Umid - Usim‖ ≤ ε / 2)
    (hr : r ≤ adaptiveStepBound k d Υbar K Δt ε)
    (hNT : NT * (3 * C * d ^ 2) ≤ stepExponentials M d k * C * r) :
    SimulatedWithinError Uexact Usim ε ∧
      stepExponentials M d k * C * r ≤ adaptiveQueryCostBound C M d k Υbar K Δt ε ∧
      NT ≤ adaptiveQueryCostBound C M d k Υbar K Δt ε / (3 * C * d ^ 2) := by
  have hcost := queryCount C M d k Υbar K Δt ε r hε hΥbar hΔt hr
  refine ⟨errorSum Uexact Umid Usim hRound hLemma7, hcost, ?_⟩
  rw [Nat.le_div_iff_mul_le (by positivity)]
  exact le_trans hNT hcost

end Qatlib.Papers.QDynamics10.MainResults.StepAlgebra
