/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Program

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Execution-derived charges and rejection of independent zero ledgers.
Every bound below concerns the same finite interpreter and its explicit
primitive-price model. No claim about host bit operations is inferred from
the unit arithmetic/access model.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.LocalMachine.LocalTransport

/-- Sequencing pays both actual event sequences under the same price model. -/
theorem charge_bind {α β : Type} (model : PriceModel) (actual : Run α)
    (next : α → Run β) :
    charge model (actual >>= next).events =
      charge model actual.events + charge model (next actual.value).events := by
  rw [events_bind, charge_append]

/-- One emitted primitive pays the price of its actual operands. -/
theorem charge_emit {α : Type} (model : PriceModel) (event : Event) (value : α) :
    charge model (emit event value).events = model.price event := by
  simp [charge]

/-- Returning already computed data emits no additional primitive operation. -/
theorem charge_pure {α : Type} (model : PriceModel) (value : α) :
    charge model (pure value : Run α).events = 0 := by
  simp [charge]

/-- The actual original table counter is paid by the traced table construction. -/
theorem table_counter_paid (model : PriceModel) (z : GaussianRat) (n : ℕ) :
    (table z n).value.2 ≤ charge model (table z n).events := by
  have hcounter : (table z n).value.2 = n-1 := by
    rw [table_value]
    exact (phaseTable_spec z n).2.1
  have hcost := table_charge_lower model z n
  rw [hcounter]
  omega

/-- Even early success pays its actual represented-input work. -/
theorem actualCost_pos (model : PriceModel) (p : List ℚ) (degree : ℕ) (eps : ℚ) :
    0 < actualCost model p degree eps := by
  have hp := model.positive (.inputNat degree)
  simp only [actualCost, produce, charge_bind, inputCoefficients_value, value_emit,
    charge_emit]
  omega

/-- Replacing an independent budget field by zero cannot certify this same execution. -/
theorem no_zero_certified_budget (model : PriceModel) (p : List ℚ) (degree : ℕ)
    (eps : ℚ) (actual : Run SynthesisResult) :
    ¬ CertifiedBudget model p degree eps actual 0 := by
  intro h
  have hcost := (certifiedBudget_sound model p degree eps actual 0 h).2
  have hpositive := actualCost_pos model p degree eps
  omega

/-- The complete run pays its actual table even if subsequent search stops early. -/
theorem actual_table_counter_paid (model : PriceModel) (p : List ℚ)
    (degree : ℕ) (eps : ℚ) :
    (finitePhaseSynthesis p degree eps).tableMultiplications ≤
      actualCost model p degree eps := by
  let k := phaseToleranceBits eps
  let r := phaseGridBits degree k
  let q := phaseBackendBits degree k
  let n := 2^r
  let z := numericalDyadicPhase r false q
  by_cases hs : (scoreData p degree ⟨gone,List.replicate degree gone⟩).1.1 ≤
      ((2 : ℚ)^phaseToleranceBits eps)⁻¹
  · have hcounter : (finitePhaseSynthesis p degree eps).tableMultiplications = 0 := by
      simp [finitePhaseSynthesis, hs]
    rw [hcounter]
    exact Nat.zero_le _
  · have hcounter : (finitePhaseSynthesis p degree eps).tableMultiplications =
        (phaseTable z n).2 := by
      simp [finitePhaseSynthesis, hs, k, r, q, n, z]
    have htable : (phaseTable z n).2 ≤ charge model (table z n).events := by
      simpa only [table_value] using table_counter_paid model z n
    rw [hcounter]
    simp only [actualCost, produce, charge_bind, inputCoefficients_value, value_emit,
      toleranceBits_value, power_value, replicateRun_value, score_value, compare_value,
      charge_emit]
    simp only [one_div, inv_pow] at *
    simp only [hs, decide_false, Bool.false_eq_true, ite_false]
    simp only [charge_bind, gridBits_value, backendBits_value, natPower_value,
      dyadicPhase_value, charge_pure]
    dsimp only [k, r, q, n, z] at htable
    dsimp only [k, r, q, n, z]
    omega

/-- A certified budget must cover the same producer's actual table counter. -/
theorem certifiedBudget_pays_table (model : PriceModel) (p : List ℚ) (degree : ℕ)
    (eps : ℚ) (actual : Run SynthesisResult) (budget : ℕ)
    (h : CertifiedBudget model p degree eps actual budget) :
    (finitePhaseSynthesis p degree eps).tableMultiplications ≤ budget :=
  (actual_table_counter_paid model p degree eps).trans
    (certifiedBudget_sound model p degree eps actual budget h).2

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
