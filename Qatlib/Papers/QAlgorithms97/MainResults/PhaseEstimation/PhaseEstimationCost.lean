/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsRefinedDefs
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.QuantumGibbs
import Qatlib.Concepts.FourierRecovery.ModularFourier.FourierGradient
import Mathlib.Data.Nat.Basic

/-!
# Phase-estimation resource counts

This module specializes the phase-estimation cost ledger to a grid with `m` levels. It separates
`m` controlled-power entries and `m` inverse-QFT ledger entries from the quadratic bound on
elementary QFT gates, matching the resource accounting discussed in [CleveEtAl1998].

## Main statements

* `phase_estimation_cost`: the combined controlled-power, inverse-QFT, and elementary-gate
  bounds.

## References

* [Cleve et al., 1998][CleveEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MbqcFlow.FlowDecision.StageAQUANTUMGIBBS
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.StageAQUANTUMGIBBS
open Qatlib.Concepts.FourierRecovery.ModularFourier

namespace Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation

/-- For a phase grid with `m` levels, the phase-estimation ledger records `m` controlled powers. -/
theorem qpe_controlled_power_count {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (m : ℕ) (hlevels : G.levels = m) :
    (qpeCostLedger O G).controlledPowers = m := by
  rw [(qpeCostLedger_counts O G).2.1, hlevels]

/-- For a phase grid with `m` levels, the phase-estimation ledger records `m` inverse-QFT gate
entries. -/
theorem qpe_inverse_qft_layer_count {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (m : ℕ) (hlevels : G.levels = m) :
    (qpeCostLedger O G).inverseQftGates = m := by
  rw [(qpeCostLedger_counts O G).2.2.1, hlevels]

/-- The elementary QFT gate count is at most `3 * (m + 1) ^ 2`. -/
theorem qft_elementary_gates_quadratic (m : ℕ) :
    qftElementaryGates m ≤ 3 * (m + 1) ^ 2 := by
  unfold qftElementaryGates
  have hA : m * (m - 1) / 2 ≤ m * m :=
    (Nat.div_le_self (m * (m - 1)) 2).trans (Nat.mul_le_mul_left m (Nat.sub_le m 1))
  have hB : m / 2 ≤ m := Nat.div_le_self m 2
  have h1 : m ≤ (m + 1) * (m + 1) := by
    have h := Nat.le_mul_self (m + 1)
    omega
  have h2 : m * m ≤ (m + 1) * (m + 1) :=
    Nat.mul_le_mul (Nat.le_succ m) (Nat.le_succ m)
  rw [pow_two]
  set M := (m + 1) * (m + 1) with hM
  omega

/-- For a phase grid with `m` levels, the ledger has `m` controlled powers and `m` inverse-QFT
gate entries, and the elementary QFT gate count is at most `3 * (m + 1) ^ 2` [Cleve et al.,
Section 5][CleveEtAl1998]. -/
theorem phase_estimation_cost {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (m : ℕ) (hlevels : G.levels = m) :
    (qpeCostLedger O G).controlledPowers = m ∧
    (qpeCostLedger O G).inverseQftGates = m ∧
    qftElementaryGates m ≤ 3 * (m + 1) ^ 2 :=
  ⟨qpe_controlled_power_count O G m hlevels,
    qpe_inverse_qft_layer_count O G m hlevels,
    qft_elementary_gates_quadratic m⟩

end Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
