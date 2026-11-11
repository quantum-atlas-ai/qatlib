/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels

/-!
# Optimal threshold allocation contract

Defines `ThresholdOptimalThresholdAllocation` for nonnegative weights with positive total
weight. The thresholds proportional to the two-thirds powers sum to one, lie in the unit
interval, and attain `quasinorm23`; the contract also requires global optimality among supported
allocations and uniqueness for positive weights. This captures the threshold optimization used
in [LowSu2026].

## Main statements

* `ThresholdOptimalThresholdAllocation`: states feasibility, objective value, optimality, and
  the positive-weight uniqueness criterion.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The contract that thresholds proportional to the two-thirds powers of nonnegative weights
form a unit-sum allocation attaining `quasinorm23`, minimize the objective over nonnegative
unit-sum allocations positive wherever the weights are positive, and are the unique strictly
positive minimizer when all weights are positive. -/
def ThresholdOptimalThresholdAllocation : Prop :=
  ∀ (n : ℕ) (w : Fin n → ℝ),
    (∀ j, 0 ≤ w j) → 0 < (∑ j, w j) →
    let α := fun j =>  (w j).rpow (2/3)/(∑ k, (w k).rpow (2/3))
    (∑ j, α j)=1 ∧ (∀ j, 0 ≤ α j ∧ α j ≤ 1) ∧
    (∑ j, w j/Real.sqrt (α j))=quasinorm23 w ∧
    (∀ β : Fin n → ℝ, (∀ j, 0 ≤ β j) → (∀ j, 0 < w j → 0 < β j) →
      (∑ j, β j)=1 → quasinorm23 w ≤ ∑ j, w j/Real.sqrt (β j)) ∧
    (∀ β : Fin n → ℝ, (∀ j, 0 < β j) → (∀ j, 0 < w j) →
      (∑ j, β j)=1 → ((∑ j, w j/Real.sqrt (β j))=quasinorm23 w ↔ β=α))

end Qatlib.Concepts.QlsReadoutSpec.Amplification
