/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels
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
