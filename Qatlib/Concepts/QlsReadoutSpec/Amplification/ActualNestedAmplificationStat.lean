/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
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

def Clause5ActualNestedAmplification : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (slots : ℕ)
    (U : ℕ → Matrix H H ℂ) (B : Word H 1) (ω : QState H)
    (G : Matrix H H ℂ) (s : ℕ),
    (∀ j < slots, U j ∈ Matrix.unitaryGroup H ℂ) → legal slots B →
    Normalized ω → IsOrthogonalProjector G →
    let ψ := clockState U B ω
    let a := normVec (G *ᵥ ψ)
    ((2*s+1 : ℕ) : ℝ)*Real.arcsin a ≤ Real.pi/2 →
    legal slots (aaWord B ω G s) ∧
    G *ᵥ clockState U (aaWord B ω G s) ω=
      (((2*s+1 : ℕ) : ℂ)*gainLoss (2*s+1) a) • (G *ᵥ ψ) ∧
    (∀ j, calls (aaWord B ω G s) j=(2*s+1)*calls B j) ∧
    gateCount (aaWord B ω G s)=(2*s+1)*gateCount B+3*s ∧
    (∀ prices, weightedCost prices (aaWord B ω G s)=(2*s+1)*weightedCost prices B)

end Qatlib.Concepts.QlsReadoutSpec.Amplification
