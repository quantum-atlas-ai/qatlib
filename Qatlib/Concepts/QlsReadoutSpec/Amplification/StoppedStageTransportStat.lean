/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
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

def Clause4StoppedStageTransport : Prop :=
  (∀ (H : Type) [Fintype H] [DecidableEq H] (P U : Matrix H H ℂ),
    IsOrthogonalProjector P → U ∈ Matrix.unitaryGroup H ℂ →
    (U*P=P ↔ P*U=P) ∧ (U*P=P ↔ P*U*P=P) ∧
    (U*P=P ↔ U=P+(1-P)*U*(1-P))) ∧
  ∀ (H : Type) [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ), clockLegal m P bad → stageLegal m P U →
    (∀ (j k : Fin (m+1)), j.val < k.val →
      U k.val*P j=P j ∧ P j*U k.val=P j ∧
      U k.val*potential (P j) bad=potential (P j) bad*U k.val) ∧
    (∀ (j k : Fin (m+1)) (ψ : QState H), j.val ≤ k.val →
      normVec (potential (P j) bad *ᵥ suffixState U j.val k.val ψ)=
        normVec (potential (P j) bad *ᵥ ψ)) ∧
    (∀ (j k : Fin (m+1)) (ω : QState H), j.val ≤ k.val →
      plainAmplitude (extendClock m P) bad U ω k.val ≤ plainAmplitude (extendClock m P) bad U ω j.val)

end Qatlib.Concepts.QlsReadoutSpec.Amplification
