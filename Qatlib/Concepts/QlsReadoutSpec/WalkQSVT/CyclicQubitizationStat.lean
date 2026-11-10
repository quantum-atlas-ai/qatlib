/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.SpectralModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

def Clause11CyclicQubitization : Prop :=
  ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (U : Matrix H H ℂ) (G : Matrix H I ℂ),
    U ∈ Matrix.unitaryGroup H ℂ → IsIsometry G →
    (Gᴴ*U*G).IsHermitian →
    (Gᴴ*(U^2)*G=1 ↔ U^2*G=G) ∧
    (Gᴴ*(U^2)*G=1 → ∀ (φ : QState I) (lam : ℝ), Normalized φ →
      (Gᴴ*U*G) *ᵥ φ=(lam : ℂ) • φ →
      let v := G *ᵥ φ
      let w := U *ᵥ v
      (-1 ≤ lam ∧ lam ≤ 1 ∧
      cyclic U v=Submodule.span ℂ {v,w} ∧
      (Module.finrank ℂ (cyclic U v)=1 ↔ abs lam=1) ∧
      (Module.finrank ℂ (cyclic U v)=2 ↔ abs lam < 1) ∧
      U *ᵥ w=v ∧ (G*Gᴴ) *ᵥ v=v ∧ (G*Gᴴ) *ᵥ w=(lam : ℂ) • v ∧
      (abs lam=1 → w=(lam : ℂ) • v) ∧
      (∀ (ψ : QState H), ψ ∈ cyclic U v →
        (U *ᵥ ψ ∈ cyclic U v) ∧ (Uᴴ *ᵥ ψ ∈ cyclic U v) ∧
          ((G*Gᴴ) *ᵥ ψ ∈ cyclic U v))))

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
