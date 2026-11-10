/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.SpectralModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
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

def Clause12WalkSpectralResolution : Prop :=
  ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (U : Matrix H H ℂ) (G : Matrix H I ℂ) (S : Matrix I I ℂ) (lam : I → ℝ),
    U ∈ Matrix.unitaryGroup H ℂ → IsIsometry G → S ∈ Matrix.unitaryGroup I ℂ →
    Gᴴ*(U^2)*G=1 → Gᴴ*U*G=S*Matrix.diagonal (fun i =>  (lam i : ℂ))*Sᴴ →
    let v := fun i =>  G *ᵥ (fun j =>  S j i)
    let e := fun i =>  residual U (v i) (lam i)
    let T := walkSupport U G S lam
    (∀ i, -1 ≤ lam i ∧ lam i ≤ 1 ∧ Normalized (v i)) ∧
    (∀ i j, i≠j → Qatlib.Foundations.PureStateMath.Inner (v i) (v j)=0 ∧ Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v j)=0 ∧
      Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (v j)=0 ∧ Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (U *ᵥ v j)=0) ∧
    IsOrthogonalProjector T ∧ U*T=T*U ∧ G*Gᴴ*(1-T)=0 ∧
    (∀ ψ : QState H, T *ᵥ ψ=ψ ↔
      ∃ a b : QState I, ψ=G *ᵥ a+U *ᵥ (G *ᵥ b)) ∧
    (∀ ψ : QState H, T *ᵥ ψ=0 ↔ Gᴴ *ᵥ ψ=0 ∧ Gᴴ *ᵥ (Uᴴ *ᵥ ψ)=0) ∧
    (∀ i, abs (lam i) < 1 → Normalized (e i) ∧ Qatlib.Foundations.PureStateMath.Inner (v i) (e i)=0 ∧
      U *ᵥ (v i)=(lam i : ℂ) • v i+(Real.sqrt (1-(lam i)^2) : ℂ) • e i ∧
      U *ᵥ (e i)=(Real.sqrt (1-(lam i)^2) : ℂ) • v i-(lam i : ℂ) • e i ∧
      (G*Gᴴ) *ᵥ e i=0 ∧
      (∀ neg : Bool, Normalized (walkBranch U (v i) (lam i) neg) ∧
        walk G U *ᵥ walkBranch U (v i) (lam i) neg=
          Complex.exp (Complex.I*(if neg then -Real.arccos (lam i) else Real.arccos (lam i))) •
            walkBranch U (v i) (lam i) neg)) ∧
    walk G U*T=
      ∑ i, if abs (lam i)=1 then (lam i : ℂ) • pureDensity (v i) else
        Complex.exp (Complex.I*Real.arccos (lam i)) • pureDensity (walkBranch U (v i) (lam i) false)+
        Complex.exp (-Complex.I*Real.arccos (lam i)) • pureDensity (walkBranch U (v i) (lam i) true)

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
