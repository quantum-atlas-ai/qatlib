/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

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

def Clause6AmplifiedSuffixRays : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (V : ℕ → Matrix H H ℂ) (ω : QState H),
    clockLegal m P bad → stageLegal m P U → Normalized ω → V 0=1 →
    (∀ j ≤ m, V j ∈ Matrix.unitaryGroup H ℂ) →
    (∀ j : Fin m,
      let G := potential (P ⟨j.val+1,by omega⟩) bad
      let a := G *ᵥ (V (j.val+1) *ᵥ ω)
      let b := G *ᵥ (U (j.val+1) *ᵥ (V j.val *ᵥ ω))
      0 < normVec a ∧ 0 < normVec b ∧ normState a=normState b) →
    ∀ (j l k h : Fin (m+1)), j.val ≤ k.val → l.val ≤ k.val →
      j.val ≤ h.val → l.val ≤ h.val →
      let sj := potential (P k) bad *ᵥ suffixState U j.val k.val (V j.val *ᵥ ω)
      let sl := potential (P k) bad *ᵥ suffixState U l.val k.val (V l.val *ᵥ ω)
      let tj := potential (P h) bad *ᵥ suffixState U j.val h.val (V j.val *ᵥ ω)
      let tl := potential (P h) bad *ᵥ suffixState U l.val h.val (V l.val *ᵥ ω)
      0 < normVec sj → 0 < normVec sl →
      normState sj=normState sl ∧ normVec tj/normVec sj=normVec tl/normVec sl

end Qatlib.Concepts.QlsReadoutSpec.Amplification
