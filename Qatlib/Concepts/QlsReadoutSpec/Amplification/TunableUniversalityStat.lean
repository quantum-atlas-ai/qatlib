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

def Clause8TunableUniversality : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ),
    clockLegal m P bad → stageLegal m P U → Normalized ω →
    0 < plainAmplitude (extendClock m P) bad U ω m →
    let E := extendClock m P
    ((tunable m E bad U ω α rs ∧ ∀ j : Fin m, α (j.val+1) ≤ 1) →
      (∀ j : Fin m, 0 < preAmplitude E bad ω U rs j.val ∧
        (2*rs (j.val+1)+1)*preAmplitude E bad ω U rs j.val ≤ 1 ∧
        rs (j.val+1)=Nat.ceil
          (Real.sqrt (α (j.val+1))/(6*preAmplitude E bad ω U rs j.val)-1/2)) ∧
      (5/6 : ℝ).rpow (∑ j : Fin m, α (j.val+1)) ≤ totalLoss m E bad U ω rs) ∧
    ((∀ j : Fin m, 0 < preAmplitude E bad ω U rs j.val ∧
      preAmplitude E bad ω U rs j.val ≤ 1/(3*(2*rs (j.val+1)+1))) →
      tunable m E bad U ω (reverseThreshold E bad U ω rs) rs ∧
      (∀ j : Fin m, reverseThreshold E bad U ω rs (j.val+1) ≤ 1) ∧
      (4*Real.pi-8)/(9*Real.pi^3)*(∑ j : Fin m, reverseThreshold E bad U ω rs (j.val+1)) ≤ -Real.log (totalLoss m E bad U ω rs))

end Qatlib.Concepts.QlsReadoutSpec.Amplification
