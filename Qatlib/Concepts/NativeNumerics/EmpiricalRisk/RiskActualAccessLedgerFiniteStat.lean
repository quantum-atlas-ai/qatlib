/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

namespace Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

def RiskActualAccessLedgerFiniteSubgoal : Prop :=
∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
  (loss : I  → ℚ) (xs : List ℚ) (q eps : ℝ) (k M r : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ)
  (hloss : ∀ i,0 ≤ loss i ∧loss i ≤ 1) (hM : 2 ≤ M),xs ≠ []  →
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskCVaR A j loss xs q eps k M r hA hloss hM)
    (fun z => Nat.clog 2 xs.length+3 < z.2.2)=0 ∧
  aeForwardAccesses (aeAccessWord (I:=I ×Bool) M)=M ∧
  aeBackwardAccesses (aeAccessWord (I:=I ×Bool) M)=M-1 ∧
  QueryCount (countedAECircuit M (payoffPreparation A (riskCDFPayoff loss 0)) (j,false))=M-1 ∧
  GateCount (countedAECircuit M (payoffPreparation A (riskCDFPayoff loss 0)) (j,false))=5*(M-1)+3
end Qatlib.Concepts.NativeNumerics.EmpiricalRisk
