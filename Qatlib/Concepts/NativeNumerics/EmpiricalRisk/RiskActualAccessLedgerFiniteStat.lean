/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs

/-!
# Specification of the finite risk access ledger

This module defines `RiskActualAccessLedgerFiniteSubgoal`, combining a probability-zero bound
for excessive CVaR calls with exact preparation-access, oracle-query, and gate counts. The
specification separates the risk algorithm of [WoernerEgger2019] from the resource counts for
its amplitude-estimation primitive [BrassardEtAl2002].

## Main statements

* `RiskActualAccessLedgerFiniteSubgoal`: for nonempty threshold lists, the CVaR call count stays
  within `Nat.clog 2 xs.length + 3` almost surely; the associated amplitude-estimation word has
  `M` forward accesses, `M - 1` backward accesses and queries, and `5 * (M - 1) + 3` gates.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

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

/-- The proposition combining the zero probability of exceeding the CVaR call budget for
nonempty threshold lists with exact counts of `M` forward accesses, `M - 1` backward
accesses and queries, and `5 * (M - 1) + 3` gates. -/
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
