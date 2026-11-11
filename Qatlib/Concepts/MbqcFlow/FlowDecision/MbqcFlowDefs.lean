/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.IsingClusterResource
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetwork
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkBranch
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkInstrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkRouting
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkTransport

/-!
# Claims for preentangled compilation and measurement gates

`Clause21Claim` packages branch and channel equivalence for preentangled compilation, resource
counts, and zero-probability branch behavior. `Clause22Claim` packages the explicit wire, CNOT,
and Figure 2b formulas, finite-gate execution, communication counts, and source-pulse
factorization.

These propositions organize concrete measurement-based constructions in the setting of
[RaussendorfBriegel2000] and [RaussendorfBriegel2001], including the explicitly stated Figure 2b
normalization boundary.

## Main statements

* `Clause21Claim`: the preentangled compilation specification.
* `Clause22Claim`: the gate-construction and resource specification.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
* [Raussendorf and Briegel, 2001][RaussendorfBriegel2001]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Qatlib
open Qatlib
open Qatlib
open Matrix
open scoped ComplexOrder

/-- The conjunction of branch and channel equivalence for preentangled compilation, the
Bell-word resource counts, and vanishing of zero-probability branches. -/
def Clause21Claim : Prop :=
  (∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs)
      (hist : Fin gs.length → Bool × Bool) (ρ : Operator (2 ^ n)),
      (mbqcPreentangledInstrument gs hg).branch hist ρ
        = (networkHistoryInstrument gs hg).branch hist ρ) ∧
  (∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs),
      (mbqcPreentangledInstrument gs hg).forget.map
        = (networkHistoryInstrument gs hg).forget.map) ∧
  (networkLegal mbqcBellWord ∧
    mbqcBellWord.length = 3 ∧
    networkCounts mbqcBellWord = (2, 1) ∧
    mbqcPreentangleCount mbqcBellWord = 1 ∧
    mbqcMeasureCount mbqcBellWord = 3 ∧
    mbqcFeedbackBits mbqcBellWord = 2 ∧
    mbqcCommBits mbqcBellWord = 2 ∧
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)),
      mbqcPreentangleCount gs = (networkCounts gs).2) ∧
  (∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hg : networkLegal gs)
      (ρ : Operator (2 ^ n)) (hist : Fin gs.length → Bool × Bool),
      ρ.PosSemidef →
        instrumentProb (networkHistoryInstrument gs hg) ρ hist = 0 →
          (mbqcPreentangledInstrument gs hg).branch hist ρ = 0)

/-- The conjunction of the wire and CNOT branch formulas, the Figure 2b normalization formula
and its counterexample, finite-gate execution, communication counts, and source-pulse
factorization. -/
def Clause22Claim : Prop :=
  (∀ (a : ℝ) (ρ : Operator 2) (b b' : Bool),
    rbWireBranch a b ρ = rbWireBranch a b' ρ ∧
    rbWireBranch a b ρ = ((2 : ℂ)⁻¹) • (rbWireUnitary a * ρ * (rbWireUnitary a).conjTranspose)) ∧
  (∃ κ : (Bool × Bool) → Fin 2 → Operator 2,
    (∀ s : Bool × Bool, ∀ v : Fin 2, MbqcPauliWire (κ s v)) ∧
    ∀ (ρ : Operator 4) (s : Bool × Bool),
      rbCnotBranch s ρ =
        ((2 : ℂ)⁻¹) ^ 2 •
          ((relabelGate (bitVecEquiv 2) (pauliProductDensity (κ s)) * rbCnotOp) * ρ *
            (relabelGate (bitVecEquiv 2) (pauliProductDensity (κ s)) * rbCnotOp).conjTranspose)) ∧
  (∀ (ρ : Operator 2),
    rbFig2bBranch false ρ = (2 : ℂ) • (rbFig2bTransferOp * ρ * (rbFig2bTransferOp).conjTranspose)) ∧
  (¬ (∀ (ρ : Operator 2) (s : Bool),
    rbFig2bBranch s ρ = rbFig2bTransferOp * ρ * (rbFig2bTransferOp).conjTranspose)) ∧
  (∀ ψ : QState (Reg 2),
    finiteWordRun 2 rbFiniteGateDecomp ψ = some (ApplyGate rbWirePulse ψ)) ∧
  (rbWireCommBits = 1 ∧ rbCnotCommBits = 2 ∧ rbFig2bCommBits = 1 ∧
    ∀ (n : ℕ) (edges : Finset (Fin n × Fin n)),
      Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse edges =
        Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix edges *
          Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix edges)

end Qatlib.Concepts.MbqcFlow.FlowDecision
