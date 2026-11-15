/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionDefs
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess
public import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeCore.InvFreePhase Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TauEmbedding
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Matrix Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable def devPlusIReflectionWord {I : Type} [DecidableEq I] (j : I) :
    List (DetectionStep I) :=
  [.rowForward, .marker, .rowBackward]

noncomputable def devPlusIWalkWord {I : Type} [DecidableEq I] (j : I) :
    List (DetectionStep I) :=
  [.fixed detectionControlledSwap] ++ devPlusIReflectionWord j ++
    [.fixed detectionControlledSwap] ++ devPlusIReflectionWord j

noncomputable def devPlusIProgram {I : Type} [Fintype I] [DecidableEq I]
    (j : I) (K : ℕ) : List (DetectionStep I) :=
  [.marker, .fixed detectionHadamard] ++ (List.replicate K (devPlusIWalkWord j)).flatten ++
    [.fixed detectionHadamard, .rowInitial]

noncomputable def devPlusIDetectionProbability {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) (j : I) (K : ℕ) : ℝ :=
  MeasureProb (detectionEvaluate U S (devPlusIProgram j K) *ᵥ detectionStart j) detectionAccept

def CorePlusICounterexample : Prop :=
  ∃ (I : Type) (hi : Fintype I) (hd : DecidableEq I) (hn : Nonempty I)
      (P : I → I → ℝ) (S : Finset I) (δ : ℝ) (j : I)
      (U : Matrix (I × I) (I × I) ℂ) (K : ℕ),
    IsTransitionMatrix P ∧ (∀ i y, P i y = P y i) ∧ 0 < δ ∧ δ ≤ 1 ∧
      SymmetricChainGap P δ ∧ S.Nonempty ∧ markedFraction S ≤ 1 / 32 ∧
      U ∈ Matrix.unitaryGroup (I × I) ℂ ∧
      (∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) ∧
      devPlusIDetectionProbability U S j K < 1 / 32

def clause37Spec : Prop :=
  (∀ (V : ℕ) (K : Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralKernel V)
      (p : Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralVertex V) (k : ℕ),
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess.GeneralGraphSetupAccount V K p k) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (P : I → I → ℝ),
    IsTransitionMatrix P →
      Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.CoreReachableSpectrum P) ∧
  (∀ (a : ℕ) (ha : 0 < a),
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.EffectiveNeighborProgram
      (2 ^ a) (2 ^ (a - 1))
      (Nat.pow_le_pow_of_le (by decide) (by omega))
      (Qatlib.Concepts.QuantumGibbs.FormAlgebra.bipartiteAdj a)
      (Qatlib.Concepts.QuantumGibbs.FormAlgebra.bipartiteMarked a)
      (Qatlib.Concepts.QuantumGibbs.FormAlgebra.bipartiteNeighbor ha)) ∧
  (∀ (a : ℕ) (ha : 0 < a),
    ∃ L : Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.WalkLedger,
      L.setupGates =
          (Qatlib.Concepts.QuantumGibbs.FormAlgebra.coherentRowWord a).length ∧
        L.setupQueries = 0 ∧
        L.updateGates = 4 ∧ L.updateQueries = 4 ∧
        L.checkGates =
          ((Qatlib.Concepts.QuantumGibbs.FormAlgebra.bipartiteCheckBlocks a ha).flatMap
            Qatlib.Concepts.QuantumGibbs.FormAlgebra.blockWord).length ∧
        L.checkQueries = 0 ∧
        L.spaceBits = a + a ∧
        L.bitTime = (a + 1) * (a + a + 1) + 4 * (a + a + 1) + 1 * (a + a + 1))

def clause38Spec : Prop :=
  Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.CoreRelationCarrier ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (W : Matrix (I × I) (I × I) ℂ)
      (ψ : QState (I × I)) (S : Finset I) (Mq k t : ℕ),
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.CoreFindEndpoint W ψ S Mq k t) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (W : Matrix (I × I) (I × I) ℂ)
      (ψ : QState (I × I)) (Mq k t : ℕ),
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.devFindSuccessMass W ψ ∅ Mq k t = 0)

def clause39Spec : Prop :=
  (∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry A → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B →
      ∀ u : QState (I ⊕ J),
        Qatlib.Concepts.SpectralFilter.BusySpectrum.bipartiteDiscriminant A B *ᵥ u = ((1 : ℝ) : ℂ) • u →
          ∀ s : Bool, Qatlib.Concepts.WalkSearch.TauEmbedding.bipartiteTauLinear A B 1 s u = 0) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (j : I) (K : ℕ),
    (devPlusIProgram j K).length ≤ (detectionProgram j K).length)

def clause37Residual : List String :=
  [ "the numerical setup word of `GeneralWalkAccessNext` and the bit-level row \
oracle of the neighbour programme are not identified on one and the same kernel",
    "the exact gate-synthesis boundary (the frozen `noCountableExactGateCover`) is \
stated in the frozen `Papers` layer and is not rebuilt on the `Foundations` layer here",
    "the paid macro schedule of the walk search (the `2 k t (M-1)` access ledger) is \
not built here",
    "the detection guarantee of the general graph is not proved here" ]

def clause38Residual : List String :=
  [ "the positive real find (an actual run whose marked-output mass is at least `1/24`) \
is not constructed here",
    "the Johnson relation detection reduction with the paper's cost form is not proved",
    "the element-distinctness walk reduction with the `O(n^{2/3})` query ledger is not \
proved here",
    "the triangle walk reduction with the `O(n^{13/10})` cost ledger is not proved here" ]

def clause39Residual : List String :=
  [ "the printed `+I` per-`K` counterexample is not proved here: the printed variant is \
built as a program, but the numeric instance at which its detection probability drops \
below `1/32` is not constructed",
    "the Theorem-5 intersection branch (the `|a| = 1` norm law of the common image) is \
not rebuilt on the `Foundations` layer; only the `λ = 1` τ-vanishing branch is",
    "the printed `+I` marker on the uncontrolled branch is not analysed" ]

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
