/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess
public import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
public import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess
public import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
public import Qatlib.Concepts.WalkSearch.ProjectorCS
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Matrix Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

def devMarkedPairs {I : Type} [Fintype I] [DecidableEq I] (S : Finset I) :
    Finset (I × I) :=
  Finset.univ.filter (fun xy => xy.1 ∈ S)

/-- The marked reflection on pairs whose first coordinate lies in `S` is unitary. -/
theorem devMarkedReflection_unitary {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) :
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs.generalMarkedReflection
        (devMarkedPairs S) ∈ Matrix.unitaryGroup (I × I) ℂ :=
  Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution.generalMarkedReflection_unitary _

structure SourceDetectionAccount {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (j : I) (K : ℕ) : Prop where

  counts : detectionCounts (detectionProgram j K) = (4 * K + 1, 4 * K + 1, 4 * K + 2)

  markedMass : MeasureProb (detectionInitial P) {xy | xy.1 ∈ S} = markedFraction S

  markerUnitary :
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs.generalMarkedReflection
        ({xy : I × I | xy.1 ∈ S} : Finset (I × I)) ∈ Matrix.unitaryGroup (I × I) ℂ

def CoreDetectionGuarantee {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (L : ℕ) (j : I)
    (U : Matrix (I × I) (I × I) ℂ) : Prop :=
  0 < δ → δ ≤ 1 → SymmetricChainGap P δ →
    0 < ε → ε ≤ markedFraction S →
      0 < L → 1000 / Real.sqrt (δ * ε) ≤ (L : ℝ) →
        U ∈ Matrix.unitaryGroup (I × I) ℂ →
          (∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) →
            (1 / 32 : ℝ) ≤ (∑ k : Fin L, detectionProbability U S j (k.val + 1)) / (L : ℝ)

def clause5Spec : Prop :=
  (∀ (V : ℕ) (K : Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralKernel V)
      (p : Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralVertex V)
      (S : Finset (Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralVertex V)) (k : ℕ),
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution.GeneralSourceDetectionAccount V K p S k) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (P : I → I → ℝ),
    IsTransitionMatrix P →
      Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.CoreReachableSpectrum P) ∧
  (∀ n : ℕ, 2 ≤ n →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      SymmetricChainGap
        (Qatlib.Concepts.QuantumGibbs.FormAlgebra.regularKernel
          (Qatlib.Concepts.QuantumGibbs.FormAlgebra.completeGraph n) ((n : ℝ) - 1)) δ) ∧
  (∀ (a : ℕ) (ha : 0 < a),
    ∃ L : Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.WalkLedger,
      L.setupGates =
          (Qatlib.Concepts.QuantumGibbs.FormAlgebra.coherentRowWord a).length ∧
        L.updateGates = 4 ∧ L.updateQueries = 4 ∧
        L.spaceBits = a + a)

def clause6Spec : Prop :=
  (∀ (V : ℕ) (K : Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralKernel V)
      (p : Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralVertex V)
      (S : Finset (Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralVertex V)) (k : ℕ),
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs.generalMarkedMass S
        (Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution.generalDetectionExecution K p S)
        = ∑ u ∈ S, (K.weight p u : ℝ) ∧
      Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs.generalMarkedMass S
        (Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs.generalMarkedReflection S
          *ᵥ (Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.generalRowState K p)) =
        Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs.generalMarkedMass S
          (Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.generalRowState K p)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (W : Matrix (I × I) (I × I) ℂ)
      (ψ : QState (I × I)) (S : Finset I) (Mq k t : ℕ),
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.CoreFindEndpoint W ψ S Mq k t) ∧
  Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.CoreRelationCarrier

def clause7Spec : Prop :=
  (∀ (V : ℕ) (K : Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralKernel V)
      (p : Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralVertex V)
      (S : Finset (Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.GeneralVertex V)) (k : ℕ),
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution.generalDetectionExecution K p S
        = Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs.generalMarkedReflection S
          *ᵥ (Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs.generalRowState K p)) ∧
  Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs.CoreUniformSource ∧
  (∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry A → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B →
      ∀ u : QState (I ⊕ J),
        Qatlib.Concepts.SpectralFilter.BusySpectrum.bipartiteDiscriminant A B *ᵥ u = ((1 : ℝ) : ℂ) • u →
          ∀ s : Bool, Qatlib.Concepts.WalkSearch.TauEmbedding.bipartiteTauLinear A B 1 s u = 0)

def clause5Residual : List String :=
  [ "the detection guarantee of the general graph is not proved here; the \
account only fixes the paid counts of the actual detection word and the marked \
mass of the detection state",
    "the anchored unitary of the frozen setup account is not constructed on the \
`Foundations` layer; the general-graph setup of `GeneralWalkAccess` supplies the \
numerical setup word, not the bit-level row oracle of the same kernel",
    "the exact gate-synthesis boundary (the frozen `noCountableExactGateCover`) is \
stated in the frozen `Papers` layer and is not rebuilt on the `Foundations` layer here" ]

def clause6Residual : List String :=
  [ "the positive real find (an actual run whose marked-output mass is at least `1/24`) \
is not constructed here; only the per-element decomposition and the one-sidedness at the \
empty marked set are proved",
    "the Johnson relation detection reduction with the paper's cost form is not proved; \
only the carrier (symmetry and non-negativity of the Johnson kernel, and the \
non-emptiness of the collision-marked set) is built",
    "the element-distinctness and triangle walk reductions with their cost ledgers are \
not proved here" ]

def clause7Residual : List String :=
  [ "the detection guarantee is stated as the frozen contract but not proved here: the \
length-averaged law needs the spectral analysis of the corrected detector on a general \
chain",
    "the optimal rate of the unified source statement is not proved",
    "the printed `+I` per-`K` counterexample is not built here",
    "the idle counterexample chain is not built here",
    "the fresh-slice applicability bridge and the non-reversible singular-gap bridge are \
not proved here" ]

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
