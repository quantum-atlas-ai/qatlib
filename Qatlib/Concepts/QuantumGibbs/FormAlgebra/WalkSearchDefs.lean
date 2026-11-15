/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphCheegerConstruction
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphNeighborProgramConstruction
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
public import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
public import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence
public import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
public import Qatlib.Concepts.WalkFind.UniformThree.PhaseReflectionSearch
public import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
public import Qatlib.Concepts.WalkSearch.ProjectorCS
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeCore.InvFreePhase Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.ProjectorCS

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators

set_option autoImplicit false

def complexLift {I : Type} (u : I → ℝ) : QState I := fun x => (u x : ℂ)

noncomputable def devRowState {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (v : QState I) : QState (I × I) :=
  SzegedyIsometry P *ᵥ v

noncomputable def devSwapRowState {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (v : QState I) : QState (I × I) :=
  SzegedyIsometryB P *ᵥ v

noncomputable def devReachableSpan {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) : Submodule ℂ (QState (I × I)) :=
  Submodule.span ℂ (Set.range (devRowState P) ∪ Set.range (devSwapRowState P))

def CoreReachableSpectrum {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) : Prop :=
  (∀ ψ ∈ devReachableSpan P, SzegedyWalk P *ᵥ ψ ∈ devReachableSpan P) ∧
    (∀ ψ ∈ devReachableSpan P, SwapGate *ᵥ ψ ∈ devReachableSpan P) ∧
    (∀ (u : I → ℝ) (lam : ℝ),
      SzegedyDiscriminant P *ᵥ u = lam • u →
        SzegedyWalk P *ᵥ (SzegedyIsometry P *ᵥ complexLift u) =
            ((2 * lam : ℝ) : ℂ) • (SzegedyIsometryB P *ᵥ complexLift u) -
              SzegedyIsometry P *ᵥ complexLift u ∧
        SzegedyWalk P *ᵥ (SzegedyIsometryB P *ᵥ complexLift u) =
            ((-(2 * lam) : ℝ) : ℂ) • (SzegedyIsometry P *ᵥ complexLift u) +
              ((4 * lam ^ 2 - 1 : ℝ) : ℂ) • (SzegedyIsometryB P *ᵥ complexLift u))

structure WalkLedger where

  setupGates : ℕ

  setupQueries : ℕ

  updateGates : ℕ

  updateQueries : ℕ

  checkGates : ℕ

  checkQueries : ℕ

  bitTime : ℕ

  spaceBits : ℕ

def WalkLedger.totalGates (L : WalkLedger) : ℕ :=
  L.setupGates + L.updateGates + L.checkGates

def WalkLedger.totalQueries (L : WalkLedger) : ℕ :=
  L.setupQueries + L.updateQueries + L.checkQueries

def devEdgeMarkedSet {I : Type} [Fintype I] [DecidableEq I] (M : Finset I) :
    Finset (I × I) :=
  Finset.univ.filter (fun p => p.1 ∈ M)

noncomputable def devFindElementMass {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix (I × I) (I × I) ℂ) (ψ : QState (I × I)) (S : Finset I)
    (Mq k t : ℕ) (x : I) : ℝ :=
  MeasureProb (phaseSearchState W ψ (devEdgeMarkedSet S) Mq k t)
    (Finset.univ.filter fun q => q.2.2.1 = x)

noncomputable def devFindSuccessMass {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix (I × I) (I × I) ℂ) (ψ : QState (I × I)) (S : Finset I)
    (Mq k t : ℕ) : ℝ :=
  MeasureProb (phaseSearchState W ψ (devEdgeMarkedSet S) Mq k t)
    (Finset.univ.filter fun q => q.2.2 ∈ devEdgeMarkedSet S)

def CoreFindEndpoint {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix (I × I) (I × I) ℂ) (ψ : QState (I × I)) (S : Finset I)
    (Mq k t : ℕ) : Prop :=
  devFindSuccessMass W ψ S Mq k t
      = ∑ x ∈ S, devFindElementMass W ψ S Mq k t x ∧
    (∀ x ∈ S, 0 ≤ devFindElementMass W ψ S Mq k t x) ∧
    (S = ∅ → devFindSuccessMass W ψ S Mq k t = 0)

/-- Every natural number is at most two raised to that number. -/
theorem nat_le_two_pow (L : ℕ) : L ≤ 2 ^ L := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    calc
      n + 1 ≤ 2 ^ n + 1 := by omega
      _ ≤ 2 ^ n * 2 := by omega
      _ = 2 ^ n * 2 := rfl

def fairBitWidth (L : ℕ) : ℕ :=
  Nat.find (p := fun b => L ≤ 2 ^ b) ⟨L, nat_le_two_pow L⟩

def fairBitDraw (L : ℕ) (b : ℕ) (r : Reg b) : Option (Fin L) :=
  if h : (bitVecEquiv b r).val < L then some ⟨(bitVecEquiv b r).val, h⟩ else none

def CoreUniformSource : Prop :=
  ∀ L : ℕ, 0 < L →
    ∃ (b : ℕ) (draw : Reg b → Option (Fin L)),
      L ≤ 2 ^ b ∧
        (∀ K K' : Fin L,
          (∑ r : Reg b, if draw r = some K then (1 : ℝ) else 0) =
            (∑ r : Reg b, if draw r = some K' then (1 : ℝ) else 0)) ∧
        (2 * (∑ K : Fin L, ∑ r : Reg b, if draw r = some K then (1 : ℝ) else 0)
            ≥ (2 ^ b : ℝ))

abbrev JohnsonVertex (X : Type) [Fintype X] [DecidableEq X] (k : ℕ) :=
  {s : Finset X // s.card = k}

noncomputable def johnsonKernel (X : Type) [Fintype X] [DecidableEq X] (k : ℕ) :
    JohnsonVertex X k → JohnsonVertex X k → ℝ :=
  fun s t =>
    if (s.1 ∩ t.1).card = k - 1 then ((k * (Fintype.card X - k) : ℕ) : ℝ)⁻¹ else 0

def devCollisionMarked (n : ℕ) (x : Fin n → ℕ) (r : ℕ) :
    Finset (JohnsonVertex (Fin n) r) :=
  Finset.univ.filter (fun s =>
    ∃ a b : Fin n, a ∈ s.1 ∧ b ∈ s.1 ∧ a ≠ b ∧ x a = x b)

def CoreRelationCarrier : Prop :=
  (∀ (X : Type) [Fintype X] [DecidableEq X] (k : ℕ),
    0 < k → 2 * k ≤ Fintype.card X →
      (∀ s t : JohnsonVertex X k, johnsonKernel X k s t = johnsonKernel X k t s) ∧
      (∀ s t : JohnsonVertex X k, 0 ≤ johnsonKernel X k s t)) ∧
  (∀ (n : ℕ) (x : Fin n → ℕ),
    (∃ a b : Fin n, a ≠ b ∧ x a = x b) →
      ∃ r : ℕ, 0 < r ∧ (devCollisionMarked n x r).Nonempty)

def clause5Spec : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (P : I → I → ℝ),
    IsTransitionMatrix P → CoreReachableSpectrum P) ∧
  (∀ n : ℕ, 2 ≤ n →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      SymmetricChainGap
        (Qatlib.Concepts.QuantumGibbs.FormAlgebra.regularKernel
          (Qatlib.Concepts.QuantumGibbs.FormAlgebra.completeGraph n) ((n : ℝ) - 1)) δ) ∧
  (∀ (a : ℕ) (ha : 0 < a),
    Qatlib.Concepts.QuantumGibbs.FormAlgebra.EffectiveNeighborProgram
      (2 ^ a) (2 ^ (a - 1))
      (Nat.pow_le_pow_of_le (by decide) (Nat.sub_le _ _))
      (Qatlib.Concepts.QuantumGibbs.FormAlgebra.bipartiteAdj a)
      (Qatlib.Concepts.QuantumGibbs.FormAlgebra.bipartiteMarked a)
      (Qatlib.Concepts.QuantumGibbs.FormAlgebra.bipartiteNeighbor ha) ∧
    ∃ L : WalkLedger,
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

def clause6Spec : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] (W : Matrix (I × I) (I × I) ℂ)
      (ψ : QState (I × I)) (S : Finset I) (Mq k t : ℕ),
    CoreFindEndpoint W ψ S Mq k t) ∧
  CoreRelationCarrier

def clause7Spec : Prop :=
  CoreUniformSource ∧
  (∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry A → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B →
      ∀ u : QState (I ⊕ J),
        Qatlib.Concepts.SpectralFilter.BusySpectrum.bipartiteDiscriminant A B *ᵥ u = ((1 : ℝ) : ℂ) • u →
          ∀ s : Bool, Qatlib.Concepts.WalkSearch.TauEmbedding.bipartiteTauLinear A B 1 s u = 0)

def clause5Residual : List String :=
  [ "the graph-local row oracle is built for the complete bipartite family only; the \
arbitrary `GeneralKernel` of `GeneralWalkAccess` is not specialised to a bit-level \
row word here",
    "the setup word of the family is the coherent row word, but the precision-indexed \
numerical setup of `GeneralWalkAccess` and the bit-level row word are not identified \
on one and the same kernel",
    "the concrete `δ`-gap family is the complete graph, whose degree is not bounded \
independently of `n`; the frozen bounded-degree requirement `d < n` is not met",
    "the effective setup/update/check account with the full paid macro schedule of the \
walk search (the `2 k t (M-1)` access ledger) is not built here",
    "the detection guarantee of the general graph is not proved for this family" ]

def clause6Residual : List String :=
  [ "the positive real find (an actual run whose marked-output mass is at least `1/24`) \
is not constructed here; only the per-element decomposition and the one-sidedness at the \
empty marked set are proved",
    "the Johnson relation detection reduction with the paper's cost form is not proved; \
only the carrier (symmetry and non-negativity of the Johnson kernel, and the \
non-emptiness of the collision-marked set) is built",
    "the element-distinctness walk reduction with the `O(n^{2/3})` query ledger is not \
proved here",
    "the triangle walk reduction with the `O(n^{13/10})` cost ledger is not proved here" ]

def clause7Residual : List String :=
  [ "the fair-bit sampler is built for the run length alone; the coupling of the sampled \
length to the marked mass of a general graph is not proved",
    "the optimal rate of the unified source statement is not proved",
    "the printed `+I` per-`K` counterexample is not built here",
    "the idle counterexample chain (an irreducible chain whose walk fixes a nonzero \
ambient vector but no nonzero reachable one) is not built here",
    "the fresh-slice applicability bridge and the non-reversible singular-gap bridge are \
not proved here" ]

end Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearchDefs
