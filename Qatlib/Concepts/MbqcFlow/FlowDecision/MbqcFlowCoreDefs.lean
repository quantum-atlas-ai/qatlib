/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetwork
import Qatlib.Concepts.MbqcFlow.FlowDecision.IsingClusterResource
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkBranch
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkInstrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkRouting
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkTransport
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Qatlib
open Qatlib
open Matrix
open scoped Classical

set_option autoImplicit false

structure MbqcGraph (n : ℕ) where

  edges : Finset (Fin n × Fin n)

def mbqcCanonical {n : ℕ} (G : MbqcGraph n) : Prop := ∀ e ∈ G.edges, (e.1 : ℕ) < (e.2 : ℕ)

def mbqcAdj {n : ℕ} (G : MbqcGraph n) (i j : Fin n) : Bool :=
  decide ((i, j) ∈ G.edges ∨ (j, i) ∈ G.edges)

def mbqcOdd {n : ℕ} (G : MbqcGraph n) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => (S.filter fun u => mbqcAdj G v u).card % 2 = 1

structure MbqcOpenGraph (n : ℕ) where

  toGraph : MbqcGraph n

  mbqcInputs : Finset (Fin n)

  mbqcOutputs : Finset (Fin n)

inductive MbqcPlane where
  | XY | XZ | YZ
  deriving DecidableEq

def mbqcPlaneAxisA : MbqcPlane → Operator 2
  | .XY => pauliX
  | .XZ => pauliZ
  | .YZ => pauliY

def mbqcPlaneAxisB : MbqcPlane → Operator 2
  | .XY => pauliY
  | .XZ => pauliX
  | .YZ => pauliZ

noncomputable def MbqcPlaneBasis (lam : MbqcPlane) (a : ℝ) (b : Bool) : Operator 2 :=
  (2 : ℂ)⁻¹ • ((1 : Operator 2) +
    (if b then (-1 : ℂ) else 1) •
      ((Complex.ofReal (Real.cos a)) • mbqcPlaneAxisA lam
        + (Complex.ofReal (Real.sin a)) • mbqcPlaneAxisB lam))

theorem mbqcPlaneBasis_add (lam : MbqcPlane) (a : ℝ) :
    MbqcPlaneBasis lam a false + MbqcPlaneBasis lam a true = 1 := by
  unfold MbqcPlaneBasis
  rw [if_neg (by simp : ¬(false = true)), if_pos rfl]
  module

def mbqcRankPrec {n : ℕ} (r : Fin n → Fin n) : Fin n → Fin n → Prop :=
  fun u v => (r u : ℕ) < (r v)

instance mbqcRankPrecDec {n : ℕ} (r : Fin n → Fin n) (u v : Fin n) :
    Decidable (mbqcRankPrec r u v) := Nat.decLt _ _

def mbqcExecPrec {n : ℕ} (r : Fin n → Fin n) (u v : Fin n) : Prop :=
  (r u : ℕ) < (r v : ℕ) ∨ ((r u : ℕ) = (r v : ℕ) ∧ (u : ℕ) < (v : ℕ))

instance mbqcExecPrecDec {n : ℕ} (r : Fin n → Fin n) (u v : Fin n) :
    Decidable (mbqcExecPrec r u v) := by
  unfold mbqcExecPrec
  infer_instance

def mbqcExecLe {n : ℕ} (r : Fin n → Fin n) (x y : Fin n) : Prop :=
  (r x : ℕ) < (r y : ℕ) ∨ ((r x : ℕ) = (r y : ℕ) ∧ (x : ℕ) ≤ (y : ℕ))

instance mbqcExecLeDec {n : ℕ} (r : Fin n → Fin n) (x y : Fin n) :
    Decidable (mbqcExecLe r x y) := by
  unfold mbqcExecLe
  infer_instance

instance mbqcExecLeTrans {n : ℕ} (r : Fin n → Fin n) : IsTrans (Fin n) (mbqcExecLe r) where
  trans := by
    intro a b c hab hbc
    unfold mbqcExecLe at hab hbc ⊢
    rcases hab with h1 | ⟨h1, h2⟩
    · rcases hbc with h3 | ⟨h3, h4⟩
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
    · rcases hbc with h3 | ⟨h3, h4⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, Nat.le_trans h2 h4⟩

instance mbqcExecLeAntisymm {n : ℕ} (r : Fin n → Fin n) : Std.Antisymm (mbqcExecLe r) :=
  ⟨fun a b hab hba => by
    unfold mbqcExecLe at hab hba
    rcases hab with h1 | ⟨h1, h2⟩
    · rcases hba with h3 | ⟨h3, h4⟩
      · omega
      · omega
    · rcases hba with h3 | ⟨h3, h4⟩
      · omega
      · apply Fin.ext; omega⟩

instance mbqcExecLeTotal {n : ℕ} (r : Fin n → Fin n) : Std.Total (mbqcExecLe r) :=
  ⟨fun a b => by unfold mbqcExecLe; omega⟩

noncomputable def mbqcExecOrder {n : ℕ} (O : Finset (Fin n)) (r : Fin n → Fin n) :
    List (Fin n) :=
  (Finset.univ \ O).sort (mbqcExecLe r)

def MbqcHasFlow {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) : Prop :=
  ∃ (f : Fin n → Option (Fin n)) (prec : Fin n → Fin n → Prop),
    ∃ _dp : DecidableRel prec,
      IsStrictOrder (Fin n) prec ∧
      ∀ v : Fin n, v ∉ O → ∃ w : Fin n, f v = some w ∧ mbqcAdj G v w ∧ w ∉ I ∧
        prec v w ∧ ∀ k : Fin n, mbqcAdj G w k → k ≠ v → prec v k

def mbqcGFlowPlaneCond (p : MbqcPlane) (mem odd : Prop) : Prop :=
  match p with
  | .XY => ¬mem ∧ odd
  | .XZ => mem ∧ odd
  | .YZ => mem ∧ ¬odd

def mbqcGFlowPlaneCondB (p : MbqcPlane) (mem odd : Bool) : Bool :=
  match p with
  | .XY => !mem && odd
  | .XZ => mem && odd
  | .YZ => mem && !odd

theorem mbqcGFlowPlaneCondB_iff (p : MbqcPlane) (mem odd : Bool) :
    mbqcGFlowPlaneCondB p mem odd = true ↔
      mbqcGFlowPlaneCond p (mem = true) (odd = true) := by
  cases p <;> simp [mbqcGFlowPlaneCondB, mbqcGFlowPlaneCond]

def MbqcHasGFlow {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) (lam : Fin n → MbqcPlane) :
    Prop :=
  ∃ (g : Fin n → Finset (Fin n)) (prec : Fin n → Fin n → Prop),
    ∃ _dp : DecidableRel prec,
      (∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ∉ I) ∧
      IsStrictOrder (Fin n) prec ∧
      (∀ v : Fin n, v ∉ O → ∀ u : Fin n, u ∈ g v → u ≠ v → prec v u) ∧
      (∀ v : Fin n, v ∉ O → ∀ u : Fin n, prec u v → u ∉ mbqcOdd G (g v)) ∧
      (∀ v : Fin n, v ∉ O →
        mbqcGFlowPlaneCond (lam v) (v ∈ g v) (v ∈ mbqcOdd G (g v)))

def mbqcFlowCheck {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (f : Fin n → Option (Fin n)) (r : Fin n → Fin n) : Prop :=
  ∀ v : Fin n, v ∉ O → ∃ w : Fin n, f v = some w ∧ mbqcAdj G v w ∧ w ∉ I ∧
    mbqcRankPrec r v w ∧
    ∀ k : Fin n, mbqcAdj G w k → k ≠ v → mbqcRankPrec r v k

instance mbqcFlowCheckDec {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (f : Fin n → Option (Fin n)) (r : Fin n → Fin n) :
    Decidable (mbqcFlowCheck G I O f r) := by
  unfold mbqcFlowCheck
  infer_instance

noncomputable def mbqcFlowDecide {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) :
    Option ((Fin n → Option (Fin n)) × (Fin n → Fin n)) :=
  (Fintype.elems (α := (Fin n → Option (Fin n)) × (Fin n → Fin n))).toList.find?
    (fun p => decide (mbqcFlowCheck G I O p.1 p.2))

def mbqcGFlowCheck {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) (lam : Fin n → MbqcPlane)
    (g : Fin n → Finset (Fin n)) (r : Fin n → Fin n) : Prop :=
  ∀ v : Fin n, v ∉ O →
    (∀ u : Fin n, u ∈ g v → u ∉ I) ∧
    (∀ u : Fin n, u ∈ g v → u ≠ v → mbqcRankPrec r v u) ∧
    (∀ u : Fin n, mbqcRankPrec r u v → u ∉ mbqcOdd G (g v)) ∧
    (mbqcGFlowPlaneCondB (lam v) (decide (v ∈ g v)) (decide (v ∈ mbqcOdd G (g v)))
      = true)

instance mbqcGFlowCheckDec {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) (g : Fin n → Finset (Fin n)) (r : Fin n → Fin n) :
    Decidable (mbqcGFlowCheck G I O lam g r) := by
  unfold mbqcGFlowCheck
  infer_instance

noncomputable def mbqcGFlowDecide {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) :
    Option ((Fin n → Finset (Fin n)) × (Fin n → Fin n)) :=
  (Fintype.elems (α := (Fin n → Finset (Fin n)) × (Fin n → Fin n))).toList.find?
    (fun p => decide (mbqcGFlowCheck G I O lam p.1 p.2))

noncomputable def mbqcRegWireGate {n : ℕ} (v : Fin n) (U : Operator 2) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => U (boolEquivFin2 (x v)) (boolEquivFin2 (y v)) *
    ∏ i ∈ Finset.univ.erase v, (if x i = y i then (1 : ℂ) else 0)

theorem mbqcRegWireGate_eq {n : ℕ} (v : Fin n) (U : Operator 2) :
    mbqcRegWireGate v U = pauliProductDensity (fun i => if i = v then U else 1) := by
  ext x y
  simp only [mbqcRegWireGate, pauliProductDensity, Matrix.of_apply]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun i => (if i = v then U else (1 : Operator 2)) (boolEquivFin2 (x i)) (boolEquivFin2 (y i)))
    (Finset.mem_univ v)]
  have hv : (if (v : Fin n) = v then U else (1 : Operator 2)) = U := by rw [if_pos rfl]
  rw [hv]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [if_neg (Finset.mem_erase.mp hi).1]
  simp only [Matrix.one_apply]
  by_cases h : x i = y i <;> simp [h]

noncomputable def mbqcResourceState {n : ℕ} (G : MbqcGraph n) : QState (Reg n) :=
  czResource G.edges

noncomputable def mbqcEntangler {n : ℕ} (G : MbqcGraph n) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (czMatrix G.edges)

noncomputable def mbqcInputFrame {n : ℕ} (I : Finset (Fin n)) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ I.card)) ℂ :=
  Matrix.of fun x y => ∏ v : Fin n,
    if h : v ∈ I then
      if (bitVecEquiv n).symm x v
          = (bitVecEquiv I.card).symm y (I.equivFin ⟨v, h⟩) then (1 : ℂ) else 0
    else (Real.sqrt 2 : ℂ)⁻¹

noncomputable def mbqcOutputFrame {n : ℕ} (O : Finset (Fin n)) (z : Fin n → Bool) :
    Matrix (Fin (2 ^ O.card)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun y x => ∏ v : Fin n,
    if h : v ∈ O then
      if (bitVecEquiv n).symm x v
          = (bitVecEquiv O.card).symm y (O.equivFin ⟨v, h⟩) then (1 : ℂ) else 0
    else if (bitVecEquiv n).symm x v = z v then (1 : ℂ) else 0

def MbqcPauliWire (W : Operator 2) : Prop :=
  W = 1 ∨ W = pauliX ∨ W = pauliZ ∨ W = pauliX * pauliZ

def MbqcCausalCorrection {n : ℕ} (prec : Fin n → Fin n → Prop)
    (corr : (Fin n → Bool) → Fin n → Operator 2) : Prop :=
  ∀ s s' : Fin n → Bool, ∀ v : Fin n, (∀ u : Fin n, prec u v → s u = s' u) →
    corr s v = corr s' v

noncomputable def mbqcWireGate {n : ℕ} (v : Fin n) (U : Operator 2) :
    Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (mbqcRegWireGate v U)

noncomputable def mbqcInterleavedGate {n : ℕ} (O : Finset (Fin n)) (r : Fin n → Fin n)
    (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool) :
    Operator (2 ^ n) :=
  (mbqcExecOrder O r).foldl
    (fun acc v => mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v))
      * mbqcWireGate v (corr s v) * acc)
    (relabelGate (bitVecEquiv n) (pauliProductDensity fun v => if v ∈ O then corr s v else 1))

noncomputable def mbqcPatternKraus {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s z : Fin n → Bool) :
    Matrix (Fin (2 ^ O.card)) (Fin (2 ^ I.card)) ℂ :=
  mbqcOutputFrame O z * mbqcInterleavedGate O r lam a corr s * mbqcEntangler G
    * mbqcInputFrame I

noncomputable def mbqcPatternBranchMap {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool) :
    Operator (2 ^ I.card) →ₗ[ℂ] Operator (2 ^ O.card) :=
  ∑ z : Fin n → Bool, conjBranch (mbqcPatternKraus G I O r lam a corr s z)

noncomputable def mbqcPatternBranch {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool)
    (ρ : Operator (2 ^ I.card)) : Operator (2 ^ O.card) :=
  mbqcPatternBranchMap G I O r lam a corr s ρ

noncomputable def mbqcPatternInstrument {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2)
    (hTP : ∀ A : Operator (2 ^ I.card),
      Matrix.trace (∑ s : Fin n → Bool, mbqcPatternBranch G I O r lam a corr s A)
        = Matrix.trace A) :
    Instrument (Fin n → Bool) (2 ^ I.card) (2 ^ O.card) :=
  Instrument.ofBranches (mbqcPatternBranchMap G I O r lam a corr)
    (fun s => CompletelyPositive.sum fun z _ =>
      completelyPositive_conjBranch (mbqcPatternKraus G I O r lam a corr s z)) hTP

theorem mbqcPatternInstrument_branch {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2)
    (hTP : ∀ A : Operator (2 ^ I.card),
      Matrix.trace (∑ s : Fin n → Bool, mbqcPatternBranch G I O r lam a corr s A)
        = Matrix.trace A) (s : Fin n → Bool) (ρ : Operator (2 ^ I.card)) :
    (mbqcPatternInstrument G I O r lam a corr hTP).branch s ρ
      = mbqcPatternBranch G I O r lam a corr s ρ := rfl

def MbqcStronglyDeterministic {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) (a : Fin n → ℝ) : Prop :=
  ∃ r : Fin n → Fin n,
    ∃ corr : (Fin n → Bool) → Fin n → Operator 2,
      (∀ s : Fin n → Bool, ∀ v : Fin n, MbqcPauliWire (corr s v)) ∧
      MbqcCausalCorrection (mbqcExecPrec r) corr ∧
      ∀ ρ : Operator (2 ^ I.card), IsDensityOperator ρ →
        ∀ s s' : Fin n → Bool,
          mbqcPatternBranch G I O r lam a corr s ρ
            = mbqcPatternBranch G I O r lam a corr s' ρ

def mbqcCounterexampleGraph : MbqcGraph 2 where edges := {(0, 1)}

theorem mbqcCounterexampleGraph_canonical : mbqcCanonical mbqcCounterexampleGraph := by
  intro e he
  simp only [mbqcCounterexampleGraph, Finset.mem_singleton] at he
  simp only [he]
  decide +kernel

noncomputable def mbqcPreentangledBranchMap {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hist : Fin gs.length → Bool × Bool) : Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n) :=
  if networkBranchValid gs hist then
    (((2 : ℂ)⁻¹) ^ ((networkCounts gs).1 + 2 * (networkCounts gs).2)) •
      conjBranch (networkLogicalMatrix gs) else 0

theorem mbqcPreentangledBranchMap_eq {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hg : networkLegal gs) (hist : Fin gs.length → Bool × Bool) :
    mbqcPreentangledBranchMap gs hist = (networkHistoryInstrument gs hg).branch hist := by
  apply LinearMap.ext
  intro ρ
  rw [mbqcPreentangledBranchMap]
  by_cases hv : networkBranchValid gs hist
  · rw [if_pos hv, LinearMap.smul_apply,
      cluster_network_history_actual_branch_formula n gs hg hist ρ, if_pos hv]
  · rw [if_neg hv, LinearMap.zero_apply,
      cluster_network_history_actual_branch_formula n gs hg hist ρ, if_neg hv]

noncomputable def mbqcPreentangledInstrument {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hg : networkLegal gs) : Instrument (Fin gs.length → Bool × Bool) (2 ^ n) (2 ^ n) :=
  Instrument.ofBranches (mbqcPreentangledBranchMap gs)
    (fun hist => by
      by_cases hv : networkBranchValid gs hist
      · rw [mbqcPreentangledBranchMap, if_pos hv, networkHalf_pow_cast]
        exact networkCP_const_smul (completelyPositive_conjBranch _) (by positivity)
      · rw [mbqcPreentangledBranchMap, if_neg hv]
        exact networkCP_zero)
    (fun A => by
      have h : ∑ hist : Fin gs.length → Bool × Bool, mbqcPreentangledBranchMap gs hist A
          = ∑ hist : Fin gs.length → Bool × Bool, (networkHistoryInstrument gs hg).branch hist A :=
        Finset.sum_congr rfl fun hist _ =>
          congrArg (fun T : Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n) => T A)
            (mbqcPreentangledBranchMap_eq gs hg hist)
      rw [h]
      exact (networkHistoryInstrument gs hg).total A)

theorem mbqcPreentangledInstrument_branch {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hg : networkLegal gs) (hist : Fin gs.length → Bool × Bool)
    (ρ : Operator (2 ^ n)) :
    (mbqcPreentangledInstrument gs hg).branch hist ρ
      = (networkHistoryInstrument gs hg).branch hist ρ :=
  congrArg (fun T : Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n) => T ρ)
    (mbqcPreentangledBranchMap_eq gs hg hist)

noncomputable def mbqcCzEdges {n : ℕ} (gs : List (ClusterNetworkGate n)) :
    List (Operator (2 ^ n)) :=
  gs.filterMap fun g =>
    match g with | .inr (i, j) => some (networkCzGate i j) | .inl _ => none

noncomputable def mbqcPreentangleUnitary {n : ℕ} (gs : List (ClusterNetworkGate n)) :
    Operator (2 ^ n) := (mbqcCzEdges gs).prod

def mbqcPreentangleCount {n : ℕ} (gs : List (ClusterNetworkGate n)) : ℕ :=
  (networkCounts gs).2

def mbqcMeasureCount {n : ℕ} (gs : List (ClusterNetworkGate n)) : ℕ := gs.length

def mbqcFeedbackBits {n : ℕ} (gs : List (ClusterNetworkGate n)) : ℕ :=
  (networkCounts gs).1

def mbqcCommBits {n : ℕ} (gs : List (ClusterNetworkGate n)) : ℕ :=
  (networkCounts gs).1

def mbqcBellWord : List (ClusterNetworkGate 2) :=
  [.inl (0, 1), .inr (0, 1), .inl (1, 1)]

theorem mbqcBellWord_legal : networkLegal mbqcBellWord := by
  intro g hg
  simp only [mbqcBellWord, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

noncomputable def rbWireEdges : Finset (Fin 2 × Fin 2) := {(0, 1)}

noncomputable def rbWirePulse : Matrix (Reg 2) (Reg 2) ℂ := sourcePulse rbWireEdges

noncomputable def rbWireCorrector (b : Bool) : Operator 2 :=
  (if b then pauliX else 1) * pauliZ

noncomputable def rbWireFrame : Matrix (Reg 2) (Fin 2) ℂ :=
  Matrix.of fun x j =>
    if x 0 = boolEquivFin2.symm j then (Real.sqrt 2 : ℂ)⁻¹ else 0

noncomputable def rbWireOutFrame (z : Bool) : Matrix (Fin 2) (Reg 2) ℂ :=
  Matrix.of fun j x => if x 0 = z ∧ x 1 = boolEquivFin2.symm j then (1 : ℂ) else 0

noncomputable def rbWireMeasureGate (a : ℝ) (b : Bool) : Matrix (Reg 2) (Reg 2) ℂ :=
  mbqcRegWireGate 0 (MbqcPlaneBasis MbqcPlane.XY a b)

noncomputable def rbWireCorrectorGate (b : Bool) : Matrix (Reg 2) (Reg 2) ℂ :=
  mbqcRegWireGate 1 (rbWireCorrector b)

noncomputable def rbWireKraus (a : ℝ) (b z : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  rbWireOutFrame z * rbWireCorrectorGate b * rbWireMeasureGate a b * rbWirePulse * rbWireFrame

noncomputable def rbWireBranchMap (a : ℝ) (b : Bool) :
    Operator 2 →ₗ[ℂ] Operator 2 :=
  ∑ z : Bool, conjBranch (rbWireKraus a b z)

noncomputable def rbWireBranch (a : ℝ) (b : Bool) (ρ : Operator 2) : Operator 2 :=
  rbWireBranchMap a b ρ

noncomputable def rbWireUnitary (a : ℝ) : Operator 2 :=
  (Real.sqrt 2 : ℂ)⁻¹ • Matrix.of fun i j : Fin 2 =>
    if j = 0 then (1 : ℂ) else if i = 0 then Complex.exp (-(a : ℂ) * Complex.I)
      else -Complex.exp (-(a : ℂ) * Complex.I)

noncomputable def rbWireInstrument (a : ℝ)
    (hTP : ∀ A : Operator 2,
      Matrix.trace (∑ b : Bool, rbWireBranch a b A) = Matrix.trace A) :
    Instrument Bool 2 2 :=
  Instrument.ofBranches (fun b => rbWireBranchMap a b)
    (fun b => CompletelyPositive.sum fun z _ =>
      completelyPositive_conjBranch (rbWireKraus a b z)) hTP

noncomputable def rbCnotEdges : Finset (Fin 4 × Fin 4) := {(0, 2), (1, 3), (2, 3)}

noncomputable def rbCnotPulse : Matrix (Reg 4) (Reg 4) ℂ := sourcePulse rbCnotEdges

noncomputable def rbCnotFrame : Matrix (Reg 4) (Fin 4) ℂ :=
  Matrix.of fun x j =>
    let d := (bitVecEquiv 2).symm j
    ∏ v : Fin 4,
      if v = 0 then (if x 0 = d 0 then (1 : ℂ) else 0)
      else if v = 1 then (if x 1 = d 1 then (1 : ℂ) else 0)
      else (Real.sqrt 2 : ℂ)⁻¹

noncomputable def rbCnotOutFrame (z : Bool × Bool) : Matrix (Fin 4) (Reg 4) ℂ :=
  Matrix.of fun j x =>
    let c := (bitVecEquiv 2).symm j
    (if x 2 = c 0 then (1 : ℂ) else 0) *
      (if x 3 = c 1 then (1 : ℂ) else 0) *
      (if x 0 = z.1 then (1 : ℂ) else 0) * (if x 1 = z.2 then (1 : ℂ) else 0)

noncomputable def rbWireH (v : Fin 4) : Matrix (Reg 4) (Reg 4) ℂ :=
  mbqcRegWireGate v (relabelGate boolEquivFin2 Hadamard)

noncomputable def rbProjGate (v : Fin 4) (b : Bool) : Matrix (Reg 4) (Reg 4) ℂ :=
  mbqcRegWireGate v (relabelGate boolEquivFin2 (Projector ({b} : Finset Bool)))

noncomputable def rbCnotKraus (s z : Bool × Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  rbCnotOutFrame z * rbWireH 3 * rbProjGate 0 s.1 * rbProjGate 1 s.2
    * rbWireH 0 * rbWireH 1 * rbCnotPulse * rbWireH 0 * rbWireH 1 * rbWireH 1 * rbCnotFrame

noncomputable def rbCnotBranchMap (s : Bool × Bool) : Operator 4 →ₗ[ℂ] Operator 4 :=
  ∑ z : Bool × Bool, conjBranch (rbCnotKraus s z)

noncomputable def rbCnotBranch (s : Bool × Bool) (ρ : Operator 4) : Operator 4 :=
  rbCnotBranchMap s ρ

noncomputable def rbCnotOp : Operator 4 := relabelGate teleportOutcomeEquiv CNOT

noncomputable def rbCnotInstrument
    (hTP : ∀ A : Operator 4,
      Matrix.trace (∑ s : Bool × Bool, rbCnotBranch s A) = Matrix.trace A) :
    Instrument (Bool × Bool) 4 4 :=
  Instrument.ofBranches rbCnotBranchMap
    (fun s => CompletelyPositive.sum fun z _ =>
      completelyPositive_conjBranch (rbCnotKraus s z)) hTP

noncomputable def rbFig2bEdges : Finset (Fin 3 × Fin 3) := {(0, 1), (0, 2)}

noncomputable def rbFig2bPulse : Matrix (Reg 3) (Reg 3) ℂ := sourcePulse rbFig2bEdges

noncomputable def rbFig2bFrame : Matrix (Reg 3) (Fin 2) ℂ :=
  Matrix.of fun x j =>
    if x 0 = boolEquivFin2.symm j then (Real.sqrt 2 : ℂ)⁻¹ else 0

noncomputable def rbFig2bOutFrame (z : Bool) : Matrix (Fin 4) (Reg 3) ℂ :=
  Matrix.of fun j x =>
    let c := (bitVecEquiv 2).symm j
    (if x 0 = z then (1 : ℂ) else 0) *
      (if x 1 = c 0 then (1 : ℂ) else 0) * (if x 2 = c 1 then (1 : ℂ) else 0)

noncomputable def rbFig2bMeasureGate (b : Bool) : Matrix (Reg 3) (Reg 3) ℂ :=
  mbqcRegWireGate 0 (MbqcPlaneBasis MbqcPlane.XY 0 b)

noncomputable def rbFig2bFlip : Operator 4 :=
  relabelGate teleportOutcomeEquiv
    (TensorGate (PauliZ * PauliZ) (PauliX * (1 : Matrix Bool Bool ℂ)))

noncomputable def rbFig2bCorrection (s : Bool) : Operator 4 :=
  if s then rbFig2bFlip else 1

noncomputable def rbFig2bKraus (s z : Bool) : Matrix (Fin 4) (Fin 2) ℂ :=
  rbFig2bCorrection s * rbFig2bOutFrame z * rbFig2bMeasureGate s * rbFig2bPulse
    * rbFig2bFrame

noncomputable def rbFig2bBranchMap (s : Bool) : Operator 2 →ₗ[ℂ] Operator 4 :=
  ∑ z : Bool, conjBranch (rbFig2bKraus s z)

noncomputable def rbFig2bBranch (s : Bool) (ρ : Operator 2) : Operator 4 :=
  rbFig2bBranchMap s ρ

noncomputable def rbFig2bTransferOp : Matrix (Fin 4) (Fin 2) ℂ :=
  Matrix.of fun j i =>
    let c := (bitVecEquiv 2).symm j
    ((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ •
      (if i = 0 then (if c 0 = c 1 then (1 : ℂ) else -1) else (1 : ℂ))

noncomputable def rbFig2bTransfer
    (hTP : ∀ A : Operator 2,
      Matrix.trace (∑ s : Bool, rbFig2bBranch s A) = Matrix.trace A) :
    Instrument Bool 2 4 :=
  Instrument.ofBranches rbFig2bBranchMap
    (fun s => CompletelyPositive.sum fun z _ =>
      completelyPositive_conjBranch (rbFig2bKraus s z)) hTP

def rbFiniteGateDecomp : List FiniteGateCode :=
  [.h 1, .cx 0 1, .h 1, .t 1, .t 1, .t 1, .t 1]

theorem rbFiniteGateDecomp_length : rbFiniteGateDecomp.length = 7 := rfl

theorem rbFiniteGateDecomp_legal : finiteWordLegal 2 rbFiniteGateDecomp = true := by
  simp [rbFiniteGateDecomp, finiteWordLegal, finiteCodeLegal]

def rbWireCommBits : ℕ := 1

def rbCnotCommBits : ℕ := 2

def rbFig2bCommBits : ℕ := 1

end Qatlib.Concepts.MbqcFlow.FlowDecision
