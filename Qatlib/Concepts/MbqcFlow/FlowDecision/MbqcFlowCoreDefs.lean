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

/-!
# Graphs, flow predicates, and MBQC branch semantics

This module defines finite open graphs, measurement planes, causal flow and generalized-flow
predicates, and finite searches over maps and rank assignments. `MbqcHasFlow` expresses the
causal flow conditions used in one-way computation [DanosKashefi2006], while `MbqcHasGFlow`
records the correction-set and plane conditions used by this development.

`mbqcPatternKraus` and `mbqcPatternBranchMap` give matrix semantics for graph patterns with
interleaved corrections and measurements. Instrument constructors take explicit
trace-preservation proofs, and concrete wire, CNOT, and Figure 2(b) patterns provide examples
from the cluster-state setting [RaussendorfBriegel2001].

## Main declarations

* `mbqcFlowDecide` and `mbqcGFlowDecide`: finite searches for rank-based witnesses.
* `MbqcStronglyDeterministic`: existence of causal Pauli corrections giving equal branches on
  density inputs.
* `mbqcPatternInstrument`: an instrument built from graph-pattern branches.
* `mbqcPreentangledBranchMap_eq`: agreement with the sequential network history branch.
* `rbWireKraus`, `rbCnotKraus`, and `rbFig2bKraus`: concrete pattern matrices.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
* [Browne et al., 2007][BrowneEtAl2007]
* [Raussendorf and Briegel, 2001][RaussendorfBriegel2001]
-/

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

/-- A finite graph presentation given by a set of ordered pairs of vertices in `Fin n`. -/
structure MbqcGraph (n : ℕ) where

  edges : Finset (Fin n × Fin n)

/-- A graph presentation is canonical when every stored edge has its first endpoint strictly
smaller than its second endpoint. -/
def mbqcCanonical {n : ℕ} (G : MbqcGraph n) : Prop := ∀ e ∈ G.edges, (e.1 : ℕ) < (e.2 : ℕ)

/-- The Boolean adjacency test treating either stored orientation of an edge as adjacency. -/
def mbqcAdj {n : ℕ} (G : MbqcGraph n) (i j : Fin n) : Bool :=
  decide ((i, j) ∈ G.edges ∨ (j, i) ∈ G.edges)

/-- The set of vertices having an odd number of neighbors in `S`. -/
def mbqcOdd {n : ℕ} (G : MbqcGraph n) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => (S.filter fun u => mbqcAdj G v u).card % 2 = 1

/-- A finite graph equipped with designated input and output vertex sets. -/
structure MbqcOpenGraph (n : ℕ) where

  toGraph : MbqcGraph n

  mbqcInputs : Finset (Fin n)

  mbqcOutputs : Finset (Fin n)

/-- The three Pauli measurement planes `XY`, `XZ`, and `YZ`. -/
inductive MbqcPlane where
  | XY | XZ | YZ
  deriving DecidableEq

/-- The first Pauli axis for each measurement plane: `X` for `XY`, `Z` for `XZ`, and `Y` for
`YZ`. -/
def mbqcPlaneAxisA : MbqcPlane → Operator 2
  | .XY => pauliX
  | .XZ => pauliZ
  | .YZ => pauliY

/-- The second Pauli axis for each measurement plane: `Y` for `XY`, `X` for `XZ`, and `Z` for
`YZ`. -/
def mbqcPlaneAxisB : MbqcPlane → Operator 2
  | .XY => pauliY
  | .XZ => pauliX
  | .YZ => pauliZ

/-- The outcome operator `(I + (-1)^b (cos(a) A + sin(a) B)) / 2` for the two Pauli axes
assigned to the measurement plane. -/
noncomputable def MbqcPlaneBasis (lam : MbqcPlane) (a : ℝ) (b : Bool) : Operator 2 :=
  (2 : ℂ)⁻¹ • ((1 : Operator 2) +
    (if b then (-1 : ℂ) else 1) •
      ((Complex.ofReal (Real.cos a)) • mbqcPlaneAxisA lam
        + (Complex.ofReal (Real.sin a)) • mbqcPlaneAxisB lam))

/-- The two outcome operators for any measurement plane and angle sum to the identity. -/
theorem mbqcPlaneBasis_add (lam : MbqcPlane) (a : ℝ) :
    MbqcPlaneBasis lam a false + MbqcPlaneBasis lam a true = 1 := by
  unfold MbqcPlaneBasis
  rw [if_neg (by simp : ¬(false = true)), if_pos rfl]
  module

/-- The strict vertex relation induced by strict comparison of the assigned finite ranks. -/
def mbqcRankPrec {n : ℕ} (r : Fin n → Fin n) : Fin n → Fin n → Prop :=
  fun u v => (r u : ℕ) < (r v)

instance mbqcRankPrecDec {n : ℕ} (r : Fin n → Fin n) (u v : Fin n) :
    Decidable (mbqcRankPrec r u v) := Nat.decLt _ _

/-- The strict lexicographic execution relation comparing ranks first and vertex indices to
break ties. -/
def mbqcExecPrec {n : ℕ} (r : Fin n → Fin n) (u v : Fin n) : Prop :=
  (r u : ℕ) < (r v : ℕ) ∨ ((r u : ℕ) = (r v : ℕ) ∧ (u : ℕ) < (v : ℕ))

instance mbqcExecPrecDec {n : ℕ} (r : Fin n → Fin n) (u v : Fin n) :
    Decidable (mbqcExecPrec r u v) := by
  unfold mbqcExecPrec
  infer_instance

/-- The non-strict lexicographic execution relation comparing ranks first and vertex indices to
break ties. -/
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

/-- The list of non-output vertices sorted by rank and then by vertex index. -/
noncomputable def mbqcExecOrder {n : ℕ} (O : Finset (Fin n)) (r : Fin n → Fin n) :
    List (Fin n) :=
  (Finset.univ \ O).sort (mbqcExecLe r)

/-- The proposition that an open graph has a flow map and a decidable strict order satisfying
adjacency, input exclusion, and the F2 and F3 causal conditions at every non-output vertex
[DanosKashefi2006]. -/
def MbqcHasFlow {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) : Prop :=
  ∃ (f : Fin n → Option (Fin n)) (prec : Fin n → Fin n → Prop),
    ∃ _dp : DecidableRel prec,
      IsStrictOrder (Fin n) prec ∧
      ∀ v : Fin n, v ∉ O → ∃ w : Fin n, f v = some w ∧ mbqcAdj G v w ∧ w ∉ I ∧
        prec v w ∧ ∀ k : Fin n, mbqcAdj G w k → k ≠ v → prec v k

/-- The plane-dependent condition on correction-set and odd-neighborhood membership: `¬mem ∧
odd` for `XY`, `mem ∧ odd` for `XZ`, and `mem ∧ ¬odd` for `YZ`. -/
def mbqcGFlowPlaneCond (p : MbqcPlane) (mem odd : Prop) : Prop :=
  match p with
  | .XY => ¬mem ∧ odd
  | .XZ => mem ∧ odd
  | .YZ => mem ∧ ¬odd

/-- The Boolean form of the plane-dependent correction-set and odd-neighborhood membership
condition. -/
def mbqcGFlowPlaneCondB (p : MbqcPlane) (mem odd : Bool) : Bool :=
  match p with
  | .XY => !mem && odd
  | .XZ => mem && odd
  | .YZ => mem && !odd

/-- The Boolean plane test evaluates to true exactly when the corresponding propositional plane
condition holds. -/
theorem mbqcGFlowPlaneCondB_iff (p : MbqcPlane) (mem odd : Bool) :
    mbqcGFlowPlaneCondB p mem odd = true ↔
      mbqcGFlowPlaneCond p (mem = true) (odd = true) := by
  cases p <;> simp [mbqcGFlowPlaneCondB, mbqcGFlowPlaneCond]

/-- The proposition that correction sets and a decidable strict order satisfy input exclusion,
forward non-self correction membership, exclusion of predecessors from odd neighborhoods,
and the assigned plane conditions. -/
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

/-- The finite-rank flow conditions requiring each non-output vertex to have an adjacent image
outside the inputs, with that image and its other neighbors strictly later in rank. -/
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

/-- Searches all finite flow-map and rank-assignment pairs and returns the first pair satisfying
`mbqcFlowCheck`, or `none` if no pair passes. -/
noncomputable def mbqcFlowDecide {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) :
    Option ((Fin n → Option (Fin n)) × (Fin n → Fin n)) :=
  (Fintype.elems (α := (Fin n → Option (Fin n)) × (Fin n → Fin n))).toList.find?
    (fun p => decide (mbqcFlowCheck G I O p.1 p.2))

/-- The rank-based generalized-flow check enforcing input exclusion, forward non-self correction
membership, exclusion of smaller-rank vertices from odd neighborhoods, and the Boolean plane
conditions. -/
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

/-- Searches all finite correction-set maps and rank assignments and returns the first pair
satisfying `mbqcGFlowCheck`, or `none` if no pair passes. -/
noncomputable def mbqcGFlowDecide {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) :
    Option ((Fin n → Finset (Fin n)) × (Fin n → Fin n)) :=
  (Fintype.elems (α := (Fin n → Finset (Fin n)) × (Fin n → Fin n))).toList.find?
    (fun p => decide (mbqcGFlowCheck G I O lam p.1 p.2))

/-- The register-indexed embedding of `U` on wire `v`, with equality indicators enforcing the
identity on every other wire. -/
noncomputable def mbqcRegWireGate {n : ℕ} (v : Fin n) (U : Operator 2) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => U (boolEquivFin2 (x v)) (boolEquivFin2 (y v)) *
    ∏ i ∈ Finset.univ.erase v, (if x i = y i then (1 : ℂ) else 0)

/-- The register wire embedding equals the tensor product with factor `U` at `v` and identity
factors elsewhere. -/
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

/-- The graph resource state `czResource G.edges` associated with the stored edge set. -/
noncomputable def mbqcResourceState {n : ℕ} (G : MbqcGraph n) : QState (Reg n) :=
  czResource G.edges

/-- The finite-indexed controlled-Z entangler obtained by relabeling the graph's
register-indexed `czMatrix`. -/
noncomputable def mbqcEntangler {n : ℕ} (G : MbqcGraph n) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (czMatrix G.edges)

/-- The input embedding that preserves the input-set bits and assigns amplitude `1 / √2` at
every non-input vertex. -/
noncomputable def mbqcInputFrame {n : ℕ} (I : Finset (Fin n)) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ I.card)) ℂ :=
  Matrix.of fun x y => ∏ v : Fin n,
    if h : v ∈ I then
      if (bitVecEquiv n).symm x v
          = (bitVecEquiv I.card).symm y (I.equivFin ⟨v, h⟩) then (1 : ℂ) else 0
    else (Real.sqrt 2 : ℂ)⁻¹

/-- The output extraction matrix that preserves the output-set bits and fixes every other bit to
the supplied record `z`. -/
noncomputable def mbqcOutputFrame {n : ℕ} (O : Finset (Fin n)) (z : Fin n → Bool) :
    Matrix (Fin (2 ^ O.card)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun y x => ∏ v : Fin n,
    if h : v ∈ O then
      if (bitVecEquiv n).symm x v
          = (bitVecEquiv O.card).symm y (O.equivFin ⟨v, h⟩) then (1 : ℂ) else 0
    else if (bitVecEquiv n).symm x v = z v then (1 : ℂ) else 0

/-- The predicate that a one-qubit operator is one of `1`, `pauliX`, `pauliZ`, or `pauliX *
pauliZ`. -/
def MbqcPauliWire (W : Operator 2) : Prop :=
  W = 1 ∨ W = pauliX ∨ W = pauliZ ∨ W = pauliX * pauliZ

/-- A correction family is causal when its value at each vertex depends only on outcome bits at
preceding vertices. -/
def MbqcCausalCorrection {n : ℕ} (prec : Fin n → Fin n → Prop)
    (corr : (Fin n → Bool) → Fin n → Operator 2) : Prop :=
  ∀ s s' : Fin n → Bool, ∀ v : Fin n, (∀ u : Fin n, prec u v → s u = s' u) →
    corr s v = corr s' v

/-- The finite-indexed embedding of a one-qubit operator on the selected wire. -/
noncomputable def mbqcWireGate {n : ℕ} (v : Fin n) (U : Operator 2) :
    Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (mbqcRegWireGate v U)

/-- The ordered product of local corrections followed by measurement outcome operators on
non-output vertices, initialized with the output-wire corrections. -/
noncomputable def mbqcInterleavedGate {n : ℕ} (O : Finset (Fin n)) (r : Fin n → Fin n)
    (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool) :
    Operator (2 ^ n) :=
  (mbqcExecOrder O r).foldl
    (fun acc v => mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v))
      * mbqcWireGate v (corr s v) * acc)
    (relabelGate (bitVecEquiv n) (pauliProductDensity fun v => if v ∈ O then corr s v else 1))

/-- The pattern Kraus matrix formed by the input frame, graph entangler, interleaved correction
and measurement operators, and output frame. -/
noncomputable def mbqcPatternKraus {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s z : Fin n → Bool) :
    Matrix (Fin (2 ^ O.card)) (Fin (2 ^ I.card)) ℂ :=
  mbqcOutputFrame O z * mbqcInterleavedGate O r lam a corr s * mbqcEntangler G
    * mbqcInputFrame I

/-- The complex-linear pattern branch for record `s`, formed by summing conjugation by the
pattern Kraus matrices over the auxiliary output records `z`. -/
noncomputable def mbqcPatternBranchMap {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool) :
    Operator (2 ^ I.card) →ₗ[ℂ] Operator (2 ^ O.card) :=
  ∑ z : Fin n → Bool, conjBranch (mbqcPatternKraus G I O r lam a corr s z)

/-- The result of applying the pattern branch map for outcome record `s` to an input operator. -/
noncomputable def mbqcPatternBranch {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool)
    (ρ : Operator (2 ^ I.card)) : Operator (2 ^ O.card) :=
  mbqcPatternBranchMap G I O r lam a corr s ρ

/-- The instrument of pattern branches constructed from a supplied proof that their sum
preserves trace. -/
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

/-- A branch of the constructed pattern instrument is exactly the corresponding
`mbqcPatternBranch`. -/
theorem mbqcPatternInstrument_branch {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2)
    (hTP : ∀ A : Operator (2 ^ I.card),
      Matrix.trace (∑ s : Fin n → Bool, mbqcPatternBranch G I O r lam a corr s A)
        = Matrix.trace A) (s : Fin n → Bool) (ρ : Operator (2 ^ I.card)) :
    (mbqcPatternInstrument G I O r lam a corr hTP).branch s ρ
      = mbqcPatternBranch G I O r lam a corr s ρ := rfl

/-- The proposition that some ranks and causal local Pauli corrections make all outcome branches
equal on every density input. Causality uses the execution relation with vertex indices
breaking rank ties. -/
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

/-- The two-vertex graph presentation containing the single edge `(0, 1)`. -/
def mbqcCounterexampleGraph : MbqcGraph 2 where edges := {(0, 1)}

/-- The single-edge two-vertex graph presentation is canonical. -/
theorem mbqcCounterexampleGraph_canonical : mbqcCanonical mbqcCounterexampleGraph := by
  intro e he
  simp only [mbqcCounterexampleGraph, Finset.mem_singleton] at he
  simp only [he]
  decide +kernel

/-- The prescribed history branch map, equal to count-weighted logical conjugation for a valid
history and zero for an invalid history. -/
noncomputable def mbqcPreentangledBranchMap {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hist : Fin gs.length → Bool × Bool) : Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n) :=
  if networkBranchValid gs hist then
    (((2 : ℂ)⁻¹) ^ ((networkCounts gs).1 + 2 * (networkCounts gs).2)) •
      conjBranch (networkLogicalMatrix gs) else 0

/-- For a legal network word, the prescribed preentangled branch map equals the corresponding
branch of `networkHistoryInstrument`. -/
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

/-- The instrument with the prescribed count-weighted logical branch maps for a legal network
word. -/
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

/-- Each branch of the preentangled instrument equals the corresponding branch of the sequential
network history instrument. -/
theorem mbqcPreentangledInstrument_branch {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hg : networkLegal gs) (hist : Fin gs.length → Bool × Bool)
    (ρ : Operator (2 ^ n)) :
    (mbqcPreentangledInstrument gs hg).branch hist ρ
      = (networkHistoryInstrument gs hg).branch hist ρ :=
  congrArg (fun T : Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n) => T ρ)
    (mbqcPreentangledBranchMap_eq gs hg hist)

/-- The list of controlled-Z matrices extracted from a network word, retaining their order and
omitting wire gates. -/
noncomputable def mbqcCzEdges {n : ℕ} (gs : List (ClusterNetworkGate n)) :
    List (Operator (2 ^ n)) :=
  gs.filterMap fun g =>
    match g with | .inr (i, j) => some (networkCzGate i j) | .inl _ => none

/-- The product of the controlled-Z matrices extracted by `mbqcCzEdges`. -/
noncomputable def mbqcPreentangleUnitary {n : ℕ} (gs : List (ClusterNetworkGate n)) :
    Operator (2 ^ n) := (mbqcCzEdges gs).prod

/-- The number of controlled-Z gates in a network word. -/
def mbqcPreentangleCount {n : ℕ} (gs : List (ClusterNetworkGate n)) : ℕ :=
  (networkCounts gs).2

/-- The measurement count assigned to a network word, equal to its list length. -/
def mbqcMeasureCount {n : ℕ} (gs : List (ClusterNetworkGate n)) : ℕ := gs.length

/-- The feedback-bit count assigned to a network word, equal to its number of wire gates. -/
def mbqcFeedbackBits {n : ℕ} (gs : List (ClusterNetworkGate n)) : ℕ :=
  (networkCounts gs).1

/-- The communication-bit count assigned to a network word, equal to its number of wire gates. -/
def mbqcCommBits {n : ℕ} (gs : List (ClusterNetworkGate n)) : ℕ :=
  (networkCounts gs).1

/-- The two-wire network word applying `clusterJ 1` on wire zero, controlled-Z on wires zero and
one, and `clusterJ 1` on wire one. -/
def mbqcBellWord : List (ClusterNetworkGate 2) :=
  [.inl (0, 1), .inr (0, 1), .inl (1, 1)]

/-- The network word `mbqcBellWord` is legal. -/
theorem mbqcBellWord_legal : networkLegal mbqcBellWord := by
  intro g hg
  simp only [mbqcBellWord, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

/-- The single edge `(0, 1)` used by the two-qubit wire pattern. -/
noncomputable def rbWireEdges : Finset (Fin 2 × Fin 2) := {(0, 1)}

/-- The register-indexed source pulse associated with the wire-pattern edge set. -/
noncomputable def rbWirePulse : Matrix (Reg 2) (Reg 2) ℂ := sourcePulse rbWireEdges

/-- The wire-pattern correction `X^b Z`, with the `X` factor present exactly when `b` is true. -/
noncomputable def rbWireCorrector (b : Bool) : Operator 2 :=
  (if b then pauliX else 1) * pauliZ

/-- The two-qubit wire input frame, with amplitude `1 / √2` when register bit zero matches the
input basis bit and zero otherwise. -/
noncomputable def rbWireFrame : Matrix (Reg 2) (Fin 2) ℂ :=
  Matrix.of fun x j =>
    if x 0 = boolEquivFin2.symm j then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- The wire output frame fixing register bit zero to `z` and reading register bit one as the
output basis bit. -/
noncomputable def rbWireOutFrame (z : Bool) : Matrix (Fin 2) (Reg 2) ℂ :=
  Matrix.of fun j x => if x 0 = z ∧ x 1 = boolEquivFin2.symm j then (1 : ℂ) else 0

/-- The wire-pattern measurement outcome operator in the `XY` plane, embedded on register wire
zero. -/
noncomputable def rbWireMeasureGate (a : ℝ) (b : Bool) : Matrix (Reg 2) (Reg 2) ℂ :=
  mbqcRegWireGate 0 (MbqcPlaneBasis MbqcPlane.XY a b)

/-- The outcome-dependent wire-pattern correction embedded on register wire one. -/
noncomputable def rbWireCorrectorGate (b : Bool) : Matrix (Reg 2) (Reg 2) ℂ :=
  mbqcRegWireGate 1 (rbWireCorrector b)

/-- The wire-pattern Kraus matrix obtained by composing its input frame, source pulse,
measurement, correction, and output frame. -/
noncomputable def rbWireKraus (a : ℝ) (b z : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  rbWireOutFrame z * rbWireCorrectorGate b * rbWireMeasureGate a b * rbWirePulse * rbWireFrame

/-- The wire-pattern branch map for outcome `b`, summing Kraus conjugations over the
output-frame record `z`. -/
noncomputable def rbWireBranchMap (a : ℝ) (b : Bool) :
    Operator 2 →ₗ[ℂ] Operator 2 :=
  ∑ z : Bool, conjBranch (rbWireKraus a b z)

/-- The wire-pattern branch map for `b` evaluated on the input operator. -/
noncomputable def rbWireBranch (a : ℝ) (b : Bool) (ρ : Operator 2) : Operator 2 :=
  rbWireBranchMap a b ρ

/-- The explicit matrix `H diag(1, exp(-i a))` associated with the wire pattern. -/
noncomputable def rbWireUnitary (a : ℝ) : Operator 2 :=
  (Real.sqrt 2 : ℂ)⁻¹ • Matrix.of fun i j : Fin 2 =>
    if j = 0 then (1 : ℂ) else if i = 0 then Complex.exp (-(a : ℂ) * Complex.I)
      else -Complex.exp (-(a : ℂ) * Complex.I)

/-- The Boolean-outcome wire-pattern instrument constructed from a supplied proof of total trace
preservation. -/
noncomputable def rbWireInstrument (a : ℝ)
    (hTP : ∀ A : Operator 2,
      Matrix.trace (∑ b : Bool, rbWireBranch a b A) = Matrix.trace A) :
    Instrument Bool 2 2 :=
  Instrument.ofBranches (fun b => rbWireBranchMap a b)
    (fun b => CompletelyPositive.sum fun z _ =>
      completelyPositive_conjBranch (rbWireKraus a b z)) hTP

/-- The three edges `(0, 2)`, `(1, 3)`, and `(2, 3)` used by the four-qubit CNOT pattern. -/
noncomputable def rbCnotEdges : Finset (Fin 4 × Fin 4) := {(0, 2), (1, 3), (2, 3)}

/-- The register-indexed source pulse associated with the CNOT-pattern edge set. -/
noncomputable def rbCnotPulse : Matrix (Reg 4) (Reg 4) ℂ := sourcePulse rbCnotEdges

/-- The four-qubit CNOT input frame preserving the two input bits on wires zero and one and
assigning `1 / √2` amplitudes on the remaining wires. -/
noncomputable def rbCnotFrame : Matrix (Reg 4) (Fin 4) ℂ :=
  Matrix.of fun x j =>
    let d := (bitVecEquiv 2).symm j
    ∏ v : Fin 4,
      if v = 0 then (if x 0 = d 0 then (1 : ℂ) else 0)
      else if v = 1 then (if x 1 = d 1 then (1 : ℂ) else 0)
      else (Real.sqrt 2 : ℂ)⁻¹

/-- The CNOT output frame fixing wires zero and one to `z` and reading wires two and three as
the two-bit output. -/
noncomputable def rbCnotOutFrame (z : Bool × Bool) : Matrix (Fin 4) (Reg 4) ℂ :=
  Matrix.of fun j x =>
    let c := (bitVecEquiv 2).symm j
    (if x 2 = c 0 then (1 : ℂ) else 0) *
      (if x 3 = c 1 then (1 : ℂ) else 0) *
      (if x 0 = z.1 then (1 : ℂ) else 0) * (if x 1 = z.2 then (1 : ℂ) else 0)

/-- The Boolean-indexed Hadamard embedded on the selected wire of a four-qubit register. -/
noncomputable def rbWireH (v : Fin 4) : Matrix (Reg 4) (Reg 4) ℂ :=
  mbqcRegWireGate v (relabelGate boolEquivFin2 Hadamard)

/-- The computational-basis projector for outcome `b`, embedded on the selected wire of a
four-qubit register. -/
noncomputable def rbProjGate (v : Fin 4) (b : Bool) : Matrix (Reg 4) (Reg 4) ℂ :=
  mbqcRegWireGate v (relabelGate boolEquivFin2 (Projector ({b} : Finset Bool)))

/-- The CNOT-pattern Kraus matrix formed from its input frame, source pulse, local Hadamards,
two outcome projectors, and output frame. -/
noncomputable def rbCnotKraus (s z : Bool × Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  rbCnotOutFrame z * rbWireH 3 * rbProjGate 0 s.1 * rbProjGate 1 s.2
    * rbWireH 0 * rbWireH 1 * rbCnotPulse * rbWireH 0 * rbWireH 1 * rbWireH 1 * rbCnotFrame

/-- The CNOT-pattern branch map for record `s`, summing Kraus conjugations over the auxiliary
output-frame record `z`. -/
noncomputable def rbCnotBranchMap (s : Bool × Bool) : Operator 4 →ₗ[ℂ] Operator 4 :=
  ∑ z : Bool × Bool, conjBranch (rbCnotKraus s z)

/-- The CNOT-pattern branch map for record `s` evaluated on the input operator. -/
noncomputable def rbCnotBranch (s : Bool × Bool) (ρ : Operator 4) : Operator 4 :=
  rbCnotBranchMap s ρ

/-- The CNOT operator relabeled from Boolean pairs to `Fin 4` by `teleportOutcomeEquiv`. -/
noncomputable def rbCnotOp : Operator 4 := relabelGate teleportOutcomeEquiv CNOT

/-- The four-outcome CNOT-pattern instrument constructed from a supplied proof of total trace
preservation. -/
noncomputable def rbCnotInstrument
    (hTP : ∀ A : Operator 4,
      Matrix.trace (∑ s : Bool × Bool, rbCnotBranch s A) = Matrix.trace A) :
    Instrument (Bool × Bool) 4 4 :=
  Instrument.ofBranches rbCnotBranchMap
    (fun s => CompletelyPositive.sum fun z _ =>
      completelyPositive_conjBranch (rbCnotKraus s z)) hTP

/-- The three-vertex edge set `{(0, 1), (0, 2)}` used for the Figure 2(b) pattern. -/
noncomputable def rbFig2bEdges : Finset (Fin 3 × Fin 3) := {(0, 1), (0, 2)}

/-- The register-indexed source pulse for the Figure 2(b) edge set. -/
noncomputable def rbFig2bPulse : Matrix (Reg 3) (Reg 3) ℂ := sourcePulse rbFig2bEdges

/-- The Figure 2(b) input frame, with amplitude `1 / √2` when register bit zero matches the
input basis bit and zero otherwise. -/
noncomputable def rbFig2bFrame : Matrix (Reg 3) (Fin 2) ℂ :=
  Matrix.of fun x j =>
    if x 0 = boolEquivFin2.symm j then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- The Figure 2(b) output frame fixing bit zero to `z` and reading bits one and two as the
output pair. -/
noncomputable def rbFig2bOutFrame (z : Bool) : Matrix (Fin 4) (Reg 3) ℂ :=
  Matrix.of fun j x =>
    let c := (bitVecEquiv 2).symm j
    (if x 0 = z then (1 : ℂ) else 0) *
      (if x 1 = c 0 then (1 : ℂ) else 0) * (if x 2 = c 1 then (1 : ℂ) else 0)

/-- The zero-angle `XY` measurement outcome operator embedded on wire zero of the Figure 2(b)
register. -/
noncomputable def rbFig2bMeasureGate (b : Bool) : Matrix (Reg 3) (Reg 3) ℂ :=
  mbqcRegWireGate 0 (MbqcPlaneBasis MbqcPlane.XY 0 b)

/-- The two-output operator obtained by relabeling the tensor product `(PauliZ * PauliZ) ⊗
(PauliX * 1)`. -/
noncomputable def rbFig2bFlip : Operator 4 :=
  relabelGate teleportOutcomeEquiv
    (TensorGate (PauliZ * PauliZ) (PauliX * (1 : Matrix Bool Bool ℂ)))

/-- The Figure 2(b) output correction, equal to `rbFig2bFlip` for a true outcome and the
identity for a false outcome. -/
noncomputable def rbFig2bCorrection (s : Bool) : Operator 4 :=
  if s then rbFig2bFlip else 1

/-- The Figure 2(b) Kraus matrix obtained by composing its input frame, source pulse,
measurement, output frame, and outcome correction. -/
noncomputable def rbFig2bKraus (s z : Bool) : Matrix (Fin 4) (Fin 2) ℂ :=
  rbFig2bCorrection s * rbFig2bOutFrame z * rbFig2bMeasureGate s * rbFig2bPulse
    * rbFig2bFrame

/-- The Figure 2(b) branch map for outcome `s`, summing Kraus conjugations over the auxiliary
record `z`. -/
noncomputable def rbFig2bBranchMap (s : Bool) : Operator 2 →ₗ[ℂ] Operator 4 :=
  ∑ z : Bool, conjBranch (rbFig2bKraus s z)

/-- The Figure 2(b) branch map for outcome `s` evaluated on the input operator. -/
noncomputable def rbFig2bBranch (s : Bool) (ρ : Operator 2) : Operator 4 :=
  rbFig2bBranchMap s ρ

/-- The explicit Figure 2(b) transfer matrix with amplitude `1 / (2√2)`, negated precisely when
the input index is zero and the two output bits differ. -/
noncomputable def rbFig2bTransferOp : Matrix (Fin 4) (Fin 2) ℂ :=
  Matrix.of fun j i =>
    let c := (bitVecEquiv 2).symm j
    ((2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ •
      (if i = 0 then (if c 0 = c 1 then (1 : ℂ) else -1) else (1 : ℂ))

/-- The Boolean-outcome Figure 2(b) instrument from one input qubit to two output qubits,
constructed from a supplied trace-preservation proof. -/
noncomputable def rbFig2bTransfer
    (hTP : ∀ A : Operator 2,
      Matrix.trace (∑ s : Bool, rbFig2bBranch s A) = Matrix.trace A) :
    Instrument Bool 2 4 :=
  Instrument.ofBranches rbFig2bBranchMap
    (fun s => CompletelyPositive.sum fun z _ =>
      completelyPositive_conjBranch (rbFig2bKraus s z)) hTP

/-- The seven-code word `H₁, CX₀₁, H₁, T₁, T₁, T₁, T₁` in the finite gate vocabulary. -/
def rbFiniteGateDecomp : List FiniteGateCode :=
  [.h 1, .cx 0 1, .h 1, .t 1, .t 1, .t 1, .t 1]

/-- The finite gate word `rbFiniteGateDecomp` has length seven. -/
theorem rbFiniteGateDecomp_length : rbFiniteGateDecomp.length = 7 := rfl

/-- The finite gate word `rbFiniteGateDecomp` is legal on two wires. -/
theorem rbFiniteGateDecomp_legal : finiteWordLegal 2 rbFiniteGateDecomp = true := by
  simp [rbFiniteGateDecomp, finiteWordLegal, finiteCodeLegal]

/-- The communication-bit budget assigned to the wire pattern, equal to one. -/
def rbWireCommBits : ℕ := 1

/-- The communication-bit budget assigned to the CNOT pattern, equal to two. -/
def rbCnotCommBits : ℕ := 2

/-- The communication-bit budget assigned to the Figure 2(b) pattern, equal to one. -/
def rbFig2bCommBits : ℕ := 1

end Qatlib.Concepts.MbqcFlow.FlowDecision
